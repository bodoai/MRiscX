-- import MRiscX.AbstractSyntax.Instr
-- import MRiscX.Semantics.Run
import MRiscX.Basic

-- ι ist der Typ für das instruction set (also z.B. Instr)
class MonadTrace (m : Type → Type) (ι : outParam Type) extends Monad m where
  trace : ι → m Unit

-- Helper-Funktion, um die Instructions als Schlüssel
-- verwenden zu können: Key = Name des Konstruktors
def Instr.toCtorName (instr : Instr) : String :=
  let str := reprStr instr
  match str.splitOn " " with
  | [] => str
  | h :: _ => h

-- key : String, value : Nat
abbrev InstrStats := Std.HashMap String Nat

def InstrStats.logInstr (instr : Instr) (stats : InstrStats) :=
  let instrStr := instr.toCtorName
  match stats.get? instrStr with
  | none => stats.insert instrStr 1
  | some n => stats.insert instrStr (n + 1)

-- spezielle Implementierung von MonadTrace:
-- in eine State-Monade eingepackte HashMap
instance : MonadTrace (StateM InstrStats) Instr where
  trace instr := do set <| (← get).logInstr instr

def InstrStats.pretty (stats : InstrStats) :=
  let entries := stats.toList.mergeSort (· ≤ ·)
  let lines :=
    entries.map fun (k, v) => s!"{k} ↦ {v}"
  "{\n" ++ String.intercalate "\n" lines ++ "\n}"


def runOneStepMonadic {m : Type → Type} [MonadTrace m Instr] (ms : MState) : m MState := do
  if ms.terminated
  then return ms
  else
    let instr := ms.currInstruction
    MonadTrace.trace instr
    return ms.runOneStep

def runMonadic {m : Type → Type} [MonadTrace m Instr] : Nat → MState → m MState
  | 0, ms => pure ms
  | n' + 1, ms => do
    if ms.terminated
      then return ms -- stop as soon as possible -> more efficient
      else
        let instr := ms.currInstruction
        MonadTrace.trace instr
        let ms' := ms.runOneStep
        runMonadic n' ms'

def code :=
  mriscx
      first:
          la x 0, 0
          la x 1, 1
          la x 2, 2
          li x 3, 3
          j first
    end

def initialState : MState := { DefaultMState with code := code }

#eval IO.println ((runMonadic 10 initialState : StateM InstrStats MState).run ∅).2.pretty

def calcStats (n : Nat) (c : Code): InstrStats :=
  ((runMonadic n { DefaultMState with code := c} : StateM InstrStats MState).run ∅).2
def calcStatsString (n : Nat) (c : Code): String :=
  calcStats n c
  |> InstrStats.pretty

#eval IO.println <| calcStatsString 100000 code
