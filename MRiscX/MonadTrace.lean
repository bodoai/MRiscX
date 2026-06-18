import MRiscX.Basic

-- ι = type for the instruction set (e.g. ι := Instr)
class MonadTrace (m : Type → Type) (ι : outParam Type) extends Monad m where
  trace : ι → m Unit

-- MonadTrace adds side effects to the interpreter execution
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
