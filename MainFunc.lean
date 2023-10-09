import Cursed.Basic
import Cursed.IO

namespace Cursed

open Util NonemptyList Cursed Util Child Toy IO

/-- Ações tomadas pelas crianças para um brinquedo. -/
inductive Actions (t : Toy)
  | take (c : Child)
  | pass (c : Child) (rest : Actions t)

namespace Actions

open Function Cursed Child Toy IO

/-- Passa um brinquedo pela fila, devolvendo uma sequência de ações tomadas pelas crianças na fila.
 -/
def passAround : (cs : NonemptyList Child) -> (t : Toy) -> Actions t
  | single c, _ => take c
  | cons c rest, t => ite (c.likes t) (take c) (pass c $ passAround rest t)

/-- Catamorfismo monádico para ações. -/
def foldlM {t: Toy} {α : Type u} {m : Type u -> Type v} [Monad m]
  (take : Child -> m α) (pass : Child -> m PUnit) (as : Actions t) : m α :=
  match as with
  | .take c => take c
  | .pass c rest => do pass c; foldlM take pass rest

/-- Aplica uma sequência de ações, devolvendo a criança que fica com o brinquedo no final. -/
def run {t : Toy} : Actions t -> Child := Id.run ∘ foldlM pure (const _ $ pure ())

/-- Teorema: Aplicar as ações definidas pela passagem dos brinquedos na fila resulta no brinquedo 
 terminar com a criança que gosta dele. -/
theorem run_passAround_respects_likes :
  ∀ t : Toy, let child := run (passAround queue t); child.likes t := by
  -- A demonstração é por inspeção para cada brinquedo.
  intro t
  cases t <;> simp_all only

/-- Aplica uma sequência de ações, descrevendo cada uma na saída padrão. -/
def runIO {t : Toy} : Actions t -> IO Child :=
  foldlM (fun c => const _ c <$> printlnTake c t) (flip printlnPass t)

end Actions
end Cursed

open Cursed Child Toy IO

/-- Simulação da brincadeira das crianças (Funcional). -/ 
def main : IO Unit := do
  -- Atribui os brinquedos às crianças, aplicando as sequências de ações na fila para cada 
  -- brinquedo.
  let pairings ← toys.mapM $ fun t => do
    println s!"[{t}]"
    let child ← Actions.runIO $ Actions.passAround queue t
    println ""
    pure (child, t)
  -- Imprime a associação final entre crianças e brinquedos.
  println "[Atribuição final de brinquedos]"
  pairings.forM $ fun (c, t) => println s!"{c} → {t}"
