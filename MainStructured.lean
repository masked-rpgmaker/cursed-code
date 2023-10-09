import Cursed.IO

open Cursed Cursed.IO Child Toy IO

/-- Simulação da brincadeira das crianças (Estruturado). -/
def main : IO Unit := do
  let mut pairings : Std.Queue (Child × Toy) := Std.Queue.empty
  for t in toys do
    println s!"[{t}]"
    let mut q := Util.NonemptyList.toList queue
    let mut stop := false
    while not stop do
      if let c :: rest := q then
        if c.likes t then
          printlnTake c t
          pairings := pairings.enqueue (c, t)
          stop := true
        else
          printlnPass c t
          q := rest
      else
        stop := true
    println ""
  println "[Atribuição final de brinquedos]"
  for (c, t) in Std.Queue.toArray pairings do println s!"{c} → {t}"
