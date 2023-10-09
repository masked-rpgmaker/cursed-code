import Cursed.Util
import Cursed.IO

open Cursed Util Child Toy IO

universe u v

section OOP

/-- Tipo das mensagens passada para objetos. -/
def Message := Type u -> (Type u -> Type v) -> Type v

/-- Tipo da interface de um objeto. -/
def Interface (msg : Message) (m : Type u -> Type v) := ∀ {α}, msg α m -> m α

end OOP

section IChildQueue

/-- Tipo de mensagem para um objeto com interface de fila de crianças.  -/
inductive IChildQueueMessage (α : Type u) (m : Type u -> Type v)
  | passAround (t : Toy) (ret : Child -> m α)

/-- Interface de fila de crianças. -/
def IChildQueue := Interface IChildQueueMessage

/-- Método de passagem de brinquedo na fila. -/
def IChildQueue.passAround [Monad m] (q : IChildQueue m) (t : Toy) : m Child :=
  q (.passAround t pure)

/-- Classe de fila com uma única criança. -/
def SingletonChildQueue (c : Child) : IChildQueue IO :=
  fun
  | .passAround t ret => do
    -- Numa fila com uma única criança, a única criança na fila sempre pega o brinquedo.
    printlnTake c t
    ret c

/-- Classe de fila com uma duas ou mais crianças. -/
def ConsChildQueue (c : Child) (next : IChildQueue IO) : IChildQueue IO :=
  fun msg => match msg with
  | .passAround t ret => do
    -- A criança pega o brinquedo caso goste dele, e passa adiante caso contrário.
    if c.likes t then
      printlnTake c t
      ret c
    else
      printlnPass c t
      next msg

/-- Constrói uma fila de crianças a partir de uma lista não-vazia. -/
def IChildQueue.fromNonemptyList : NonemptyList Child -> IChildQueue IO
  | NonemptyList.single c => SingletonChildQueue c
  | NonemptyList.cons c rest => ConsChildQueue c $ IChildQueue.fromNonemptyList rest

end IChildQueue

section IPlaySimulator

/-- Tipo de mensagem para um objeto de simulador da brincadeira.  -/
inductive IPlaySimulatorMessage (α : Type u) (m : Type u -> Type v)
  | simulate (ret : Array (Child × Toy) -> m α)

/-- Interface para um objeto de simulador da brincadeira.  -/
def IPlaySimulator := Interface IPlaySimulatorMessage

/-- Método de execução de simulação. -/
def IPlaySimulator.simulate [Monad m] (q : IPlaySimulator m) : m (Array (Child × Toy)) :=
  q (.simulate pure)

/-- Instância singular do simulador.  -/
def IPlaySimulator.instance : IPlaySimulator IO :=
  fun
  | .simulate ret => do
    let mut pairings : Std.Queue (Child × Toy) := Std.Queue.empty
    let q : IChildQueue IO := IChildQueue.fromNonemptyList queue
    for t in toys do
      println s!"[{t}]"
      let c <- q.passAround t
      println ""
      pairings := pairings.enqueue (c, t)
    ret pairings.toArray

end IPlaySimulator

section IPlaySimulator

/-- Simulação da brincadeira das crianças (POO). -/ 
def main : IO Unit := do
  let simulator : IPlaySimulator IO := IPlaySimulator.instance
  let pairings <- simulator.simulate
  println "[Atribuição final de brinquedos]"
  for (c, t) in pairings do println s!"{c} → {t}"
