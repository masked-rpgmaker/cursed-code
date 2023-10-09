import Std.Classes.SetNotation

namespace Cursed.Util

/-- Definição indutiva de uma lista não vazia. -/
inductive NonemptyList (α : Type u)
  | single (val : α)
  | cons (head : α) (tail : NonemptyList α)

def NonemptyList.toList : NonemptyList α -> List α
  | single x => [x]
  | cons h t => h :: t.toList

instance : Singleton α (NonemptyList α) := ⟨NonemptyList.single⟩

instance : Insert α (NonemptyList α) := ⟨NonemptyList.cons⟩
