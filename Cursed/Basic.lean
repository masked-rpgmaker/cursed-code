import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Order.Basic

import Cursed.Util

namespace Cursed

open Util

/-- Tipo dos brinquedos. -/
inductive Toy
  | PlasticSpider
  | RubberFrog
  | Denture
  | GlowInTheDarkGhost
  | Witch

instance Toy.instToString : ToString Toy where
  toString
  | PlasticSpider => "Aranhas de plástico"
  | RubberFrog => "Sapos de borracha"
  | Denture => "Dentaduras"
  | GlowInTheDarkGhost => "Fantasminhas que brilham no escuro"
  | Witch => "Bruxinhas"

/-- Lista de brinquedos. -/
def Toy.toys : List Toy := [PlasticSpider, RubberFrog, Denture, GlowInTheDarkGhost, Witch]

/-- Tipo das crianças. -/
inductive Child
  | Samuel
  | Franklin
  | Hellen
  | JC
  | Daniel

namespace Child

instance : ToString Child where
  toString
  | Samuel   => "Samuel"
  | Franklin => "Franklin"
  | Hellen   => "Hellen"
  | JC       => "JC"
  | Daniel   => "Daniel"

open Toy

/-- Posição das crianças na fila. -/
def ord : Child -> Fin 5
  | Samuel   => 0
  | Franklin => 1
  | Hellen   => 2
  | JC       => 3
  | Daniel   => 4

/-- Lema: Cada posição na fila é ocupada por no máximo uma criança. -/
lemma ord_injective : Function.Injective ord := by
  intro c₁ c₂ h
  cases c₁ <;> cases c₂ <;> {
    try rfl
    try simp only [ord] at h
  }

/-- Versão de equivalência do lema anterior. -/
lemma ord_inj { c₁ c₂ : Child } : c₁.ord = c₂.ord ↔ c₁ = c₂ := ord_injective.eq_iff

/-- Axioma: existe uma equivalência entre crianças e brinquedos, i.e., cada
 criança termina a brincadeira com exatamente um brinquedo. -/
axiom toy : Child ≃ Toy

/-- Definição: uma criança recebe um brinquedo se nenhuma das crianças à sua frente na fila pega o
 brinquedo para si. -/
def receives (c : Child) (t : Toy) : Prop := ∀ c' : Child, c'.ord < c.ord → toy c' ≠ t

/-- Lema: Samuel recebe todos os brinquedos. -/
lemma samuel_receives_all_toys : ∀ t : Toy, Samuel.receives t := by
  -- O resultado segue por vacuidade (nenhuma criança está à frente de Samuel na fila).
  intro t c h
  conv at h => rhs; dsimp only [ord]
  absurd h
  exact Fin.not_lt_zero c.ord

/-- Axioma: Hellen gosta de Fantasminhas que brilham no escuro.​ -/
axiom hellen_takes_ghosts : toy Hellen = GlowInTheDarkGhost

/-- Axioma: Daniel nunca vai receber Bruxinhas.​ -/
axiom daniel_never_receives_witches : ¬Daniel.receives Witch

/-- Axioma: Franklin não gosta de Bruxinhas.​ -/
axiom franklin_dislikes_witches : toy Franklin ≠ Witch

/-- Axioma: As outras crianças nunca receberão Sapos de borracha.​ -/
axiom other_children_never_receive_frogs : ∀ c : Child, c ≠ Samuel → ¬c.receives RubberFrog

/-- Axioma: As Dentaduras sempre serão passadas para todas as crianças.​ -/
axiom all_children_receive_dentures : ∀ c : Child, c.receives Denture

/-- Lema: A única criança anterior a Franklin na fila é Samuel. -/
lemma lt_franklin_eq_samuel { c : Child } : c.ord < Franklin.ord ↔ c = Samuel := by
  -- A demonstração é puramente formal. Como Franklin está na posição 1, a única criança anterior
  -- deve estar na posição 0, que é a posição de Samuel.
  have samuel_ord_zero : Samuel.ord = 0 := rfl
  constructor <;> intro h
  . conv at h => rhs; simp only [ord]
    rw [Fin.lt_def, Fin.val_one, Nat.lt_one_iff, ←Fin.val_zero, Fin.val_inj] at h
    rw [←ord_inj, samuel_ord_zero]
    exact h
  . simp only [h, ord]

/-- Teorema: Samuel gosta de Sapos de borracha. -/
theorem samuel_takes_frogs : toy Samuel = RubberFrog := by
  -- Sabemos que as outras crianças nunca recebem os Sapos de borracha.
  -- Em particular, Franklin não nunca recebe os Sapos. Segue que alguma criança anterior a
  -- Franklin na fila gosta de Sapos.
  have h := other_children_never_receive_frogs Franklin
  simp only [ne_eq, receives, not_forall, not_not, exists_prop, forall_true_left] at h
  -- Mas a única criança anterior a Franklin na fila é Samuel. Logo, Samuel gosta de Sapos.
  let ⟨c, h₁, h₂⟩ := h
  rw [lt_franklin_eq_samuel] at h₁
  rw [h₁] at h₂
  exact h₂

/-- Lema: A única criança tão à frente na fila quanto Daniel é o próprio Daniel. -/
lemma daniel_leq_iff_eq_daniel { c : Child } : Daniel.ord ≤ c.ord ↔ c = Daniel := by
  constructor <;> intro h
  . have daniel_last : Daniel.ord = Fin.last 4 := by simp only
    simpa only [←ord_inj, daniel_last, ←Fin.last_le_iff]
  . rw [h]
    simp only

/-- Teorema: Daniel gosta de Dentaduras. -/
theorem daniel_takes_dentures : toy Daniel = Denture := by
  -- Sabemos que todas as crianças recebem as Dentaduras.
  have h := all_children_receive_dentures Daniel
  -- Sabemos também que alguma criança deve pegar a Dentadura. Seja c tal criança.
  let ⟨c, h₁⟩ := toy.surjective Denture
  -- Por casos:
  if h₂ : c.ord < Daniel.ord then
    -- Se a criança aparece antes de Daniel na fila, então Daniel não  recebe a Dentadura. Uma 
    -- contradição.
    apply (h c h₂ h₁).elim
  else
    -- Se a criança não aparece antes de Daniel na fila, então, como Daniel é o último da fila,
    -- a criança é exatamente Daniel.
    rw [Fin.not_lt, daniel_leq_iff_eq_daniel] at h₂
    rw [h₂] at h₁
    exact h₁
  -- Como o único caso possível é aquele onde c = Daniel, segue que Daniel gosta de Dentaduras.
  done

/-- Teorema: JC gosta de Bruxinhas. -/
theorem jc_takes_witches : toy JC = Witch := by
  -- Sabemos que alguma criança gosta de bruxinhas.
  -- Por eliminação:
  --  ⬝ Hellen gosta de Fantasmas
  --  ⬝ Samuel gosta de Sapos
  --  ⬝ Daniel gosta de Dentaduras
  --  ⬝ Franklin não gosta de Bruxinhas]
  -- Logo, a única criança que pode (e portanto deve) gostar de bruxinhas é JC.
  let ⟨c, h⟩ := toy.surjective Witch    
  cases c
  case JC => exact h
  repeat simp only [
    hellen_takes_ghosts,
    samuel_takes_frogs,
    daniel_takes_dentures,
    franklin_dislikes_witches
  ] at h

/-- Teorema: Franklin gosta de Bruxinhas. -/
theorem franklin_takes_spiders : toy Franklin = PlasticSpider := by
  -- Sabemos que alguma criança gosta de Aranhas.
  -- Por eliminação:
  --  ⬝ Hellen gosta de Fantasmas
  --  ⬝ Samuel gosta de Sapos
  --  ⬝ Daniel gosta de Dentaduras
  --  ⬝ JC gosta de Bruxinhas
  -- Logo, a única criança que pode (e portanto deve) gostar de bruxinhas é JC.
  let ⟨c, h⟩ := toy.surjective PlasticSpider
  cases c
  case Franklin => exact h
  repeat simp only [
    hellen_takes_ghosts,
    samuel_takes_frogs,
    daniel_takes_dentures,
    jc_takes_witches
  ] at h

/-- Definição dos gostos de cada criança. -/
def likes : Child -> Toy -> Bool
  | Samuel,   RubberFrog          => true
  | Franklin, PlasticSpider       => true
  | Hellen,   GlowInTheDarkGhost  => true
  | JC,       Witch               => true
  | Daniel,   Denture             => true
  | _, _                          => false

/-- Teorema: A definição de gostos acima corresponde exatamente aos brinquedos pegos por cada 
 criança. -/
theorem likes_iff {c : Child} {t : Toy} : c.likes t ↔ toy c = t := by
  -- A demonstração é por inspeção.
  cases c <;> cases t <;> simp only [
    samuel_takes_frogs,
    franklin_takes_spiders,
    hellen_takes_ghosts,
    jc_takes_witches,
    daniel_takes_dentures
  ]

/-- Fila das crianças. -/
def queue : NonemptyList Child := {Samuel, Franklin, Hellen, JC, Daniel}

end Child
