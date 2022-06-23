import data.real.basic
import tactic

open_locale big_operators
universes u

variable α : Type*

local notation `V` := list α
local notation `E` := list (α × α)

class digraph :=
  (nodes : V)
  (edges : E)
  (nonsymmetric : ∀ (u v : α ), (u, v) ∈ edges → (v, u) ∉ edges)

@[class] structure flow_network
  extends digraph α :=
  (source : α)
  (sink : α)
  (capacity : E -> ℝ)
  (postive_capacity : ∀ x : E, capacity x ≥ 0)

def mk_in [decidable_eq α] : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
| ⟨v, e, hnonsymm⟩ f  := λs,
  list.sum (list.map (λ u',
                     list.sum (list.map (λ u,
                                        f (u, u')) (list.diff v s))
                                        ) s)

-- [f (u, u') | u in (v\s) u' in s]
-- list.sum [list.sum [f (u, u') | u in (v\s)] |  u' in s]

-- def mk_in : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hnonsymm⟩ f  := λs,  ∑ u in (v \ s) , ∑ u' in s, f (u, u')

-- Man kan ju tänka på typer som en samling saker, och då blir `x : β` typ samma sak som `x ∈ β`.  `set β` defineras som `def set (α : Type u) := α → Prop`, d.v.s. ett predikat som avgör vilka element i typen som är med i mängden.  `set β` blir då ungefär som `𝒫(β)`
