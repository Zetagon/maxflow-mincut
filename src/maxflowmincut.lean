import data.real.basic
import data.set
import tactic
open set

open_locale big_operators
universes u

variable α : Type u

local notation `V` := set α
local notation `E` := set (α × α)

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
def foobar : (digraph α) -> (V × V -> ℝ) -> (V -> ℝ)
| ⟨v, e, hnonsymm⟩ f  := λs,  ∑ e in (v ∪ s) × s, f e
