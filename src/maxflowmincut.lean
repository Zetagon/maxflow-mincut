import data.real.basic
import data.set
import tactic
import data.finset
open set

open_locale big_operators
universes u

variable α : Type u

local notation `V` := finset α
local notation `E` := finset (α × α)

class digraph :=
  (nodes : V)
  (edges : E)
  (subset : ∀e: α × α, e ∈ edges → (e.1 ∈ nodes ∧ e.2 ∈ nodes))
  --(subset : ∀e ∈ edges, (e.1 ∈ nodes ∧ e.2 ∈ nodes))
  --(subset : ∀ ⟨u, v⟩ ∈ edges → (u ∈ nodes ∧ v ∈ nodes))
  (nonsymmetric : ∀ (u v : α ), (u, v) ∈ edges → (v, u) ∉ edges)

class capacity := 
  (G : digraph α)
  (capacity : E -> ℝ)
  (postive_capacity : ∀ x : E, capacity x ≥ 0)
  --(vanishes : )
  

@[class] structure flow_network
  extends digraph α :=
  (source : α)
  (sink : α)
  (capacity : E -> ℝ)
  (postive_capacity : ∀ x : E, capacity x ≥ 0)

open_locale classical 
noncomputable def mk_in : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
| ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  ∑ u in s, ∑ u' in (v \ s), f (u, u')--∑ e' in (v \ s) × s, f(e')--∑ u in (v \ s)

def mk_out : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
| ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  sorry--∑ e' in (v \ s) × s, f(e')--∑ u in s, ∑ u' in (v \ s), f (u, u')
