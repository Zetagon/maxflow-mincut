import data.real.basic
import data.set
import tactic
import data.finset
open set

open_locale big_operators
universes u

variable V : Type u


class digraph
  extends quiver V
  :=
  (hnonsymmetric : ∀ u v : V, ¬ (hom u v ∧ hom v u))


class capacity
  extends digraph V:=
  (capacity : V -> V -> ℝ)
  (positive_capacity : ∀ u v : V, capacity u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (hom u v) → capacity u v = 0)

class flow_network
  extends capacity V :=
  (source : V)
  (sink : V)

def Vset : set V
:= λ x, true


def mk_out : (V -> ℝ) -> (set V -> ℝ)
| f := λ s, ∑ y in Vset V, f  y

-- open_locale classical
-- noncomputable def mk_in : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  ∑ u in s, ∑ u' in (v \ s), f (u, u')--∑ e' in (v \ s) × s, f(e')--∑ u in (v \ s)

-- def mk_out : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  sorry--∑ e' in (v \ s) × s, f(e')--∑ u in s, ∑ u' in (v \ s), f (u, u')
