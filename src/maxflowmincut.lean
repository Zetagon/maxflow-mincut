import data.real.basic
import data.set
import tactic
import data.finset
open set

open_locale big_operators
open_locale classical
universes u

variable V : Type u


class digraph [fintype V]
  extends quiver V
  :=
  (hnonsymmetric : ∀ u v : V, ¬ (hom u v ∧ hom v u))


class capacity [fintype V]
  extends digraph V:=
  (capacity : V -> V -> ℝ)
  (non_neg_capacity : ∀ u v : V, capacity u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (hom u v) → capacity u v = 0)

class flow_network [fintype V]
  extends capacity V :=
  (source : V)
  (sink : V)

def Vset [fintype V] : finset V
:= finset.univ

noncomputable def mk_in [fintype V] : (V -> V -> ℝ) -> (finset V -> ℝ)
| f := λ s, ∑ x in Vset V \ s, ∑ y in Vset V, f x y

noncomputable def mk_out [fintype V] : (V -> V -> ℝ) -> (finset V -> ℝ)
| f := λ s, ∑ x in Vset V, ∑ y in Vset V \ s, f x y

class active_flow_network [fintype V]
  extends flow_network V :=
  (f : V -> V -> ℝ)
  (non_neg_flow : ∀ u v : V, f u v ≥ 0)
  (no_overflow : ∀ u v : V, f u v ≤ capacity u v)
  (conservation : ∀ v : V, 
                  v ∈ Vset V \ {source, sink} → 
                  mk_out V f {v} = mk_in V f {v})

noncomputable def F_value [fintype V] : active_flow_network V -> ℝ
:= λ N, mk_out V N.f {N.sink} - mk_in V N.f {N.sink}



-- open_locale classical
-- noncomputable def mk_in : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  ∑ u in s, ∑ u' in (v \ s), f (u, u')--∑ e' in (v \ s) × s, f(e')--∑ u in (v \ s)

-- def mk_out : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  sorry--∑ e' in (v \ s) × s, f(e')--∑ u in s, ∑ u' in (v \ s), f (u, u')
