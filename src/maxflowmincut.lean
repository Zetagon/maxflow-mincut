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
  (c : V -> V -> ℝ)
  (non_neg_capacity : ∀ u v : V, c u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (hom u v) → c u v = 0)

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

--class flow [fintype] :=
--  (fn : flow_network)


class active_flow_network [fintype V]
  :=
  (network : flow_network V)
  (f : V -> V -> ℝ)
  (non_neg_flow : ∀ u v : V, f u v ≥ 0)
  (no_overflow : ∀ u v : V, f u v ≤ capacity.c u v)
  (conservation : ∀ v : V, 
                  v ∈ Vset V \ {network.source, network.sink} →
                  mk_out V f {v} = mk_in V f {v})

noncomputable def F_value [fintype V] : active_flow_network V -> ℝ
:= λ N, mk_out V N.f {N.network.sink} - mk_in V N.f {N.network.sink}

--def make_cut [fintype V] : flow_network V -> (V -> Prop) -> Prop
--:= λ N f, 

class cut [fintype V]
  :=
  (network : flow_network V)
  (S : finset V)
  (T : finset V)
  (disjoint : S ∩ T = ∅)
  (fill : S ∪ T = Vset V)

noncomputable def cut_value [fintype V] : cut V -> ℝ
:= λ N, mk_out V N.network.c N.S


lemma lemma_1 [fintype V] (afn : active_flow_network V) (S : finset V) : 
S ⊂ Vset V \ {afn.network.source, afn.network.sink} -> mk_in V afn.f S = mk_out V afn.f S
:=
begin
  sorry
end

lemma lemma_2 [fintype V] (afn : active_flow_network V) (ct : cut V):
  afn.network = ct.network → F_value V afn ≤ cut_value V ct :=
begin
  sorry
end

def is_max_flow_network [fintype V] (fn: active_flow_network V) : Prop
:= ∀ fn' : active_flow_network V, fn.network = fn'.network → F_value V fn ≥ F_value V fn'

def is_min_cut [fintype V] (fn: cut V) : Prop
:= ∀ fn' : cut V, fn.network = fn'.network → cut_value V fn ≤ cut_value V fn'


lemma superlemma_1 [fintype V] (afn : active_flow_network V) (ct : cut V) :
  afn.network = ct.network -> cut_value V ct = F_value V afn -> is_max_flow_network V afn ∧ is_min_cut V ct
  :=
  begin
  sorry
  end


class residual_network [fintype V]
  extends quiver V :=
  (source : V)
  (sink : V)

def mk_cf [fintype V] : active_flow_network V -> V -> V -> ℝ
:= λ n u v,
  if @capacity.c V _ _  = 3 then

-- open_locale classical
-- noncomputable def mk_in : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  ∑ u in s, ∑ u' in (v \ s), f (u, u')--∑ e' in (v \ s) × s, f(e')--∑ u in (v \ s)

-- def mk_out : (digraph α) -> (α × α -> ℝ) -> (V -> ℝ)
-- | ⟨v, e, hsubset, hnonsymm⟩ f  := λs,  sorry--∑ e' in (v \ s) × s, f(e')--∑ u in s, ∑ u' in (v \ s), f (u, u')
