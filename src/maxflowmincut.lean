import data.real.basic
import data.set
import tactic
import data.finset
open set
open quiver

open_locale big_operators
open_locale classical

structure strange_digraph (V : Type*) [quiver.{0} V] :=
  (hnonsymmetric : ∀ u v : V, ¬ ((u ⟶ v) ∧ (v ⟶ u)))


structure capacity (V : Type*) [quiver.{0} V]
  extends strange_digraph V:=
  (c : V -> V -> ℝ)
  (non_neg_capacity : ∀ u v : V, c u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (u ⟶ v) → c u v = 0)

structure flow_network (V : Type*) [quiver.{0} V]
  extends capacity V :=
  (source : V)
  (sink : V)

noncomputable def mk_in {V : Type* } [inst : fintype V]
  (f : V -> V -> ℝ) (s : finset V) : ℝ
  := ∑ x in finset.univ \ s, ∑ y in finset.univ, f x y

noncomputable def mk_out {V : Type* } [inst : fintype V]
  (f : V -> V -> ℝ) (s : finset V) : ℝ
  := ∑ x in finset.univ, ∑ y in finset.univ \ s, f x y


structure active_flow_network (V : Type*) [quiver.{0} V] [fintype V]
  :=
  (network : flow_network V)
  (f : V -> V -> ℝ)
  (non_neg_flow : ∀ u v : V, f u v ≥ 0)
  (no_overflow : ∀ u v : V, f u v ≤ network.c u v)
  (conservation : ∀ v : V, 
                  v ∈ (finset.univ : finset V) \ {network.source, network.sink} →
                  mk_out f {v} = mk_in f {v})

noncomputable def F_value {V : Type*} [quiver.{0} V] [fintype V] :
                  active_flow_network V -> ℝ
:= λ N, mk_out N.f {N.network.sink} - mk_in N.f {N.network.sink}

structure cut (V : Type*) [quiver.{0} V] [fintype V]
  :=
  (network : flow_network V)
  (S : finset V)
  (T : finset V)
  (disjoint : S ∩ T = ∅)
  (fill : S ∪ T = finset.univ)

noncomputable
def cut_value {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
    (c : cut V) : ℝ
:= mk_out c.network.c c.S


lemma lemma_1 {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) :
S ⊂ finset.univ \ {afn.network.source, afn.network.sink} -> mk_in afn.f S = mk_out afn.f S
:=
begin
  sorry
end

lemma lemma_2  {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V):
  afn.network = ct.network → F_value afn ≤ cut_value ct :=
begin
  sorry
end

def is_max_flow_network  {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (fn: active_flow_network V) : Prop
:= ∀ fn' : active_flow_network V, fn.network = fn'.network → F_value fn ≥ F_value fn'

def is_min_cut {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (fn: cut V) : Prop
:= ∀ fn' : cut V, fn.network = fn'.network → cut_value fn ≤ cut_value fn'


lemma superlemma_1  {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) :
  afn.network = ct.network -> cut_value ct = F_value afn -> is_max_flow_network afn ∧ is_min_cut ct
  :=
  begin
  sorry
  end


structure residual_network  {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  :=
  (f : V -> V -> ℝ)
  (source : V)
  (sink : V)

noncomputable
def mk_cf {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (n : active_flow_network V)
  (u v : V)
  : ℝ
:= if  u ⟶ v
   then n.network.c  u v - n.f u v
   else if v ⟶ u
        then n.f v u
        else 0

noncomputable
def mk_residual_network {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V)
  : residual_network
  := ⟨mk_cf afn, afn.network.source, afn.network.sink⟩
