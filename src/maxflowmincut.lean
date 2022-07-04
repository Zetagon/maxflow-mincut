import data.real.basic
import data.set
import tactic
import data.finset
open set
open quiver
open finset

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
  := ∑ x in finset.univ \ s, ∑ y in s, f x y

noncomputable def mk_out {V : Type* } [inst : fintype V]
  (f : V -> V -> ℝ) (s : finset V) : ℝ
  := ∑ x in s, ∑ y in finset.univ \ s, f x y


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


lemma foobar { a b : ℝ } : a + - b = a - b := rfl

lemma mk_in_single_node { V : Type* } [fintype V] (p : V) (f : V -> V -> ℝ) :
            mk_in f {p} = ∑ v in finset.univ \ {p}, f v p :=
  begin
    sorry
  end

lemma mk_out_single_node { V : Type* } [fintype V] {s : finset V} {f : V -> V -> ℝ} :
            mk_out f s = ∑ u in finset.univ, ∑ v in finset.univ \ s, f u v :=
      by simp only [mk_out]

notation ` V' ` := univ

lemma lemma_1 {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) :
S ⊂ finset.univ \ {afn.network.source, afn.network.sink} -> mk_in afn.f S = mk_out afn.f S
:=
begin
  intro hin,
  rw ← add_left_inj (- mk_out afn.f S),
  simp only [add_right_neg],
  rw ← add_zero (mk_in afn.f S),
  nth_rewrite 0 ← add_neg_self (∑ u in S, (∑ v in S, afn.f u v)),
  rw ← add_assoc,
  have tmp : mk_in afn.f S + ∑ (u : V) in S, ∑ (v : V) in S, afn.f u v =
             ∑ u in S, ∑ v in finset.univ, afn.f v u
             := by sorry,

  have tmp2: (-∑ (u : V) in S, ∑ (v : V) in S, afn.f u v) + -mk_out afn.f S =
             - ∑ u in S, ∑ v in finset.univ, afn.f u v
             := by sorry,
  rw tmp,
  rw add_assoc,
  rw tmp2,
  clear tmp tmp2,
  have foo : ∑ (u : V) in S, ∑ (v : V) in V' \ S,
               afn.f v u
             -
             ∑ (u : V) in S,
                ∑ (v : V) in V' \ S, afn.f u v
           =
             ∑ (u : V) in S,
               (∑ (v : V), afn.f v u - ∑ (v : V), afn.f u v ) :=
      begin
        rw ← @sum_sub_distrib _ _ S (λ u, ∑ (v : V) in V' \S, afn.f v u) (λ u, ∑ (v : V), afn.f u v) _,
      end,

  rw foobar,
  rw foo,
  rw ← mk_in_single_node u afn.f,
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
