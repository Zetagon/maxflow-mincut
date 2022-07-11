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

lemma f_zero_zero {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : afn.f x x = 0 :=
begin
 have hnonsymm : _ := afn.network.hnonsymmetric x x,
 have hvanish: _ := afn.network.vanishes x x,
 simp only [not_and, imp_not_self] at hnonsymm,
 have hnon_edge := hnonsymm, clear hnonsymm,
 have hcapacity_zero := hvanish hnon_edge,
 have hno_overflow := afn.no_overflow x x,
 rw hcapacity_zero at hno_overflow,
 have hnon_neg_flow := afn.non_neg_flow x x,
 linarith,
end


lemma mk_in_single_node { V : Type* } [inst : quiver.{0} V] [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_in (afn.f) {p} = ∑ v in finset.univ, (afn.f) v p :=
  begin
      rw @sum_eq_sum_diff_singleton_add _ _ _ _ univ p (by simp) (λ x, afn.f x p),
      have foo : (λ (x : V), afn.f x p) p = afn.f p p := rfl,
      simp only [congr_fun],
      rw f_zero_zero afn p,
      have bar : ∑ (x : V) in univ \ {p}, afn.f x p + 0 = (λp', ∑ (x : V) in univ \ {p'}, afn.f x p' ) p
      := by simp,
      rw bar, clear bar,
      rw ← @finset.sum_singleton _ _ p (λp', ∑ (x : V) in univ \ {p'}, afn.f x p' ) _,
      simp [mk_in],
  end

@[simp] lemma mk_in_single_node' { V : Type* } [inst : quiver.{0} V] [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) v p = mk_in (afn.f) {p} :=
  by rw mk_in_single_node

lemma mk_out_single_node { V : Type* } [quiver.{0} V] [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_out afn.f {p} = ∑ v in finset.univ, (afn.f) p v :=
begin
  sorry,
end

@[simp] lemma mk_out_single_node' { V : Type* } [quiver.{0} V] [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) p v = mk_out afn.f {p} :=
  by rw mk_out_single_node

notation ` V' ` := univ

lemma break_out_neg (a b : ℝ) : (-a) + -(b) = -(a + b) :=
by ring

noncomputable
def tmp_f {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : ℝ
:= (mk_out afn.f {x} - mk_in afn.f {x})

def tmp_zero {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : ℝ
:= 0

lemma lemma_1 {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) :
S ⊆ finset.univ \ {afn.network.source, afn.network.sink} -> mk_in afn.f S = mk_out afn.f S
:=
begin
  intro hin,
  rw ← add_left_inj (- mk_out afn.f S),
  simp only [add_right_neg],
  rw ← add_zero (mk_in afn.f S),
  nth_rewrite 0 ← add_neg_self (∑ u in S, (∑ v in S, afn.f u v)),
  rw ← add_assoc,
  have tmp : mk_in afn.f S + ∑ u in S, ∑ v in S, afn.f u v =
             ∑ u in S, ∑ v in finset.univ, afn.f u v
             := by sorry,

  have tmp2: mk_out afn.f S + (∑ u in S, ∑ v in S, afn.f u v) =
             ∑ u in S, ∑ v in finset.univ, afn.f v u
             := by sorry,
  rw tmp,
  rw add_assoc,
  rw break_out_neg,
  nth_rewrite 1 add_comm,
  rw tmp2,
  clear tmp tmp2,
  rw foobar,
  rw ← @sum_sub_distrib _ _ S _ _ _,
  simp only [mk_in_single_node', mk_out_single_node'],
  -- have f := λ x, (mk_out afn.f {x} - mk_in afn.f {x}),
  have hseq : S = S := rfl,
  have h : ∀ (x : V), x ∈ S -> tmp_f afn x = tmp_zero afn x :=
  begin
    intros x hx,
    unfold tmp_f,
    unfold tmp_zero,
    rw afn.conservation x,
    { ring, },
    { exact finset.mem_of_subset hin hx,}
  end,
  have foo := finset.sum_congr hseq h,
  unfold tmp_f at foo,
  rw foo,
  unfold tmp_zero,
  simp,
end

lemma out_in_disjunct {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S T : finset V) (disjunct : ∀ (x : V), x ∈ S → x ∉ T ) :
  mk_out afn.f (S ∪ T) - mk_in afn.f (S ∪ T) = mk_out afn.f S + mk_out afn.f T - mk_in afn.f S - mk_in afn.f T :=
begin
  -- simp only [mk_in, mk_out],
  -- rw ← disj_union_eq_union S T disjunct,
  -- rw finset.sum_disj_union disjunct,
  sorry,
end

lemma out_as_in {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V): 
  mk_out afn.f S = mk_in afn.f (univ \ S) := --Perhaps reconsider univ
  begin
    rw mk_out,
    rw mk_in, 
    rw sum_comm,
    rw sum_comm,
    have foo: S = univ \ (univ \ S):=
    begin
      simp only [sdiff_sdiff_right_self, finset.inf_eq_inter, finset.univ_inter],
    end,
    nth_rewrite 0 foo,
  end

lemma in_as_out {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
(afn : active_flow_network V) (S : finset V): 
  mk_in afn.f S = mk_out afn.f (univ \ S) := 
  begin  
    have foo: S = univ \ (univ \ S):= --This occurs in the previous lemma.
    begin
      simp only [sdiff_sdiff_right_self, finset.inf_eq_inter, finset.univ_inter],
    end,
    nth_rewrite 0 foo,
    rw out_as_in,
  end


lemma flow_value_global_ver {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V): 
  mk_out afn.f {afn.network.source} - mk_in afn.f {afn.network.source} = mk_out afn.f ct.S - mk_in afn.f ct.S:=
  begin
    sorry
  end

lemma outFlow_leq_outCut {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) : mk_out afn.f S ≤ mk_out afn.network.c S
  :=
  begin
    sorry
  end

lemma flow_leq_cut {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
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
  (afn : active_flow_network V) (ct : cut V) (hsame_network: afn.network = ct.network):
  cut_value ct = F_value afn -> is_max_flow_network afn ∧ is_min_cut ct
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
