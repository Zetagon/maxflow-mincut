import data.real.basic
import data.set
import tactic
import data.finset
import tactic.induction
open finset


open_locale big_operators
open_locale classical

--constant X : finset ℕ
--X = ({ x : ℕ // x < 5})
--X = 2
--#print X
--inductive oier : Sort*
--| a 
--| b
--| c 
--def aosdjfl : finset oier 
--:= let x := ({oier.a} : finset oier)
--   in xᶜ
notation ` V' ` := univ

structure strange_digraph (V : Type*)  :=
  (is_edge : V → V → Prop)
  (hnonsymmetric : ∀ u v : V, ¬ ((is_edge u v) ∧ (is_edge v u)))

structure capacity (V : Type*)
  extends strange_digraph V:=
  (c : V -> V -> ℝ)
  (non_neg_capacity : ∀ u v : V, c u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (is_edge u v) → c u v = 0)

structure flow_network (V : Type*)
  extends capacity V :=
  (source : V)
  (sink : V)

noncomputable
def mk_in {V : Type* } [inst : fintype V]
  (f : V -> V -> ℝ) (s : finset V) : ℝ
  := ∑ x in finset.univ \ s, ∑ y in s, f x y

noncomputable
def mk_out {V : Type* } [inst : fintype V]
  (f : V -> V -> ℝ) (s : finset V) : ℝ
  := ∑ x in s, ∑ y in finset.univ \ s, f x y


structure active_flow_network (V : Type*)  [fintype V]
  :=
  (network : flow_network V)
  (f : V -> V -> ℝ)
  (non_neg_flow : ∀ u v : V, f u v ≥ 0)
  (no_overflow : ∀ u v : V, f u v ≤ network.c u v)
  (conservation : ∀ v : V, 
                  v ∈ (V' : finset V) \ {network.source, network.sink} →
                  mk_out f {v} = mk_in f {v})

noncomputable def F_value {V : Type*}  [fintype V] :
                  active_flow_network V -> ℝ
:= λ N, mk_out N.f {N.network.source} - mk_in N.f {N.network.source}

structure cut (V : Type*)  [fintype V]
  :=
  (network : flow_network V)
  (S : finset V)
  (T : finset V)
  (sins : network.source ∈ S)
  (tint : network.sink ∈ T)
  (Tcomp : T = univ \ S)

noncomputable
def cut_value {V : Type*}  [inst' : fintype V]
    (c : cut V) : ℝ
:= mk_out c.network.c c.S


lemma f_vanishes_outside_edge {V : Type*} [fintype V] 
  (afn : active_flow_network V) (u : V) (v : V) (not_edge: ¬afn.network.is_edge u v): afn.f u v = 0 := 
  begin
    have cap_is_zero: afn.network.c u v = 0 :=
      begin
        exact afn.network.vanishes u v not_edge,
      end,
    have bar := afn.no_overflow u v,
    have foo := afn.non_neg_flow u v,
    linarith,
  end

lemma x_not_in_s {V : Type*} [fintype V]
  (c : cut V)  : ∀ x : V, x ∈ c.T -> x ∉ ({c.network.source} : finset V) :=
begin
  intros x hxinS,
  cases c,
  simp only [mem_singleton] at *,
  rw c_Tcomp at hxinS,
  have foo : univ \ c_S ∩ c_S = ∅ := sdiff_inter_self c_S univ,
  have foo : disjoint (univ \ c_S)  c_S  := sdiff_disjoint,
  have bar : c_network.source ∈ c_S := c_sins,
  exact disjoint_iff_ne.mp foo x hxinS c_network.source c_sins
end

lemma foobar { a b : ℝ } : a + - b = a - b := rfl

lemma f_zero_zero {V : Type*}  [inst' : fintype V]
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


lemma mk_in_single_node { V : Type* }  [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_in (afn.f) {p} = ∑ v in finset.univ, (afn.f) v p :=
  begin
      rw @sum_eq_sum_diff_singleton_add _ _ _ _ univ p (by simp only [mem_univ]) (λ x, afn.f x p),
      have foo : (λ (x : V), afn.f x p) p = afn.f p p := rfl,
      simp only [congr_fun],
      rw f_zero_zero afn p,
      have bar : ∑ (x : V) in univ \ {p}, afn.f x p + 0 = (λp', ∑ (x : V) in univ \ {p'}, afn.f x p' ) p
      := by simp only [add_zero],
      rw bar, clear bar,
      rw ← @finset.sum_singleton _ _ p (λp', ∑ (x : V) in univ \ {p'}, afn.f x p' ) _,
      simp only [mk_in, sum_singleton],
  end

@[simp] lemma mk_in_single_node' { V : Type* }  [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) v p = mk_in (afn.f) {p} :=
  by rw mk_in_single_node

lemma mk_out_single_node { V : Type* }  [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_out afn.f {p} = ∑ v in finset.univ, (afn.f) p v :=
begin
  sorry,
end

@[simp] lemma mk_out_single_node' { V : Type* }  [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) p v = mk_out afn.f {p} :=
  by rw mk_out_single_node


lemma break_out_neg (a b : ℝ) : (-a) + -(b) = -(a + b) :=
by ring

noncomputable
def tmp_f {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : ℝ
:= (mk_out afn.f {x} - mk_in afn.f {x})

def tmp_zero {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : ℝ
:= 0

lemma lemma_1 {V : Type*}  [inst' : fintype V]
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
  simp only [sum_const_zero],
end

lemma out_in_disjunct {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S T : finset V) (disjunct : ∀ (x : V), x ∈ S → x ∉ T ) :
  mk_out afn.f (S ∪ T) - mk_in afn.f (S ∪ T) = mk_out afn.f S + mk_out afn.f T - mk_in afn.f S - mk_in afn.f T :=
begin
  have foo : mk_out afn.f (S ∪ T) + ∑ u in S, ∑ v in T, afn.f u v + ∑ u in T, ∑ v in S, afn.f u v
             =
             mk_out afn.f S + mk_out afn.f T
  :=
  begin
    have mk_out1 : mk_out afn.f S = ∑ (x : V) in S, ∑ (y : V) in univ \ S, afn.f x y := rfl,
    have mk_out2 : mk_out afn.f T = ∑ (x : V) in T, ∑ (y : V) in univ \ T, afn.f x y := rfl,
    unfold1 mk_out,
    rw ← mk_out1,
    rw ← mk_out2,
    clear mk_out1,
    clear mk_out2,
    rw ← disj_union_eq_union S T disjunct,
    rw finset.sum_disj_union disjunct,
    have foo : ∀ (x : V), x ∈ univ \ S.disj_union T disjunct → x ∉ T := sorry,
    have bar : ∀ (x : V), x ∈ univ \ S.disj_union T disjunct → x ∉ S := sorry,
    exact calc
     ∑ (x : V) in S, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
               ∑ (x : V) in T, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
               ∑ (u : V) in S, ∑ (v : V) in T, afn.f u v +
               ∑ (u : V) in T, ∑ (v : V) in S, afn.f u v
               =
               ∑ (x : V) in S, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
               ∑ (u : V) in S, ∑ (v : V) in T, afn.f u v +
               (∑ (x : V) in T, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
                ∑ (u : V) in T, ∑ (v : V) in S, afn.f u v) : by linarith
         ... = ∑ (u : V) in S, (∑ (v : V) in (V' \ S.disj_union T disjunct), afn.f u v +
                                ∑ v in T, afn.f u v) +
               (∑ (u : V) in T, (∑ (v : V) in V' \ S.disj_union T disjunct, afn.f u v +
                                 ∑ (v : V) in S, afn.f u v)) : begin  rw ← sum_add_distrib, rw ← sum_add_distrib,  end
           ... = ∑ (u : V) in S, (∑ (v : V) in (V' \ S.disj_union T disjunct).disj_union T foo, afn.f u v) +
               (∑ (u : V) in T, (∑ (v : V) in (V' \ S.disj_union T disjunct).disj_union S bar, afn.f u v +
                                 ∑ (v : V) in S, afn.f u v))  :
               begin
                 simp_rw ← finset.sum_disj_union foo,
                 sorry,
                 -- simp_rw ← finset.sum_disj_union foo,
               end
           ... = mk_out afn.f S + mk_out afn.f T : sorry,
    -- rw tmp, clear tmp,
    -- have tmp : ∑ (x : V) in S, (∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y + ∑ (v : V) in T, afn.f x v) +
    --            (∑ (x : V) in T, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
    --             ∑ (u : V) in T, ∑ (v : V) in S, afn.f u v)
    --            =
    --            ∑ (x : V) in S, (∑ (y : V) in (V' \ S.disj_union T disjunct).disj_union T foo, afn.f x y) +
    --            (∑ (x : V) in T, ∑ (y : V) in V' \ S.disj_union T disjunct, afn.f x y +
    --             ∑ (u : V) in T, ∑ (v : V) in S, afn.f u v) :=
    -- begin

    -- end,
    -- rw ← sum_add_distrib,
    -- rw ← finset.sum_disj_union foo,
  end,

  -- simp only [mk_in, mk_out],
  -- rw ← disj_union_eq_union S T disjunct,
  -- rw finset.sum_disj_union disjunct,


  sorry,
end

lemma out_as_in {V : Type*}  [inst' : fintype V]
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

lemma in_as_out {V : Type*}  [inst' : fintype V]
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



lemma S_minus_s_eq_T_union_s {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V):
  V' \ (ct.S \ {afn.network.source}) = ct.T ∪ {afn.network.source} :=
begin
  rw sdiff_sdiff_right',
  simp only [inf_eq_inter, univ_inter, sup_eq_union],
  have fljlkoo : (V' \ ct.S) = ct.T :=
  begin
    rw cut.Tcomp,
  end,
  rw fljlkoo,
end

lemma zero_left_move {a b c d : ℝ} : (0 = a + b - c - d) -> (d - b = a - c) :=
begin
  intro h,
  linarith,
end
lemma flow_value_global_ver {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V)
  (h_equal_networks : afn.network = ct.network) :
  mk_out afn.f {afn.network.source} - mk_in afn.f {afn.network.source} = mk_out afn.f ct.S - mk_in afn.f ct.S:=
  begin
    set S := ct.S,
    set T := ct.T,
    set s := afn.network.source,
    set t := afn.network.sink,
    set f := afn.f,
    have hs : s = afn.network.source := rfl,
    have hT : T = ct.T := rfl,
    have foo : mk_out f (S \ {s}) = mk_in f (T ∪ {s})
    :=
    begin
      rw ← S_minus_s_eq_T_union_s,
      exact out_as_in afn (S \ {s}),
    end,
    have bar : mk_in f (S \ {s}) = mk_out f (T ∪ {s})
    :=
    begin
      rw ← S_minus_s_eq_T_union_s,
      exact in_as_out afn (S \ {s}),
    end,
    have baz : 0 = mk_out f S + mk_in f {s} - mk_in f S - mk_out f {s} :=
    calc 0 = mk_out f (S \ {s}) - mk_out f (S \ {s}) : (sub_self (mk_out f (S \ {s}))).symm
       ... =  mk_out f (S \ {s}) - mk_in f (S \ {s}) :
       begin
         have baz : S \ {s} ⊆ V' \ {s, t} := begin
           sorry
         end,
         rw lemma_1 afn (S \ {s}) baz,
       end
       ... = mk_in f (T ∪ {s}) - mk_out f (T ∪ {s}) :
       begin
         rw foo,
         rw bar,
       end
       ... = - (mk_out f (T ∪ {s}) - mk_in f (T ∪ {s})) : (neg_sub (mk_out f (T ∪ {s})) (mk_in f (T ∪ {s}))).symm
       ... = mk_in f T + mk_in f {s} - mk_out f T - mk_out f {s} :
       begin
         rw hs, rw hT,
         have blurg := (x_not_in_s ct),
         rw ← h_equal_networks at blurg,
         rw out_in_disjunct afn ct.T {afn.network.source} blurg,
         ring,
       end
       ... = mk_out f S + mk_in f {s} - mk_in f S - mk_out f {s}  :
       begin
         simp_rw [in_as_out, out_as_in],
         simp only [sdiff_sdiff_right_self, inf_eq_inter, univ_inter, sub_left_inj],
         rw ← ct.Tcomp,
         simp only [sub_right_inj],
         have b : V' \ T = S :=
         begin
           rw [hT, ct.Tcomp],
           simp only [sdiff_sdiff_right_self, inf_eq_inter, univ_inter],
         end,
         rw b,
       end,
       exact zero_left_move baz,
  end

lemma outFlow_leq_outCut {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) : mk_out afn.f S ≤ mk_out afn.network.c S
  :=
  begin
    sorry
  end

lemma major_doublesum {V : Type*} (X : finset V) (Y : finset V) (f : V → V → ℝ) (g : V → V → ℝ): (∀ x y: V, f x y ≤ g x y) → 
∑ (x : V) in X, ∑ (y : V) in Y, f x y ≤ ∑ (x : V) in X, ∑ (y : V) in Y, g x y:=
  begin
    sorry
  end

lemma flow_leq_cap_global_ver {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V): mk_out afn.f S ≤ mk_out afn.network.c S
  := 
  begin
    sorry,
  end

lemma sub_non_neg_ineq (x : ℝ) (y : ℝ): y ≥ 0 -> x-y ≤ x
:= begin simp only [sub_le_self_iff, imp_self] end

lemma mk_in_non_neg {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V): mk_in afn.f S ≥ 0
  := 
  begin
    sorry
  end

lemma flow_leq_cut {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) (same_net : afn.network = ct.network):
  F_value afn ≤ cut_value ct :=
begin 
  unfold F_value,
  rw flow_value_global_ver afn ct same_net,

  have foo: mk_out afn.f ct.S - mk_in afn.f ct.S ≤ mk_out afn.f ct.S :=
    begin
      exact sub_non_neg_ineq (mk_out afn.f ct.S) (mk_in afn.f ct.S) (mk_in_non_neg afn ct.S),
    end,
  
  have bar: mk_out afn.f ct.S ≤ mk_out afn.network.c ct.S :=
    begin
      rw [mk_out, mk_out],
      have blurg: ∀ (x y : V), (afn.f x y ≤ afn.network.to_capacity.c x y) :=
        begin
          exact afn.no_overflow,
        end,
      exact major_doublesum (ct.S) (V' \ ct.S) (afn.f) (afn.network.c) (blurg),
    end,
  
  have blurg: mk_out afn.network.to_capacity.c ct.S = cut_value ct :=
    begin
      rw same_net,
      refl,
    end,

  have soap: mk_out afn.f ct.S - mk_in afn.f ct.S ≤ mk_out afn.network.to_capacity.c ct.S :=
    begin
      exact le_trans (foo) (bar),
    end,
  
  rw blurg at soap,
  exact soap,
end

def is_max_flow_network  {V : Type*}  [inst' : fintype V]
  (fn: active_flow_network V) : Prop
:= ∀ fn' : active_flow_network V, fn.network = fn'.network → F_value fn' ≤ F_value fn

def is_min_cut {V : Type*}  [inst' : fintype V]
  (fn: cut V) : Prop
:= ∀ fn' : cut V, fn.network = fn'.network → cut_value fn ≤ cut_value fn'


lemma superlemma_1  {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) (hsame_network: afn.network = ct.network):
  cut_value ct = F_value afn -> is_max_flow_network afn --∧ is_min_cut ct
  :=
  begin
    intro h_eq_val,
    intro fn, 
    intro h_same_net,
    rw ← h_eq_val,
    have blorgon: fn.network = ct.network :=
    begin
      rw ← h_same_net,
      exact hsame_network,
    end,
    exact flow_leq_cut (fn) (ct) (blorgon),
  end

lemma imp_is_trans {p : Prop} {q : Prop} {r : Prop} (h_1: p → q) (h_2: q → r): (p → r)
:= 
begin
  exact h_2 ∘ h_1,
  --intro p,
  --exact h_2(h_1(p)),
end

noncomputable
def mk_cf {V : Type*}  [inst' : fintype V]
  (n : active_flow_network V)
  (u v : V)
  : ℝ
:= if  n.network.is_edge u v
   then n.network.c  u v - n.f u v
   else if n.network.is_edge v u
        then n.f v u
        else 0

structure residual_network  (V : Type*)  [inst' : fintype V]
  :=
  (afn : active_flow_network V)
  (f' : V -> V -> ℝ)
  (f_def : f' = mk_cf afn)
  (is_edge : V -> V -> Prop)
  (is_edge_def : is_edge = λ u v, f' u v > 0 )


noncomputable
def mk_rsn {V : Type*} [fintype V]
  (afn : active_flow_network V) : residual_network V
:= ⟨afn, mk_cf afn, rfl, λ u v, mk_cf afn u v > 0 , rfl ⟩

universe u

inductive path {V : Type u } (is_edge : V -> V -> Prop) (a : V) : V → Type (u + 1)
| nil  : path a
| cons : Π {b c : V}, path b → (is_edge b c) → path c

def no_augumenting_path {V : Type*} [inst' : fintype V]
  (rsn : residual_network V) : Prop
  := ∀ t : V, ∀ p : path rsn.is_edge rsn.afn.network.source t, ¬ (t = rsn.afn.network.sink)

def path.in {V : Type u }
  {is_edge : V -> V -> Prop}
  (u v : V)
  {s : V}
  : ∀ {t : V}, path is_edge s t  -> Prop
  | t (@path.nil  _ is_edge' a)  := u = v
  | t (@path.cons _ _ _ t' _ p _)  := (u = t' ∧ v = t) ∨ (@path.in t' p)

lemma residual_capacity_non_neg {V : Type*} [inst' : fintype V]
  (rsn : residual_network V)
  : ∀ u v : V,  0 ≤ rsn.f' u v :=
begin
  intros u v,
  cases rsn,
  simp only,
  rw rsn_f_def,
  unfold mk_cf,
  have tmp := classical.em (rsn_afn.network.to_capacity.to_strange_digraph.is_edge u v),
  cases tmp,
  {
    simp only [tmp, if_true, sub_nonneg, rsn_afn.no_overflow],
  },
  {
    simp only [tmp, if_false], clear tmp,
    have tmp := classical.em (rsn_afn.network.to_capacity.to_strange_digraph.is_edge v u),
    cases tmp,
    {
      have tmp' := rsn_afn.non_neg_flow v u,
      simp only [tmp, tmp', if_true],
      linarith,
    },
    {
      simp only [tmp, if_false],
    },
  },
end

@[simp]
noncomputable
def augumenting_path_min_weight {V : Type*} [inst' : fintype V]
  (rsn : residual_network V)
  {s : V} :
  ℝ -> Π {t : V}, path rsn.is_edge s t -> ℝ
  | weight _ path.nil := weight
  | weight t (@path.cons _ _ _ t' _ p is_edge') :=
  if (weight < rsn.f' t' t) && (rsn.f' t' t ≠ 0)
  then augumenting_path_min_weight (rsn.f' t' t) p
  else augumenting_path_min_weight weight p

lemma min_weight {V : Type*} [inst' : fintype V]
  (rsn : residual_network V)
  (s t : V)
  (p : path rsn.is_edge s t) :
  ∀ u v : V, path.in u v p -> augumenting_path_min_weight rsn 0 p ≤ rsn.f' u v :=
begin
  intros u v hin_p,
  induction' p,
  {
    simp,
    simp_rw [rsn.f_def, mk_cf],
    cases classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge u v),
    {
      simp [h],
      exact rsn.afn.no_overflow u v,
    },
    {
      simp [h],
      cases classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge v u),
      {
        simp [h_1],
        exact rsn.afn.non_neg_flow v u,
      },
      {
        simp [h_1],
      }
    }
  },
  {
    unfold augumenting_path_min_weight,
    simp,
    cases classical.em (0 < rsn.f' b t ∧ ¬rsn.f' b t = 0),
    {
      simp [h_1],
      sorry
    },
    {
      simp [h_1],
      exact ih u v,
    }

    -- simp_rw [rsn.f_def, mk_cf],
    -- cases classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge u v),
    -- {
    --   simp [h_1],
    --   cases classical.em (0 < rsn.f' b t ∧ ¬rsn.f' b t = 0),
    --   {
    --     simp [h_2],

    --   },
    --   {  }
    -- },
    -- {  }
  }
end




lemma superlemma2 {V : Type*} [inst' : fintype V]
  (rsn : residual_network V)
  : (is_max_flow_network rsn.afn) -> no_augumenting_path rsn
:=
begin
sorry
end

section superlemma3

  noncomputable
  def mk_S {V : Type u} [inst' : fintype V]
    (rsn : residual_network V) : finset V :=
    {x | (∃ p : path rsn.is_edge rsn.afn.network.source x, true)}.to_finset

  noncomputable
  def mk_cut_from_S {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (hno_augumenting_path : no_augumenting_path rsn)
    (S : finset V) (hS : S = mk_S rsn) : cut V :=
  ⟨rsn.afn.network, S, V' \ S,
    begin
      rw hS,
      unfold mk_S,
      simp only [set.mem_to_finset, set.mem_set_of_eq],
      exact exists.intro path.nil trivial,
    end,
    begin
      rw hS,
      unfold mk_S,
      simp only [mem_sdiff, mem_univ, set.mem_to_finset, set.mem_set_of_eq, true_and],
      intro p,
      unfold no_augumenting_path at hno_augumenting_path,
      specialize hno_augumenting_path rsn.afn.network.sink ,
      simp only [eq_self_iff_true, not_true] at hno_augumenting_path,
      apply exists.elim p,
      intros p h,
      specialize hno_augumenting_path p,
      exact hno_augumenting_path,
    end,
      rfl⟩

  lemma s_t_not_connected {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (S : finset V) (hS : S = mk_S rsn) :
    ∀ u ∈ S, ∀ v ∈ (V' \ S), ¬ rsn.is_edge u v
    :=
    begin
      intros u h_u_in_S v h_v_in_T is_edge_u_v,
      rw hS at *,
      unfold mk_S at *,
      simp only [set.mem_to_finset, set.mem_set_of_eq, mem_sdiff, mem_univ, true_and] at *,
      apply exists.elim h_u_in_S,
      intros p _,
      have tmp := path.cons p is_edge_u_v,
      apply h_v_in_T,
      exact exists.intro tmp trivial,
    end

  lemma residual_capacity_zero {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (ct : cut V)
    (h_eq_network : rsn.afn.network = ct.network)
    (h: ∀ u ∈ ct.S, ∀ v ∈ ct.T, ¬ rsn.is_edge u v) :
    ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 :=
  begin
    intros u h_u_in_S v h_v_in_T,
    specialize h u h_u_in_S v h_v_in_T,
    rw rsn.is_edge_def at h,
    simp only [not_lt] at h,
    have hge := residual_capacity_non_neg rsn u v,
    exact ge_antisymm hge h,
  end

  lemma min_max_cap_flow {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (ct : cut V)
    (h_eq_network : rsn.afn.network = ct.network)
    (h: ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 ) :
    (∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.afn.f u v = rsn.afn.network.c u v) ∧
    (∀ u ∈ ct.T, ∀ v ∈ ct.S, rsn.afn.f u v = 0) :=
  begin
    split,
    {
      intros u h_u_in_S v h_v_in_T,
      specialize h u h_u_in_S v h_v_in_T,
      rw rsn.f_def at h,
      unfold mk_cf at h,
      have tmp := classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge u v),
      cases tmp,
      {
        simp only [tmp, if_true] at h,
        linarith,
      },
      {
        simp only [tmp, if_false, ite_eq_right_iff] at h,
        have foo := rsn.afn.network.vanishes u v tmp,
        rw foo,
        clear tmp h,
        have foo := rsn.afn.non_neg_flow u v,
        have bar := rsn.afn.no_overflow u v,
        linarith,
      }
    },
    {
      intros v h_v_in_T u h_u_in_S,
      specialize h u h_u_in_S v h_v_in_T,
      rw rsn.f_def at h,
      unfold mk_cf at h,
      have tmp := classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge u v),
      cases tmp,
      {
        have foo := rsn.afn.network.hnonsymmetric u v,
        simp only [not_and] at foo,
        specialize foo tmp,
        have bar := rsn.afn.non_neg_flow v u,
        have baz := rsn.afn.no_overflow v u,
        have blurg := rsn.afn.network.vanishes v u foo,
        linarith,
      },
      {
        simp only [tmp, if_false, ite_eq_right_iff] at h,
        clear tmp,
        have tmp := classical.em (rsn.afn.network.to_capacity.to_strange_digraph.is_edge v u),
        cases tmp,
        {
          exact h tmp,
        },
        {
          have foo := rsn.afn.non_neg_flow v u,
          have bar := rsn.afn.no_overflow v u,
          have baz := rsn.afn.network.vanishes v u tmp,
          linarith,
        },
      },
    }
  end

  lemma f_value_eq_out {V : Type*} [inst' : fintype V]
    (ct : cut V)
    (afn : active_flow_network V)
    (h_eq_network : afn.network = ct.network)
    (h : (∀ u ∈ ct.T, ∀ v ∈ ct.S, afn.f u v = 0)) :
    F_value afn = mk_out afn.f ct.S :=
  begin
    dsimp [F_value],
    rw flow_value_global_ver afn ct h_eq_network,
    dsimp [mk_in],
    simp_rw [← ct.Tcomp],
    simp only [sub_eq_self],
    have sum_eq_sum_zero : ∑ (x : V) in ct.T, ∑ y in ct.S, (afn.f x y) = ∑ x in ct.T, ∑ y in ct.S, 0
    :=
    begin
      apply finset.sum_congr rfl,
      intros x x_in_T,
      apply finset.sum_congr rfl,
      intros y y_in_S,
      exact h x x_in_T y y_in_S,
    end,
    rw sum_eq_sum_zero,
    simp only [sum_const_zero],
  end

  lemma cut_value_eq_out {V : Type*} [inst' : fintype V]
    (ct : cut V)
    (afn : active_flow_network V)
    (h_eq_network : afn.network = ct.network)
    (h : (∀ u ∈ ct.S, ∀ v ∈ V' \ ct.S, afn.f u v = afn.network.c u v) ∧
         (∀ u ∈ V' \ ct.S, ∀ v ∈ ct.S, afn.f u v = 0)) :
        mk_out afn.f ct.S = cut_value ct :=
  begin
    cases h with h_flow_eq_cap h_flow_zero,
    dsimp [cut_value, mk_out],
    apply finset.sum_congr rfl,
    intros x x_in_S,
    rw ← ct.Tcomp at *,
    apply finset.sum_congr rfl,
    intros y y_in_T,
    simp [h_eq_network, h_flow_eq_cap x x_in_S y y_in_T],
  end

  lemma eq_on_res_then_on_sum {V : Type*} [inst' : fintype V]
    (A : finset V) (B : finset V) (f : V → V → ℝ) (g : V → V → ℝ)
    (eq_on_res : ∀ u ∈ A, ∀ v ∈ B, f u v = g u v) :
    ∑ (u : V) in A, ∑ (v : V) in B, f u v = ∑ (u : V) in A, ∑ (v : V) in B, g u v :=
  begin
    apply finset.sum_congr rfl,
    intros a a_in_A,
    apply finset.sum_congr rfl,
    intros b b_in_B,
    exact eq_on_res a a_in_A b b_in_B,
  end

  lemma superlemma3 {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    -- (hno_augumenting_path : ∀ s t : V, path rsn.is_edge s t → ¬(s = rsn.afn.network.source ∧ t = rsn.afn.network.sink))
    (hno_augumenting_path : no_augumenting_path rsn)
    : (∃c : cut V, cut_value c = F_value rsn.afn) :=
  begin
    let S : finset V := mk_S rsn,
    let T := V' \ S,
    have blorg: S = mk_S rsn := by refl,
    let min_cut := mk_cut_from_S (rsn) (hno_augumenting_path) (S) (blorg),

    have subtract: ∀ x y : ℝ, (x=y) ↔ y-x=0 := begin intros x y, split, intro heq, linarith, intro heq, linarith, end,

    have cf_vanishes_on_pipes: ∀u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, rsn.f' u v = 0 := sorry, 
    have cf_vanishes_on_pipes_spec: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, (rsn.afn.network.is_edge u v) → 
        (rsn.afn.network.c u v - rsn.afn.f u v = 0) := 
        begin
          intros u u_in_S v v_in_T is_edge,
          have t: mk_cf rsn.afn u v = rsn.afn.network.c u v - rsn.afn.f u v := begin unfold mk_cf, simp only [is_edge, if_true], end,
          rw ← t,
          have r: mk_cf rsn.afn u v = rsn.f' u v := begin rw rsn.f_def, end,
          rw r,
          exact cf_vanishes_on_pipes u u_in_S v v_in_T,
        end,
    have eq_on_pipes: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, rsn.afn.f u v = rsn.afn.network.c u v := 
      begin 
        intros u u_in_S v v_in_T,
        cases classical.em (rsn.afn.network.is_edge u v),
        { rw subtract (rsn.afn.f u v) (rsn.afn.network.to_capacity.c u v),
          have mk_cf_spec: (rsn.f' u v = rsn.afn.network.c u v - rsn.afn.f u v) 
          := 
            begin
              rw rsn.f_def,
              unfold mk_cf,
              simp only [h, if_true],
            end,
          rw ← mk_cf_spec,
          have h: rsn.f' u v = 0 := 
          begin
            exact cf_vanishes_on_pipes u u_in_S v v_in_T,
          end,
          exact h,
          },
        { 
          rw rsn.afn.network.vanishes u v h,
          exact f_vanishes_outside_edge (rsn.afn) (u) (v) (h),
          
         },
        --have no_edge: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, ¬rsn.is_edge u v := sorry,
        --have f_prim_is_zero: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, rsn.f' u v = 0 := sorry,
        --have connector_full_or_non_existent: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S,  
        --(rsn.afn.network.c u v = rsn.afn.f u v) ∨ (¬rsn.afn.network.is_edge u v)  := sorry, 
      end,
    
    have no_backflow: ∀ u ∈ V' \ min_cut.S, ∀ v ∈ min_cut.S, rsn.afn.f u v = 0 := begin sorry end,
    have no_backflow_func: ∀ u ∈ V' \ min_cut.S, ∀ v ∈ min_cut.S, rsn.afn.f u v = (λ u v, 0) u v := 
      begin  
        simp_rw ← no_backflow,
        exact no_backflow,
      end,

    have eq_net : rsn.afn.network = min_cut.network := by refl,

    have cut_eq_flow: cut_value min_cut = F_value rsn.afn := 
    begin
      rw F_value,
      simp only,
      rw flow_value_global_ver rsn.afn min_cut eq_net,

      have no_input : mk_in rsn.afn.f min_cut.S = 0 := 
        begin
          rw mk_in,
          rw eq_on_res_then_on_sum (V' \ min_cut.S) (min_cut.S) (rsn.afn.f) (λ u v, 0) (no_backflow_func),
          simp only [sum_const_zero],
        end,

      rw no_input,
      simp only [sub_zero],

      have flow_eq_cap_on_cut : mk_out rsn.afn.f min_cut.S = mk_out rsn.afn.network.c min_cut.S := 
        begin
          unfold mk_out,
          rw eq_on_res_then_on_sum (min_cut.S) (V' \ min_cut.S) (rsn.afn.f) (rsn.afn.network.to_capacity.c) (eq_on_pipes),
        end,

      rw flow_eq_cap_on_cut,
      refl,
    end,
      --begin 
        --have blurg : F_value rsn.afn = mk_out rsn.afn.f ted.S := 
        --  begin
        --    have h_eq_network : rsn.afn.network = ted.network := by refl, 
        --    have h_right : ∀ u ∈ ted.T, ∀ v ∈ ted.S, rsn.f' u v = 0 := sorry,

            --have no_backward : ∀ u ∈ ted.T, ∀ v ∈ ted.S, rsn.afn.f u v = 0 := sorry,

            --rw F_value,
            --rw flow_value_global_ver (rsn.afn) (ted) (),
            --exact f_value_eq_out (ted) (rsn.afn) (h_eq_network) (h_right),
          --  sorry
          --end,
        --rw blurg,

        --have blurgon : mk_out rsn.afn.f ted.S = cut_value ted := 
        --  begin
            --have substitute : mk_out rsn.afn.f ted.S = mk_out rsn.afn.network.c S := begin unfold mk_out, sorry end,
            --rw cut_value,
            --rw sub2,
            --unfold mk_out,

            --have flow_eq_cap : ∀ u ∈ ted.S, ∀ v ∈ V' \ ted.S, rsn.afn.f u v = rsn.afn.network.c u v := sorry,
            --have sub2 : (∀ u ∈ ted.S, ∀ v ∈ V' \ ted.S, rsn.afn.f u v = ted.network.to_capacity.c u v) := 
            --begin
            --  have h_eq_network : rsn.afn.network = ted.network := by refl, 
            --  exact min_max_cap_flow (rsn) (ted) (h_eq_network) 
            --  sorry 
            --end,
          
            --exact eq_on_res_then_on_sum (ted.S) (ted.T) (rsn.afn.f) (ted.network.to_capacity.c) (sub2),
        --    sorry
        --  end,
        --rw ← blurgon,
      --end, 
    exact exists.intro min_cut cut_eq_flow,
  end



-- lemma three_way_equiv (a b c : Prop) : (a -> b) -> (b -> c) -> (c -> a) -> ((a <-> b) ∧ (b <-> c) ∧ (c <-> a))
-- :=
-- begin
--   intros hab hbc hca,
--   split,
--   {
--     have foo := hca ∘ hbc,
--     exact ⟨hab, foo⟩,
--   },
--   { split,
--     {
--       exact ⟨hbc, hab ∘ hca⟩
--     },
--     exact ⟨hca, hbc ∘ hab ⟩,
--   }
-- end
end superlemma3

theorem maxflow_mincut {V : Type*} [inst' : fintype V]
  (rsn : residual_network V) :
  (is_max_flow_network rsn.afn -> no_augumenting_path rsn) ∧
  (no_augumenting_path rsn -> (∃c : cut V, cut_value c = F_value rsn.afn)) ∧
  ((∃c : cut V, cut_value c = F_value rsn.afn ∧ c.network = rsn.afn.network) -> is_max_flow_network rsn.afn)
:=
begin
split,
{
  exact superlemma2 rsn,
},
{
  split,
  { exact superlemma3 rsn },
  {
    intro c,
    cases c with c heq,
    cases heq with heq heq_network,
    have foo := superlemma_1 rsn.afn c heq_network.symm heq,
    exact foo,
  }
} 
end
