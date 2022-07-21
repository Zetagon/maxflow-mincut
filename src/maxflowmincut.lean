import data.real.basic
import data.set
import tactic
import data.finset
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

structure strange_digraph (V : Type*)  :=
  (is_edge : V → V → Prop)
  (hnonsymmetric : ∀ u v : V, ¬ ((is_edge u v) ∧ (is_edge v u)))

infixr ` ⇉ `:10 := strange_digraph.is_edge -- type as \h


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
                  v ∈ (finset.univ : finset V) \ {network.source, network.sink} →
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

end definitions

lemma x_not_in_s {V : Type*} [fintype V]
  (c : cut V)  : ∀ x : V, x ∈ c.T -> x ∉ ({c.network.source} : finset V) :=
begin
  intros x hxinS,
  cases c,
  simp at *,
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

notation ` V' ` := univ

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
  simp,
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
  simp,
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
         simp,
         rw ← ct.Tcomp,
         simp,
         have b : V' \ T = S :=
         begin
           rw [hT, ct.Tcomp],
           simp,
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
  intro p,
  exact h_2(h_1(p)),
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

inductive path {V : Type* } (is_edge : V -> V -> Prop) (a : V) : V → Prop
| nil  : path a
| cons : Π {b c : V}, path b → (is_edge b c) → path c

-- @[instance] def foobarbaz {V : Type*} [inst : quiver.{0} V] [inst' : fintype V] [inst'' : has_singleton V (quiver (resnet V))]
--   (afn : active_flow_network V)
--   : quiver (resnet V) :=
-- { hom =  λ u  v, mk_cf afn u v > 0 }




-- noncomputable
-- def mk_residual_network {V : Type*} [inst : quiver.{0} V] [inst' : fintype V]
--   (afn : active_flow_network V)
--   : residual_network V
--   := ⟨mk_cf afn, afn.network.source, afn.network.sink⟩
def no_augumenting_path {V : Type*} [inst' : fintype V]
  (rsn : residual_network V) : Prop
  := ∀ t : V, path rsn.is_edge rsn.afn.network.source t → ¬( t = rsn.afn.network.sink)


lemma superlemma2 {V : Type*} [inst' : fintype V]
  (rsn : residual_network V)
  : (is_max_flow_network rsn.afn) -> no_augumenting_path rsn
:=
begin
sorry
end

section superlemma3

  noncomputable
  def mk_S {V : Type*} [inst' : fintype V]
    (rsn : residual_network V) : finset V :=
    {x | path rsn.is_edge rsn.afn.network.source x}.to_finset

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
      exact path.nil,
    end,
    begin
      rw hS,
      unfold mk_S,
      simp only [mem_sdiff, mem_univ, set.mem_to_finset, set.mem_set_of_eq, true_and],
      intro p,
      unfold no_augumenting_path at hno_augumenting_path,
      have tmp := hno_augumenting_path rsn.afn.network.sink p,
      simp only [eq_self_iff_true, not_true] at tmp,
      exact tmp,
    end,
      rfl⟩

  lemma s_t_not_connected {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (S : finset V) (hS : S = mk_S rsn) :
    ∀ u ∈ S, ∀ v ∈ (V' \ S), ¬ rsn.is_edge u v
    := sorry

  lemma residual_capacity_zero {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (ct : cut V)
    (h_eq_network : rsn.afn.network = ct.network)
    (h: ∀ u ∈ ct.S, ∀ v ∈ (V' \ ct.S), ¬ rsn.is_edge u v) :
    ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 :=
    sorry

  lemma min_max_cap_flow {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    (ct : cut V)
    (h_eq_network : rsn.afn.network = ct.network)
    (h: ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 ) :
    (∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.afn.f u v = rsn.afn.network.c u v) ∧
    (∀ u ∈ ct.T, ∀ v ∈ ct.S, rsn.afn.f u v = 0) := sorry

  lemma f_value_eq_out {V : Type*} [inst' : fintype V]
    (ct : cut V)
    (afn : active_flow_network V)
    (h_eq_network : afn.network = ct.network)
    (h : (∀ u ∈ ct.T, ∀ v ∈ ct.S, afn.f u v = 0)) :
    F_value afn = mk_out afn.f ct.S := sorry

  lemma cut_value_eq_out {V : Type*} [inst' : fintype V]
    (ct : cut V)
    (afn : active_flow_network V)
    (h_eq_network : afn.network = ct.network)
    (h : (∀ u ∈ ct.S, ∀ v ∈ ct.T, afn.f u v = afn.network.c u v) ∧
         (∀ u ∈ ct.T, ∀ v ∈ ct.S, afn.f u v = 0)) :
        mk_out afn.f ct.S = cut_value ct := sorry

  lemma superlemma3 {V : Type*} [inst' : fintype V]
    (rsn : residual_network V)
    -- (hno_augumenting_path : ∀ s t : V, path rsn.is_edge s t → ¬(s = rsn.afn.network.source ∧ t = rsn.afn.network.sink))
    (hno_augumenting_path : no_augumenting_path rsn)
    : (∃c : cut V, cut_value c = F_value rsn.afn) :=
  begin
    let S : finset V := mk_S rsn,
    let T := V' \ S,
    have blorg: S = mk_S rsn := 
      begin 
        refl, 
      end,
    let ted := mk_cut_from_S (rsn) (S) (blorg),
    have bob: cut_value ted = F_value rsn.afn := 
      begin 
        have blurg : F_value rsn.afn = mk_out rsn.afn.f ted.S := 
          begin
            have h_eq_network : rsn.afn.network = ted.network := sorry, 
            have h_right : ∀ u ∈ ted.T, ∀ v ∈ ted.S, rsn.afn.f u v = 0 := sorry,
            exact f_value_eq_out (ted) (rsn.afn) (h_eq_network) (h_right),
          end,
        rw blurg,

        have blurgon : mk_out rsn.afn.f ted.S = cut_value ted := 
          begin
            have substitute : mk_out rsn.afn.f ted.S = mk_out rsn.afn.network.c S := sorry,
            rw cut_value,
            have sub2 : ted.network.to_capacity.c = rsn.afn.f := sorry,
            rw sub2,
          end,
        rw ← blurgon,
      end, 
    exact exists.intro ted bob,
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
    exact foo.left,
  }
}

end
