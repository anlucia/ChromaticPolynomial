import «ChromaticPolynomial».SpanningSubgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Set
import Mathlib

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] (G : SimpleGraph V)

open Classical

/-- Number of connected components of the spanning subraph defined by F ⊆ G.edgeSet -/
noncomputable
def edge_subset_ConnectedComponent_card (F :  {F // F ⊆ G.edgeSet}) :=
  Fintype.card ((G.spanningSubgraph_fromEdgeSet' F).coe).ConnectedComponent

variable (R: Type*) [CommRing R] [CharZero R] [NoZeroDivisors R]

/-- The chromatic polynomial of a graph G -/
@[simp]
noncomputable
def ChromaticPolynomial : Polynomial R :=
  ∑ F : {F // F ⊆ G.edgeSet}, (-1)^(Fintype.card F) *
  Polynomial.X^(G.edge_subset_ConnectedComponent_card F)

/- We will consider α-colorings of G -/
variable (α : Type*) [Fintype α]

/-- An assignment π : V → α is a proper coloring if it assigns different values to adjacent vertices -/
def is_proper (π : V → α) := (∀ {v w : V}, G.Adj v w → π v ≠ π w)

/-- Homomorphisms G →g ⊤ are equivalent to functions π : V → α  which are proper coloring -/
def coloring_equiv_coloring' : G.Coloring α ≃ {π : V → α // G.is_proper α π } where
  toFun C := ⟨C.toFun, C.valid⟩
  invFun π := Coloring.mk ↑(π) π.prop
  left_inv C := rfl
  right_inv π := by {simp; rfl}

variable (e : Sym2 V)

/-- For a (non necessarily valid) coloring π, indicator_constant is a function from the set of edges
  to the ring R, which has value 1 is the edge is colored properly (i.e., if the endpoints
  of the edge have different colors), and 0 otherwise. -/
noncomputable
def indicator_nonconstant (π : V → α) :=
  Sym2.lift ⟨fun v w => ite (π v ≠ π w) (1:R) 0, by {intros; simp_rw [ne_comm]}⟩

lemma indicator_nonconstant_eq_one_or_zero (π : V → α) :
  indicator_nonconstant R α π e = 1 ∨ indicator_nonconstant R α π e = 0 := by
    obtain ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    simp [indicator_nonconstant, ← hvw]
    exact ne_or_eq (π v) (π w)

/- The opposite function to indicator_noncostant -/
noncomputable
def indicator_constant (π : V → α) :=
  Sym2.lift ⟨fun v w => ite (π v = π w) (1:R) 0, by {intros; simp_rw [eq_comm]}⟩

lemma indicator_nonconstant_eq_one_minus_indicator_constant (π : V → α) :
  indicator_nonconstant R α π e = (1 - indicator_constant R α π) e := by
    obtain ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    simp
    simp [indicator_constant, indicator_nonconstant]
    rw [← hvw]
    simp [Sym2.lift_mk]
    split
    next h => simp_all only [sub_self]
    next h => simp_all only [sub_zero]

lemma indicator_constant_eq_one_or_zero (π : V → α) :
  indicator_constant R α π e = 1 ∨ indicator_constant R α π e = 0 := by
    obtain ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    simp [indicator_constant, ← hvw]
    exact eq_or_ne (π v) (π w)

/-- An assignment of colors to vertices π is a proper coloring if and only if the indicator_nonconstant function
  takes value 1 on each edge, or in other words, if and only if its product over the edges is equal to 1. -/
@[simp]
noncomputable
def indicator_proper (π : V → α) :=
  ∏ (e ∈ G.edgeSet), (indicator_nonconstant R α π e)

lemma indicator_proper_eq_one_or_zero (π : V → α) :
  G.indicator_proper R α π = 1 ∨ G.indicator_proper R α π = 0 := by
    by_cases h : ∃ e ∈ G.edgeSet, indicator_nonconstant R α π e = 0
    right
    obtain ⟨e₀, ⟨he₀, idxe₀⟩⟩ := h
    simp
    calc ∏ e ∈ G.edgeSet.toFinset, indicator_nonconstant R α π e =
      indicator_nonconstant R α π e₀ *  ∏ e ∈ G.edgeSet.toFinset \ {e₀}, indicator_nonconstant R α π e := by
          refine Finset.prod_eq_mul_prod_diff_singleton ?h (indicator_nonconstant R α π)
          exact mem_edgeFinset.mpr he₀
      _ = 0 := by
          rw [idxe₀]
          simp
    left
    apply Finset.prod_eq_one
    intro e he
    let e₁ : G.edgeSet := ⟨e, Set.mem_toFinset.mp he⟩
    apply (Or.resolve_right (indicator_nonconstant_eq_one_or_zero R α e₁ π))
    simp at h
    apply h
    exact mem_edgeFinset.mp he

lemma indicator_proper_eq_one_iff_proper (π : V → α) :
  (G.indicator_proper R α π) = 1 ↔ G.is_proper α π := by
    constructor
    · intro h v w hedge
      contrapose h
      let e₀ := s(v, w)
      let f := indicator_nonconstant R α π
      have h₁ : f e₀ = 0 := by
        simp only [f, e₀, h, indicator_nonconstant, Sym2.lift_mk]
        exact rfl
      simp
      apply Ne.symm
      calc 1 ≠ 0 := one_ne_zero
      _ = indicator_nonconstant R α π e₀ * ∏ e ∈ G.edgeSet.toFinset \ {e₀}, indicator_nonconstant R α π e := by
        simp_all only [zero_mul, f, e₀]
      _ = ∏ e ∈ G.edgeSet.toFinset, indicator_nonconstant R α π e := by
          refine Eq.symm (Finset.prod_eq_mul_prod_diff_singleton ?h (indicator_nonconstant R α π))
          exact mem_edgeFinset.mpr hedge
    · intro h
      simp
      rw [Finset.prod_eq_one]
      intro e he
      simp [Set.mem_toFinset] at he
      obtain ⟨⟨v, w⟩, hsw⟩ := e.exists_rep
      simp [indicator_nonconstant]
      rw [← hsw]
      simp [Sym2.lift_mk]
      subst hsw
      exact h he

variable (H : G.Subgraph) (π : {π : V → α // ∀ {v w : V}, H.Adj v w → π v = π w })
#check ConnectedComponent.lift π.val ?h

def equiv_constant_on_cc (H : G.Subgraph) :
  {π : V → α // ∀ {v w : V}, H.Adj v w → π v = π w } ≃ (H.coe.ConnectedComponent → α) := where
  toFun π := Quot.lift_mk π.val
  invFun P :=
  left_inv := sorry
  right_inv := sorry

open Finset

lemma indicator_constant_connected_components (F :  {F // F ⊆ G.edgeSet}) : ∑ (π : V → α), ∏ (e ∈ F.val), (indicator_constant R α π e) =
  (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
    let H := (G.spanningSubgraph_fromEdgeSet' F)
    have h' : H.edgeSet = ↑F := by
                simp [H]
                change (fromEdgeSet F).edgeSet = F.val
                rw [edgeSet_fromEdgeSet, ← powerset_edgeSet_eq_diff_setOf_isDiag]
    calc ∑ π : V → α, ∏ (e ∈ F.val), indicator_constant R α π e =
      ∑ π : V → α, ite (∀ e ∈ F.val, indicator_constant R α π e = 1) 1 0 := by
          apply sum_congr rfl; intro π _
          by_cases h : ∀ e ∈ F.val, indicator_constant R α π e = 1
          · simp_all [prod_eq_one]
          · apply eq_ite_iff.mpr
            right
            constructor
            · exact h
            · apply prod_eq_zero_iff.mpr
              simp at h
              obtain ⟨e, he, hzero⟩ := h
              use e
              constructor
              simp [he]
              exact Or.resolve_left (indicator_constant_eq_one_or_zero R α e π) hzero
      _ = ∑ π : V → α, ite (∀ {v w : V}, H.Adj v w → π v = π w) 1 0 := by
          apply sum_congr rfl; intro π _
          apply ite_congr
          · rw [eq_iff_iff]
            apply Iff.intro
            · intro hone
              intro v w hvw
              simp [Sym2.forall, indicator_constant] at hone
              apply hone
              rw [← H.mem_edgeSet] at hvw
              rw [← h']
              exact hvw
            · intro hallvw
              intro e he
              simp [indicator_constant]
              obtain ⟨⟨v, w⟩, hsw⟩ := e.exists_rep
              rw [← hsw]
              simp [Sym2.lift_mk]
              apply hallvw
              rw [← H.mem_edgeSet, h']
              exact Set.mem_of_eq_of_mem hsw he
          repeat' exact fun _ ↦ rfl
      _ = Fintype.card {π : V → α //  ∀ {v w : V}, H.Adj v w → π v = π w} := by
          rw [sum_ite, sum_const_zero, add_zero, sum_const]
          simp
          symm
          apply Fintype.card_subtype
      _ = Fintype.card (H.coe.ConnectedComponent → α) := by
          apply Nat.cast_inj.mpr
          apply Fintype.card_congr
          apply equiv_constant_on_cc
      _ = (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
          simp
          exact rfl

/-- The chromatic polynomial of a graph G evaluated at a integer n is the number of proper
  colorings of the graph with n colors. -/
lemma ChromaticPolynomial_eval (α : Type*) [Fintype α] :
  (G.ChromaticPolynomial R).eval (Fintype.card α : R) = Fintype.card (G.Coloring α) := by
  symm
  let proper := {π : V → α | G.is_proper α π}.toFinset
  let edges :=  G.edgeSet.toFinset
  calc ↑(Fintype.card (G.Coloring α)) = ∑ (_ : (G.Coloring α)), (1:R) := by
         simp [sum_const, card_univ]
    _ = ∑ (_ ∈ proper), (1:R) := by
        simp
        rw [Set.toFinset_card]
        apply Fintype.card_congr (G.coloring_equiv_coloring' α)
    _ = ∑ (π ∈ proper), (G.indicator_proper R α π) := by
        apply sum_congr rfl
        rintro π hproper
        symm
        apply (G.indicator_proper_eq_one_iff_proper R α π).mpr
        exact Set.mem_toFinset.mp hproper
    _ = ∑ (π ∈ proper), (G.indicator_proper R α π) + ∑ (π ∈ properᶜ), (G.indicator_proper R α π) := by
        rw [self_eq_add_right]
        apply sum_eq_zero
        intro π hnotproper
        rw [← Set.toFinset_compl] at hnotproper
        simp [coe_compl] at hnotproper
        rw [← (G.indicator_proper_eq_one_iff_proper R α π)] at hnotproper
        exact Or.resolve_left (G.indicator_proper_eq_one_or_zero R α π) hnotproper
    _ = ∑ (π : V → α), (G.indicator_proper R α π) := by
        exact sum_add_sum_compl proper (G.indicator_proper R α)
    _ = ∑ (π : V → α), ∏ (e ∈ edges), (1 - indicator_constant R α π e) := by
        simp only [indicator_proper]
        apply sum_congr rfl
        intro π _
        apply prod_congr rfl
        intro e he
        rw [Set.mem_toFinset] at he
        apply indicator_nonconstant_eq_one_minus_indicator_constant R α
    _ = ∑ (π : V → α), ∑ (F ∈ G.edgeSet.toFinset.powerset), ∏ (e ∈ F), (-(indicator_constant R α π e)) := by
        simp_rw [sub_eq_add_neg, add_comm (1 : R), Finset.prod_add, Finset.prod_const_one, mul_one]
    _ = ∑ (F ∈ G.edgeSet.toFinset.powerset), ∑ (π : V → α), ∏ (e ∈ F), (-(indicator_constant R α π e)) := by
        exact Finset.sum_comm
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-(indicator_constant R α π e)) := by
        apply Finset.sum_bij'
          (fun F (hF: F ∈ G.edgeSet.toFinset.powerset) ↦ ⟨F.toSet, by {aesop}⟩)
          (fun F _ ↦ F.val.toFinset)
        repeat' simp
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-(indicator_constant R α π e)) := by
        apply sum_congr rfl
        simp
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), ∏ (e ∈ F.val), (-1*(indicator_constant R α π e)) := by
        simp_all only [neg_mul, one_mul]
    _ = ∑ F : {F // F ⊆ G.edgeSet}, ∑ (π : V → α), (-1)^(Fintype.card F) * ∏ (e ∈ F.val), indicator_constant R α π e := by
        simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Set.toFinset_card]
    _ = ∑ F : {F // F ⊆ G.edgeSet},  (-1)^(Fintype.card F) * ∑ (π : V → α), ∏ (e ∈ F.val), indicator_constant R α π e := by
        apply sum_congr rfl; intro F _
        simp [mul_sum]
    _ = ∑ F : {F // F ⊆ G.edgeSet},
      (-1)^(Fintype.card F) * (↑(Fintype.card α))^(G.edge_subset_ConnectedComponent_card F) := by
        apply sum_congr rfl; intro F _
        simp [G.indicator_constant_connected_components R α]
    _ = Polynomial.eval (↑(Fintype.card α)) (G.ChromaticPolynomial R) := by
        dsimp
        rw [Polynomial.eval_finset_sum]
        apply sum_congr rfl; intro F _
        simp

end SimpleGraph
