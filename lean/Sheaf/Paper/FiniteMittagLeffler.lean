/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Sheaf.CategoryTheory.Triangulated.MilnorSequence
public import Sheaf.Paper.PbcRoosTriangle
public import Sheaf.Paper.SequentialDerivedInverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Mittag--Leffler vanishing for finite abelian groups

Source: blueprint sec-deligne-laumon-a1/sk-l-dl-a1-endpoints, order 2731;
Stacks Project, Tags 07KW and 07KY (blueprint: lem-weil-pbc-mittag-leffler).
The natural index n denotes positive level n+1. Canonical maps in D(Ab) are specified
by their limit-projection equations, exactly as in `milnor_shortExact`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The first right derived inverse limit with the recorded canonical instance parameters.
This abbreviates the existing right derived functor; it does not replace it by a cokernel.
Source: Stacks Tag 07KW (blueprint: lem-weil-pbc-mittag-leffler). -/
abbrev firstDerivedLimitAb (B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : AddCommGrpCat.{u} :=
  letI := roosTowerEnoughInjectives
  letI := roosLimitAdditive
  ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj B

/-- Finite abelian groups form an ML tower and its first derived inverse limit vanishes.
Source: Stacks Tags 02N0, 0597 and 07KW (blueprint: lem-weil-pbc-mittag-leffler).
Proof: for a fixed level the descending images are subgroups of a finite group.
Choose an image of minimum cardinality; all later images equal it. For any tuple y,
the finite nonempty sets of prefix solutions x_j-f_j(x_(j+1))=y_j form an ML tower:
choose the last x to be zero and solve backwards; descending finite images stabilize.
By Mathlib's finite cofiltered-system theorem there is a compatible family of prefixes,
hence a full solution. Thus roosMap is surjective. The cokernel description in
lem-pc-derived-limit-roos-abelian-groups identifies R¹ lim with zero. -/
theorem finiteTower_mittagLeffler_vanishing (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n)) :
    (A ⋙ forget AddCommGrpCat).IsMittagLeffler ∧
      IsZero (firstDerivedLimitAb A) := by
  classical
  let (n : ℕᵒᵖ) : Finite (A.obj n) := hA n
  refine ⟨?_, ?_⟩
  · exact (A ⋙ forget AddCommGrpCat).isMittagLeffler_of_exists_finite_range
      (fun n ↦ ⟨n, 𝟙 n, by
        have : Finite ((A ⋙ forget AddCommGrpCat).obj n) := hA n
        exact Set.toFinite _⟩)
  · have hsurj : Function.Surjective (roosMap A) := by
      intro y
      let Y (n : ℕ) := Pi.π (fun n : ℕ ↦ A.obj (op n)) n y
      let f (n : ℕ) := A.map (homOfLE (Nat.le_succ n)).op
      let E (n : ℕ) := {x : ∀ j : Fin (n + 1), A.obj (op j.val) //
        ∀ j : Fin n, x ⟨j.val, by omega⟩ -
          f j.val (x ⟨j.val + 1, by omega⟩) = Y j.val}
      let r (n : ℕ) : E (n + 1) → E n := fun x ↦
        ⟨fun j ↦ x.val ⟨j.val, by omega⟩,
          fun j ↦ x.prop ⟨j.val, by omega⟩⟩
      let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (fun n ↦ ↾(r n))
      have hnonempty (n : ℕ) : Nonempty (E n) := by
        let x : ∀ j : Fin (n + 1), A.obj (op j.val) :=
          Fin.reverseInduction 0 (fun j z ↦ Y j.val + f j.val z)
        refine ⟨⟨x, fun j ↦ ?_⟩⟩
        have h := @Fin.reverseInduction_castSucc n
          (fun j ↦ A.obj (op j.val)) 0 (fun j z ↦ Y j.val + f j.val z) j
        simp only [Fin.val_castSucc, Fin.val_succ] at h
        change x ⟨j.val, _⟩ = Y j.val + f j.val (x ⟨j.val + 1, _⟩) at h
        rw [h]
        exact add_sub_cancel_right _ _
      have : ∀ n : ℕᵒᵖ, Nonempty (F.obj n) := fun n ↦ hnonempty n.unop
      have : ∀ n : ℕᵒᵖ, Finite (F.obj n) := fun n ↦ by
        change Finite (E n.unop)
        dsimp only [E]
        infer_instance
      obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
      let x (n : ℕ) := (s (op n)).val ⟨n, Nat.lt_succ_self n⟩
      have hx (n : ℕ) : x n - f n (x (n + 1)) = Y n := by
        have he := congrArg (fun z : E n ↦ z.val ⟨n, Nat.lt_succ_self n⟩)
          (hs (homOfLE (Nat.le_succ n)).op)
        simp only [F, Functor.ofOpSequence_map_homOfLE_succ] at he
        change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ = x n at he
        have heq := (s (op (n + 1))).prop ⟨n, Nat.lt_succ_self n⟩
        change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ -
          f n (x (n + 1)) = Y n at heq
        rwa [he] at heq
      refine ⟨(Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x, ?_⟩
      apply (Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).injective
      funext n
      simp only [Concrete.productEquiv_apply_apply]
      change ((roosMap A ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n)
        ((Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x)) = _
      simpa [roosMap, towerTransitionEndomorphism, towerProductShift, Y, f] using hx n
    have : Epi (roosMap A) := (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
    obtain ⟨_, e₁, _⟩ := derivedLimitRoosAbelianGroups.{u}.2
    exact (isZero_cokernel_of_epi (roosMap A)).of_iso (e₁ A)

/-- Finiteness one degree earlier makes the canonical Milnor projection invertible.
Source: Stacks Tag 07KY (blueprint: lem-weil-pbc-mittag-leffler).
Proof: apply finiteTower_mittagLeffler_vanishing to H^(i-1)(K_n). In the short exact
sequence of lem-pc-derived-limit-milnor-sequence the first term is zero. Thus its
right arrow is mono and epi, hence an isomorphism. The equations hπ identify b with
that canonical right arrow, since the limit projections jointly determine a map. -/
theorem milnorMap_isIso_of_finite [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (i : ℤ)
    (hfinite : ∀ n : ℕᵒᵖ,
      Finite ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)).obj (K.obj n)))
    (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
      limit (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (op n) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj (op n)) n)) : IsIso b := by
  obtain ⟨a, b', h, _⟩ := milnor_shortExact.{u, v} i
  obtain ⟨⟨hz, hS⟩, hb'⟩ := h K L p δ hT
  have heq : b = b' K L p δ := by
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    exact (hπ n).trans (hb' n).symm
  rw [heq]
  exact hS.isIso_g_iff.mpr
    (finiteTower_mittagLeffler_vanishing
      (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)) hfinite).2

/-- For finite groups in degree zero the Milnor projection is invertible in every degree.
Source: Stacks Tag 07KY (blueprint: lem-weil-pbc-mittag-leffler).
Proof: the cohomology in degree i-1 of each single-degree object is either the finite
group itself or zero. Apply milnorMap_isIso_of_finite in each integer degree. -/
theorem milnorMap_single_isIso_of_finite [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n))
    [HasProduct (fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n)))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n)))
    (δ : (∏ᶜ fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n ↦ (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).map
        (A.map (homOfLE (Nat.le_succ n)).op)) L p δ)
    (i : ℤ)
    (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
      limit (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0 ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0 ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (op n) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (p ≫ Pi.π (fun n : ℕ ↦
          (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n))) n)) :
    IsIso b := by
  have : HasProduct (fun n : ℕ ↦
      (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (op n)) :=
    inferInstanceAs (HasProduct (fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n))))
  apply milnorMap_isIso_of_finite
    (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0) L p δ hT i ?_ b hπ
  intro n
  change Finite ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)).obj
    ((DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj n)))
  have := hA n
  by_cases hi : i - 1 = 0
  · rw [hi]
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      AddCommGrpCat.{u} 0).app (A.obj n)
    have : Finite ((𝟭 AddCommGrpCat.{u}).obj (A.obj n)) := hA n
    exact Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).injective
  · have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)).obj
        ((DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj n))) := by
      rcases lt_or_gt_of_ne hi with h | h
      · exact (DerivedCategory.isGE_iff _ 0).mp inferInstance (i - 1) h
      · exact (DerivedCategory.isLE_iff _ 0).mp inferInstance (i - 1) h
    have := AddCommGrpCat.subsingleton_of_isZero hz
    infer_instance

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Finiteness in degree i-1 makes the evaluated pro-etale Milnor map invertible.
Source: blueprint order 2731; Stacks Tags 07KW and 07KY
(blueprint: lem-weil-pbc-mittag-leffler).
Proof: exact evaluation yields the tower of finite groups H^(i-1)(U,M_n).
Apply finiteTower_mittagLeffler_vanishing to annihilate its first derived limit.
The evaluated exact sequence of prop-weil-pbc-roos-triangle then has zero left term,
so its right arrow is mono and epi. Its projection equations identify it with b,
since the limit projections jointly determine a map. For the supplied Roos triangle,
complete the identity square on the two product objects to a morphism into the
canonical triangle. Its remaining component g is invertible because the other two
components are identities. The first square and the projection equations identify b
with evaluated cohomology of g followed by the canonical Milnor map. Both factors
are invertible. Weak contractibility makes sections exact, so this cohomology
presheaf computes hypercohomology, also for unbounded towers. -/
theorem completedMilnorMap_isIso_of_finite
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (L : DerivedCategory (Scheme.CompletedAdicModules T d))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n)) ⟶
      L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).map
        (homOfLE (Nat.le_succ n)).op) L p δ)
    (U : (pbcMilnorTests T).FullSubcategory) (i : ℤ)
    (hfinite : ∀ n : ℕᵒᵖ, Finite
      ((((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U)).obj n))
    (b : ((pbcCohomologyPresheaf T d i).obj L).obj (op U) ⟶
      limit (((pbcCohomologyTowers T d i).obj M).obj (op U)))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (((pbcCohomologyTowers T d i).obj M).obj (op U)) (op n) =
      ((pbcCohomologyPresheaf T d i).map
        (p ≫ Pi.π (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n)) n)).app
          (op U)) : IsIso b := by
  obtain ⟨RF, p', δ', hT', hseq⟩ := pbcRoosTriangle T d
  obtain ⟨a', b', hseq⟩ := hseq i
  obtain ⟨⟨hz, hS⟩, _, hb'⟩ := hseq M U
  have hbiso : IsIso ((b'.app M).app (op U)) :=
    hS.isIso_g_iff.mpr (finiteTower_mittagLeffler_vanishing
      (((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U)) hfinite).2
  let f := fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).map
    (homOfLE (Nat.le_succ n)).op
  let C := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ
  let C' := Pretriangulated.Triangle.mk (p'.app M)
    (towerTransitionEndomorphism f) (δ'.app M)
  obtain ⟨g, hp, hδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    C C' hT (hT' M) (𝟙 _) (𝟙 _) (by simp [C, C'])
  let φ : C ⟶ C' :=
    { hom₁ := g
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := hp
      comm₂ := by simp [C, C']
      comm₃ := hδ }
  have hg : IsIso g :=
    Pretriangulated.isIso₁_of_isIso₂₃ φ hT (hT' M) inferInstance inferInstance
  have hcomp : b = ((pbcCohomologyPresheaf T d i).map g).app (op U) ≫
      (b'.app M).app (op U) := by
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    rw [Category.assoc, hb', hπ]
    rw [← NatTrans.comp_app, ← Functor.map_comp]
    have hp' : p = g ≫ p'.app M := by simpa [C, C'] using hp
    simp only [hp', Category.assoc]
    rfl
  rw [hcomp]
  infer_instance

end AlgebraicGeometry.ProEtale
