/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.OpenClosed.Derived
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Counit identification of a scalar support-triangle comparison

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Existence and Locality;
Stacks Project, Tags 07A6, 0149, 014A, 04CA, 08M3, 010N and 05RT
(blueprint: lem-pur-supported-triangle-mate-identification).

## Main definitions and statement

- `scalarSupportTriangle`: the prescribed counit/unit triangle with explicit boundary.
- `scalarSupportOpenProjection`: the canonical open coefficient projection.
- `scalarSupportClosedMate`: the counit-defined exceptional transpose.
- `scalarSupportTriangle_mate_identification`: identification and isomorphism criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The shift structure on scalar extension induced by its adjunction to exact restriction.
Source: Stacks 07A6; Mathlib's unique adjunction-compatible shift structure
(blueprint: lem-pur-supported-triangle-mate-identification). -/
instance scalarSupportExtensionCommShift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : Scheme.{u}) : (scalarExtension φ P).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ)).leftAdjointCommShift ℤ

/-- A support triangle with its prescribed counit, open unit, and an explicit boundary.
The distinguishedness of the boundary is supplied separately, as in
exists_etale_closedSupportTriangle; no new choice of support functor is made.
Source: blueprint Existence and Locality; Stacks 07A6 and 0149
(blueprint: lem-pur-supported-triangle-mate-identification). -/
def scalarSupportTriangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) (K : DerivedCategoryModule A P)
    (δ : (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        (D(upperStar (ModuleCat.{u + 1} A) j).obj K) ⟶
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategoryModule A P) :=
  Triangle.mk
    ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app K) δ

/-- The canonical open coefficient projection, including the scalar/pullback identification.
The outer geometric comparison converts the existing L(j*) interface to exact D(j*).
Source: blueprint Locality; Stacks 07A4 and 07A6
(blueprint: lem-pur-supported-triangle-mate-identification). -/
def scalarSupportOpenProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {P U : Scheme.{u}} (j : U ⟶ P)
    (K : DerivedCategoryModule A P) :
    (scalarExtension φ P).obj
        (R(lowerStar (ModuleCat.{u + 1} A) j).obj
          (D(upperStar (ModuleCat.{u + 1} A) j).obj K)) ⟶
      R(lowerStar (ModuleCat.{u + 1} B) j).obj
        (D(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj K)) :=
  (scalarMate φ j).app (D(upperStar (ModuleCat.{u + 1} A) j).obj K) ≫
    R(lowerStar (ModuleCat.{u + 1} B) j).map
      ((scalarExtension φ U).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).inv.app K) ≫
        (scalarPullbackIso φ j).inv.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
          ((scalarExtension φ P).obj K))

/-- The exceptional coefficient comparison is the transpose of the extended counit
precomposed with the inverse of the canonical closed coefficient projection.
Source: blueprint Existence; Stacks 07A6
(blueprint: lem-pur-supported-triangle-mate-identification). -/
def scalarSupportClosedMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (K : DerivedCategoryModule A P)
    [IsIso ((scalarMate φ i).app
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))] :
    (scalarExtension φ Z).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
        ((scalarExtension φ P).obj K) :=
  (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} B) i))).homEquiv _ _
    (inv ((scalarMate φ i).app
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ≫
      (scalarExtension φ P).map
        ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K))

-- Abstract the chosen derived functors during diagram elaboration.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

private theorem scalarExtension_additive
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : Scheme.{u}) : (scalarExtension φ P).Additive :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ)).left_adjoint_additive

private theorem scalarExtension_triangulated
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : Scheme.{u}) : (scalarExtension φ P).IsTriangulated := by
  let adj : scalarExtension φ P ⊣
      Sheaf.derivedRestrictScalars P.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  exact adj.isTriangulated_leftAdjoint

private theorem restriction_reflects_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : Scheme.{u})
    {X Y : DerivedCategoryModule B P} (f : X ⟶ Y)
    [IsIso ((Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map f)] : IsIso f := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((Sheaf.restrictScalars P.smallEtaleTopology φ).map
      ((_root_.DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars P.smallEtaleTopology φ).mapDerivedCategoryHomologyFunctorIso n)
      f).2 (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars P.smallEtaleTopology φ)

private theorem scalar_open_zero
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {P U : Scheme.{u}} (j : U ⟶ P)
    (X : DerivedCategoryModule A P)
    (hX : IsZero (L(upperStar (ModuleCat.{u + 1} A) j).obj X)) :
    IsZero (L(upperStar (ModuleCat.{u + 1} B) j).obj
      ((scalarExtension φ P).obj X)) := by
  have := scalarExtension_additive φ U
  exact ((scalarExtension φ U).map_isZero hX).of_iso ((scalarPullbackIso φ j).app X)

private theorem supported_open_orthogonal
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z P U : Scheme.{u}} (i : Z ⟶ P) (j : U ⟶ P)
    [IsOpenImmersion j] (hij : Disjoint (Set.range j.base) (Set.range i.base))
    (M : DerivedCategoryModule A Z) (N : DerivedCategoryModule B U) :
    Subsingleton
      ((((Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj (R(lowerStar (ModuleCat.{u + 1} A) i).obj M)))
          ⟦(1 : ℤ)⟧) ⟶
        (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
          (R(lowerStar (ModuleCat.{u + 1} B) j).obj N)) := by
  let S := (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
    ((scalarExtension φ P).obj (R(lowerStar (ModuleCat.{u + 1} A) i).obj M))
  have hz : IsZero (L(upperStar (ModuleCat.{u + 1} A) j).obj
      (R(lowerStar (ModuleCat.{u + 1} A) i).obj M)) :=
    (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
      (ModuleCat.{u + 1} A) j i hij M).of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).app _)
  have hzB := scalar_open_zero φ j _ hz
  have hzS : IsZero (L(upperStar (ModuleCat.{u + 1} A) j).obj S) :=
    ((Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).map_isZero hzB).of_iso
      ((scalarRestrictionPullbackIso φ j).app _)
  have hzShift : IsZero (L(upperStar (ModuleCat.{u + 1} A) j).obj (S⟦(1 : ℤ)⟧)) :=
    ((shiftFunctor _ (1 : ℤ)).map_isZero hzS).of_iso
      ((L(upperStar (ModuleCat.{u + 1} A) j).commShiftIso (1 : ℤ)).app S)
  have hzFinal := scalar_open_zero φ j _ hzShift
  let adj := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ)).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
  refine ⟨fun f g ↦ (adj.homEquiv (S⟦(1 : ℤ)⟧) N).symm.injective ?_⟩
  exact hzFinal.eq_of_src _ _

/-- Every indicated support-triangle comparison has the counit-defined first component.
The first equality is before transport; the second expresses the same equality after
canonical restriction/direct-image identifications. The final implication detects the
isomorphism before forgetting the B-action. No flatness or faithfulness is assumed.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Existence and Locality;
Stacks 07A6, 0149, 014A, 04CA, 08M3, 010N and 05RT
(blueprint: lem-pur-supported-triangle-mate-identification).

Proof:
1. Exact derived scalar extension and restriction carry the A-support triangle to a
   distinguished triangle. The target is the restricted B-support triangle. The first
   square of the given triangle morphism says a ; Res(counit_B) = Res(T counit_A).
   Use lem-pur-derived-change-of-rings, lem-pur-sheaf-ring-derived-coefficient-adjunction,
   lem-weil-pbc-exact-functor-derived-factorization and lem-exc-closed-support-triangle.
2. Transposition under i_*B adjoint Ri!B gives i_*B(b) ; counit_B = q_i^{-1} ; T counit_A.
   Apply Res and precompose with Res(q_i). The candidate h = Res(q_i) ; Res(i_*B(b))
   satisfies exactly the same first-square equation, without any injectivity on Hom.
   This is the adjunction of lem-exc-closed-ambient.
3. Closed direct image and restriction are exact, and commute sectionwise. Their termwise
   derived comparison applies even when T_Z Ri!A L is unbounded. Thus j* of the source
   first term is zero by open-closed vanishing. The bounded-below open comparison and
   j* adjoint Rj_* imply Hom(S[1], O) = 0; exact j* commutes with shifts. Use
   lem-trf-oriented-closed-base-localization, lem-exc-derived-open-closed-vanishing,
   lem-sbc-canonical-restrict-scalars-functor-comparisons and
   prop-weil-pbc-inverse-image-modules-exact.
4. Hom exactness for the backwards-rotated target triangle factors a-h through O[-1].
   Shift-one orthogonality kills this factor, giving a=h. Naturality of the canonical
   restriction/direct-image comparison gives the displayed transported equation.
   Use lem-weil-pbc-hom-into-triangle-exact.
5. If the open projection is invertible, the middle and right components of the triangle
   morphism are invertible, so its first component is invertible by triangle two-of-three.
   Cancel the invertible q_i to deduce invertibility of i_*A Res_Z(b).
6. The termwise closed inverse/direct-image counit i* i_* = 1 descends through exact
   derived factorization. Applying i* and its natural counit gives invertibility of Res_Z(b).
   Use lem-trf-oriented-closed-base-localization and exact inverse image as in Step 3.
7. Exact restriction commutes with all cohomology and reflects isomorphisms of module
   sheaves. Consequently every cohomology map of b is invertible, and the unbounded
   derived cohomology criterion makes b invertible. Use def-pc-sheaf-restrict-scalars,
   lem-weil-pbc-exact-functor-complex-cohomology and
   lem-weil-pbc-unbounded-derived-iso-cohomology. No flatness of B/A is used. -/
theorem scalarSupportTriangle_mate_identification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategoryModule A P)
    (_hK : ∃ n : ℤ, K.IsGE n)
    (_hTK : ∃ n : ℤ, ((scalarExtension φ P).obj K).IsGE n)
    (_hM : ∃ n : ℤ,
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K).IsGE n)
    (_hN : ∃ n : ℤ,
      ((R(lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
        ((scalarExtension φ P).obj K)).IsGE n)
    (_hOA : ∃ n : ℤ,
      (R(lowerStar (ModuleCat.{u + 1} A) j).obj
        (D(upperStar (ModuleCat.{u + 1} A) j).obj K)).IsGE n)
    (_hOB : ∃ n : ℤ,
      (R(lowerStar (ModuleCat.{u + 1} B) j).obj
        (D(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj K))).IsGE n)
    [IsIso ((scalarMate φ i).app
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))]
    (δA : (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        (D(upperStar (ModuleCat.{u + 1} A) j).obj K) ⟶
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))⟦(1 : ℤ)⟧)
    (δB : (R(lowerStar (ModuleCat.{u + 1} B) j)).obj
        (D(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj K)) ⟶
      ((R(lowerStar (ModuleCat.{u + 1} B) i)).obj
        ((R(lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
          ((scalarExtension φ P).obj K)))⟦(1 : ℤ)⟧)
    (_hδA : scalarSupportTriangle A i j K δA ∈ distTriang _)
    (_hδB : scalarSupportTriangle B i j ((scalarExtension φ P).obj K) δB ∈ distTriang _)
    (τ : (scalarExtension φ P ⋙ Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).mapTriangle.obj
        (scalarSupportTriangle A i j K δA) ⟶
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).mapTriangle.obj
        (scalarSupportTriangle B i j ((scalarExtension φ P).obj K) δB))
    (_hτ₂ : τ.hom₂ = 𝟙 _)
    (_hτ₃ : τ.hom₃ = (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
      (scalarSupportOpenProjection φ j K)) :
    τ.hom₁ = (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
        ((scalarMate φ i).app
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ≫
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
        (R(lowerStar (ModuleCat.{u + 1} B) i).map (scalarSupportClosedMate φ i K)) ∧
    (τ.hom₁ ≫ (scalarRestrictionDirectImageMap φ i).app
        ((R(lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
          ((scalarExtension φ P).obj K)) =
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
          ((scalarMate φ i).app
            ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ≫
        (scalarRestrictionDirectImageMap φ i).app
          ((scalarExtension φ Z).obj
            ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ≫
        R(lowerStar (ModuleCat.{u + 1} A) i).map
          ((Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
            (scalarSupportClosedMate φ i K))) ∧
    (IsIso (scalarSupportOpenProjection φ j K) → IsIso (scalarSupportClosedMate φ i K)) := by
  let TP := scalarExtension φ P
  let RP := Sheaf.derivedRestrictScalars P.smallEtaleTopology φ
  let IB := R(lowerStar (ModuleCat.{u + 1} B) i)
  let M := (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K
  let q := (scalarMate φ i).app M
  let b := scalarSupportClosedMate φ i K
  let adj := Adjunction.ofIsLeftAdjoint IB
  have hb : IB.map b ≫ adj.counit.app (TP.obj K) =
      inv q ≫ TP.map
        ((Adjunction.ofIsLeftAdjoint
          (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K) := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  have hsub := supported_open_orthogonal φ i j
    (by rw [_hij]; exact disjoint_compl_right)
    M (D(upperStar (ModuleCat.{u + 1} B) j).obj (TP.obj K))
  have ht := RP.map_distinguished _ _hδB
  have : Subsingleton
      ((((TP ⋙ RP).mapTriangle.obj (scalarSupportTriangle A i j K δA)).obj₁)⟦(1 : ℤ)⟧ ⟶
        (RP.mapTriangle.obj (scalarSupportTriangle B i j (TP.obj K) δB)).obj₃) := hsub
  have heq : τ.hom₁ = RP.map q ≫ RP.map (IB.map b) := by
    apply Triangle.cancel_mor₁_of_subsingleton ht
    change τ.hom₁ ≫ RP.map (adj.counit.app (TP.obj K)) =
      (RP.map q ≫ RP.map (IB.map b)) ≫ RP.map (adj.counit.app (TP.obj K))
    rw [Category.assoc, ← RP.map_comp, hb, RP.map_comp,
      ← Category.assoc, ← RP.map_comp, IsIso.hom_inv_id, RP.map_id, Category.id_comp]
    have hc := τ.comm₁
    change RP.map (TP.map
      ((Adjunction.ofIsLeftAdjoint
        (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)) ≫ τ.hom₂ =
      τ.hom₁ ≫ RP.map (adj.counit.app (TP.obj K)) at hc
    rw [_hτ₂] at hc
    change RP.map (TP.map
      ((Adjunction.ofIsLeftAdjoint
        (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)) ≫ 𝟙 _ =
      τ.hom₁ ≫ RP.map (adj.counit.app (TP.obj K)) at hc
    simpa only [Category.comp_id] using hc.symm
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, Category.assoc]
    exact congrArg (fun t ↦ RP.map q ≫ t)
      ((scalarRestrictionDirectImageMap φ i).naturality b)
  · intro hop
    have : IsIso τ.hom₂ := by rw [_hτ₂]; infer_instance
    have : IsIso τ.hom₃ := by rw [_hτ₃]; infer_instance
    have := scalarExtension_triangulated φ P
    have : IsIso τ.hom₁ := isIso₁_of_isIso₂₃ τ
      ((TP ⋙ RP).map_distinguished _ _hδA) ht inferInstance inferInstance
    have : IsIso (RP.map q ≫ RP.map (IB.map b)) := heq ▸ inferInstance
    have : IsIso (RP.map (IB.map b)) := IsIso.of_isIso_comp_left (RP.map q) _
    have : IsIso (IB.map b) := restriction_reflects_iso φ P _
    exact isIso_of_reflects_iso b IB

end AlgebraicGeometry.Etale
