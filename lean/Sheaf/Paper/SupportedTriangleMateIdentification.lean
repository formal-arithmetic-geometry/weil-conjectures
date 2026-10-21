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
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import WeilConjectures.SixFunctors.OpenClosed.Derived
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
  sorry

end AlgebraicGeometry.Etale
