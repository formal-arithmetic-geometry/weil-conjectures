/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Exceptional inverse image and arbitrary finite coefficient change

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
`thm-coef-finite-hom.proof.md`, Paragraph 3, and `lem-coef-finite-closed-shriek.proof.md`
in the same directory (blueprint: lem-coef-general-finite-closed-shriek).

The ordinary direct-image coefficient comparison is inverted by the canonical mate
construction.  The resulting natural transformation is the exceptional coefficient
comparison; its counit equation is included in the statement below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.FiniteCoefficientOrdinary

/-- The closed-immersion coefficient comparison is invertible on every ordinary derived
object.  This is the direct-image input to the exceptional mate construction.
Source: latest Weil blueprint, `lem-coef-finite-closed-shriek.proof.md`, Paragraph 1
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: closed direct image is exact, preserves sums, and is extension by zero on geometric
stalks. Thus it commutes with tensor by the constant coefficient complex on K-flat
representatives, without any boundedness restriction on N. The resulting derived tensor
isomorphism is the canonical direct-image comparison, by its adjunction characterization.
-/
theorem isIso_directImageComparison_of_isClosedImmersion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∀ N : Etale.DerivedCategoryModule A Z,
      IsIso ((directImageMaps.etale φ i).app N) := by
  sorry

/-- The canonical natural transformation obtained by taking the mate of the ordinary
closed direct-image coefficient isomorphism.

Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3
(blueprint: lem-coef-general-finite-closed-shriek).
-/
noncomputable def closedShriekCoefficientMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint := by
  let F_A := R(Etale.lowerStar (ModuleCat.{u + 1} A) i)
  let F_B := R(Etale.lowerStar (ModuleCat.{u + 1} B) i)
  let q : F_A ⋙ Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ≅
      Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⋙ F_B :=
    NatIso.ofComponents
      (fun N ↦ letI := isIso_directImageComparison_of_isClosedImmersion φ i N
        asIso ((directImageMaps.etale φ i).app N)) (by
        intro N N' f
        exact (directImageMaps.etale φ i).naturality f)
  exact (mateEquiv (Adjunction.ofIsLeftAdjoint F_A)
    (Adjunction.ofIsLeftAdjoint F_B)
    (TwoSquare.mk _ _ _ _ q.inv)).natTrans

/-- The right-adjoint conjugate of the derived direct-image compositor for two closed
immersions.  This is the canonical `e` used to identify the composite exceptional
right adjoint with the iterated exceptional right adjoint.
Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3
(blueprint: lem-coef-general-finite-closed-shriek).
-/
noncomputable def closedShriekCompositionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (i' : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) (i' ≫ i))).rightAdjoint ≅
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i')).rightAdjoint :=
  by
    let aComp := Adjunction.ofIsLeftAdjoint
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) (i' ≫ i)))
    let aIter := (Adjunction.ofIsLeftAdjoint
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) i'))).comp
      (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
    exact conjugateIsoEquiv aComp aIter
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i' i)

/-- Data expressing the general finite coefficient closed-shriek comparison.
The comparison is a natural transformation, so its naturality in the complex is part
of the field `comparison`; the mate equation uniquely specifies every component.
The two coherence fields state equalities of exceptional coefficient mates at M. Composition
uses the conjugate of the direct-image compositor, while successive coefficient change uses
the scalar-composition isomorphisms on the source and target of the exceptional functor.
Source: latest Weil blueprint, `lem-coef-finite-closed-shriek.proof.md`, Paragraphs 1--2
(blueprint: lem-coef-general-finite-closed-shriek).
-/
structure ClosedShriekComparisonData
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule A X) where
  comparison :
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint
  comparison_isIso : IsIso (comparison.app M)
  comparison_is_canonical : comparison = closedShriekCoefficientMate φ i
  comparison_counit :
    (directImageMaps.etale φ i).app
          ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map (comparison.app M) ≫
      (Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
      ((Adjunction.ofIsLeftAdjoint
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M)
  comparison_unique :
    ∀ b :
        (Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ).obj
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ⟶
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
            ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M),
      (directImageMaps.etale φ i).app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).map b ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i))).counit.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M) =
      (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).map
        ((Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M) →
      b = comparison.app M
  comparison_composition :
    ∀ {W : Scheme.{u}} (i' : W ⟶ Z) [IsClosedImmersion i'],
      (closedShriekCoefficientMate φ (i' ≫ i)).app M =
        (Sheaf.fixedCoefficientDerivedScalarExtension (W.smallEtaleTopology) φ).map
            ((closedShriekCompositionIso A i' i).hom.app M) ≫
          (closedShriekCoefficientMate φ i').app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
          (R(Etale.lowerStar (ModuleCat.{u + 1} B) i')).rightAdjoint.map
            ((closedShriekCoefficientMate φ i).app M) ≫
          (closedShriekCompositionIso B i' i).inv.app
            ((Sheaf.fixedCoefficientDerivedScalarExtension
              (X.smallEtaleTopology) φ).obj M)
  comparison_successive_change :
    ∀ {C : Type (u + 1)} [CommRing C] [Finite C]
      (ψ : B →+* C),
      (closedShriekCoefficientMate (ψ.comp φ) i).app M =
        (scalarComposition (Z.smallEtaleTopology) φ ψ).inv.app
            ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M) ≫
          (Sheaf.fixedCoefficientDerivedScalarExtension
            (Z.smallEtaleTopology) ψ).map ((closedShriekCoefficientMate φ i).app M) ≫
          (closedShriekCoefficientMate ψ i).app
            ((Sheaf.fixedCoefficientDerivedScalarExtension
              (X.smallEtaleTopology) φ).obj M) ≫
          (R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).rightAdjoint.map
            ((scalarComposition (X.smallEtaleTopology) φ ψ).hom.app M)
  source_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor A Z
      ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M)
  scalar_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor B Z
      ((Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ).obj
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj M))
  target_finite :
    Etale.DerivedCategory.boundedConstructibleFiniteTor B Z
      ((R(Etale.lowerStar (ModuleCat.{u + 1} B) i)).rightAdjoint.obj
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M))

/-- Exceptional inverse image commutes with arbitrary finite coefficient change on the
small étale site.

Source: latest Weil blueprint, `thm-coef-finite-hom.proof.md`, Paragraph 3 and
`lem-coef-finite-closed-shriek.proof.md`, Paragraphs 1--2
(blueprint: lem-coef-general-finite-closed-shriek).

Proof: tensor the closed-support triangle by the coefficient ring and compare its open
term by the ordinary finite direct-image theorem.  The first component is the scalar
extension of the exceptional counit after the canonical direct-image comparison; the
closed direct image is fully faithful, so its adjoint transpose is invertible.  The
finite-Tor constructibility assertion is obtained from the boundary-duality and finite
biduality inputs.  Naturality, the counit equation, composition of closed immersions,
and successive coefficient changes follow by uniqueness of adjoint mates and the
canonical direct-image compositor.
-/
theorem generalFiniteCoefficientClosedShriek
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (_hell : IsUnit (ell : k))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (_hA : ∃ r : ℕ, (ell ^ r : A) = 0)
    (_hB : ∃ r : ℕ, (ell ^ r : B) = 0)
    {Z X : Scheme.{u}}
    (aZ : Z ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    (aX : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (_hi : i ≫ aX = aZ)
    (M : Etale.DerivedCategoryModule A X)
    (_hM : Etale.DerivedCategory.boundedConstructibleFiniteTor A X M) :
    Nonempty (ClosedShriekComparisonData φ i M) := by
  sorry

end AlgebraicGeometry.FiniteCoefficientOrdinary
