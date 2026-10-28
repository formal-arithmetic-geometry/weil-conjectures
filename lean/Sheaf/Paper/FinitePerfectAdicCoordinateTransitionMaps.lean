/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
import Sheaf.Paper.FinitePerfectAdicCoordinateScalarExtension
import Sheaf.Paper.WitnessCompatibility
import Sheaf.Paper.EtaleSourceNormalizationUniversal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Transition maps between specified finite perfect adic origins

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.

This is the transition-map and universality part of
`finitePerfectAdic_descend_coordinate_transitions`.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-maps)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/--
The supplied comparisons of finite quotient coordinates determine consecutive
coefficient-restricted arrows.  Each arrow is universal after etale pullback.

Source: Stacks Project, Tags 09AL and 09C6; balancing in Tag 06YY.
(blueprint: new-w5-finite-perfect-adic-coordinate-transition-maps)
-/
theorem finitePerfectAdic_coordinate_transition_maps
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅
      finitePerfectAdicQuotientCoordinates X d φ M V n) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
        (normalizationRestrict V.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
      ∀ (n : ℕ) (U : V.left.Etale), Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (dK n) U))) := by
  classical
  have hstep (n : ℕ) : ∃ δ : K (n + 1) ⟶
      (normalizationRestrict V.left.smallEtaleTopology
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
      ∀ U : V.left.Etale, Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) δ U))) := by
    let R := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
    let S := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
    let q : R →+* S := RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    let T := ProEtale.pbcFixedScalarExtension V.left.smallEtaleTopology q
    let P := ProEtale.pbcFixedScalarExtension (ProEt.topology V.left) q
    let c := ProEtale.pbcComparisonReduction V.left q
    let aT := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars V.left.smallEtaleTopology q)
    let aP := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology V.left) q)
    obtain ⟨b⟩ := finitePerfectAdic_coordinate_scalar_extension X d φ hφ hcompat M V n
      P aP
    let F := ProEtale.comparisonUpperStar (ModuleCat.{t + 1} S) V.left
    let k : F.mapDerivedCategory.obj (T.obj (K (n + 1))) ≅
        F.mapDerivedCategory.obj (K n) :=
      (c.app (K (n + 1))).symm ≪≫ P.mapIso (e (n + 1)) ≪≫
        b ≪≫ (e n).symm
    obtain ⟨f, hf⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        (T.obj (K (n + 1))) (K n) (hKplus n)).2 k.hom
    have hfi : IsIso (F.mapDerivedCategory.map f) := by
      have hf' : F.mapDerivedCategory.map f = k.hom := hf
      rw [hf']
      infer_instance
    have : IsIso f := by
      rw [DerivedCategory.isIso_iff]
      intro i
      have hi : IsIso (F.map ((DerivedCategory.homologyFunctor _ i).map f)) :=
        (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).2
          (by dsimp only [Functor.comp_map]; infer_instance)
      exact isIso_of_reflects_iso _ F
    let δ := aT.unit.app (K (n + 1)) ≫
      (normalizationRestrict V.left.smallEtaleTopology q).map f
    have hδ : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk δ)) := by
      refine ⟨(mkInitialOfLeftAdjoint _ aT (K (n + 1))).ofIso
        (StructuredArrow.isoMk (asIso f) ?_)⟩
      rfl
    exact ⟨δ, fun U ↦ etaleSourceNormalization_universal V.left q δ hδ U⟩
  choose δ hδ using hstep
  exact ⟨δ, hδ⟩

end AlgebraicGeometry.Scheme
