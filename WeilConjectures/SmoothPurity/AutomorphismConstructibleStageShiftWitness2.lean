/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing

/-!
# Integer shift witnesses for ordinary condensed pullbacks

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md, Weil structures paragraph.
(blueprint: new-h2-integral-shift-witness)

The auxiliary definitions construct the bounded-constructible restrictions, their canonical
termwise comparisons, and the inverse square comparison. The theorem records the integer shifts,
exactness, and compatibility for the coefficient cases of the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The four coefficient transports elaborate several canonical ring-object instances.
/-- Normalized shifts on the bounded constructible restrictions in the specified square.
Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md, Weil structures paragraph
(blueprint: new-h2-integral-shift-witness).

Proof: derived upper-star preserves bounded constructibility for `f`; transport by the
scheme isomorphisms preserves it for `eX` and `eY`, without assuming they are linear over
`D.k`. The coefficient-specific triangulated-subcategory theorem applies since separated
finite-type schemes over `D.k` are noetherian. Transport termwise integer shifts through
`modulePullbackExactComparison`, and restrict through the fully faithful inclusions. The
three termwise comparisons then commute with shifts and the restrictions are triangulated.
The ambient square comparison commutes with these shifts by the compositor-shifts theorem.
Its inverse does too; full faithfulness restricts this identity to the specified comparison.
Here exactness of a functor of triangulated categories is `IsTriangulated`, together with
its coherent integer `CommShift` structure. -/
theorem automorphismConstructibleStage_condensed_shift_witness
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj.{u}
        (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ))))
    (f : Y ⟶ X) (eX : X.left ≅ X.left) (eY : Y.left ≅ Y.left)
    (h : eY.hom ≫ f.left = f.left ≫ eX.hom) :
    ∃ (tX : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated)
      (tY : (boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated),
      (fun [tx : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated]
        [ty : (boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated] ↦
        ∃ (cf : (restrictedCondensedPullback Λ f.left).CommShift ℤ)
          (cX : (restrictedCondensedPullback Λ eX.hom).CommShift ℤ)
          (cY : (restrictedCondensedPullback Λ eY.hom).CommShift ℤ),
          (fun [sf : (restrictedCondensedPullback Λ f.left).CommShift ℤ]
            [sx : (restrictedCondensedPullback Λ eX.hom).CommShift ℤ]
            [sy : (restrictedCondensedPullback Λ eY.hom).CommShift ℤ] ↦
            NatTrans.CommShift (restrictedCondensedPullbackTermwiseComparison Λ f.left).hom ℤ ∧
              NatTrans.CommShift (restrictedCondensedPullbackTermwiseComparison Λ eX.hom).hom ℤ ∧
              NatTrans.CommShift (restrictedCondensedPullbackTermwiseComparison Λ eY.hom).hom ℤ ∧
              (restrictedCondensedPullback Λ f.left).IsTriangulated ∧
              (restrictedCondensedPullback Λ eX.hom).IsTriangulated ∧
              (restrictedCondensedPullback Λ eY.hom).IsTriangulated ∧
              NatTrans.CommShift
                (restrictedCondensedPullbackSquareComparison Λ f.left eX eY h).hom ℤ)
            (sf := cf) (sx := cX) (sy := cY)) (tx := tX) (ty := tY) := by
  have htri_of_iso
      {Z : Scheme.{u}}
      {R T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}}
      [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
      (φ : T ⟶ R) [IsMonHom φ] [IsIso φ]
      [(boundedConstructible T).IsTriangulated] :
      (boundedConstructible R).IsTriangulated := by
    have heq : boundedConstructible R =
        (boundedConstructible T).inverseImage (Mod.comap φ).mapDerivedCategory := by
      ext L
      exact (boundedConstructible_comap_iso_iff φ L).symm
    rw [heq]
    infer_instance
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have tX : (boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated := by
    rcases hΛ with hA | hO | hE | hQ
    · obtain ⟨i⟩ := hA
      let A := PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)
      have : Finite A := by
        dsimp [A]
        rw [hπ]
        infer_instance
      let : TopologicalSpace A := ⊥
      have : DiscreteTopology A := ⟨rfl⟩
      let φ : IntegralModelsEmbedded.discreteObj.{u} A ⟶
          Profinite.continuousMapRingObj.{u} A :=
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous A)
      have : IsIso (IntegralModelsEmbedded.constantToContinuous A) := by
        let J := coherentTopology Profinite.{u}
        let g := Profinite.constantToContinuousRing.{u} A
        have : Presheaf.IsLocallyInjective J g :=
          ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
            (Profinite.constantToContinuousAb.{u} A) a b h⟩
        have : Presheaf.IsLocallySurjective J g :=
          ⟨fun a ↦ Presheaf.imageSieve_mem J (Profinite.constantToContinuousAb.{u} A) a⟩
        have hg : J.W g := J.W_of_isLocallyBijective g
        have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map g) := (J.W_iff g).mp hg
        unfold IntegralModelsEmbedded.constantToContinuous
        rw [Adjunction.homEquiv_counit]
        change IsIso (_ ≫ (presheafToSheaf J RingCat.{u + 1}).map g ≫ _)
        infer_instance
      have : IsIso φ := by dsimp [φ]; infer_instance
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom X.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint X.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.continuousMapRingObj A) X.left)).IsTriangulated :=
        AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_finiteDiscreteRingObj
          X.left A
      have : IsIso (Mon.mkIso' (asIso φ)).inv.hom :=
        inferInstanceAs (IsIso ((Mon.forget _).map (Mon.mkIso' (asIso φ)).inv))
      have : IsIso (coefficientMap (Mon.mkIso' (asIso φ)).inv.hom X.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint X.left).map
          (Mon.mkIso' (asIso φ)).inv.hom))
      exact htri_of_iso (coefficientMap (Mon.mkIso' (asIso φ)).inv.hom X.left ≫
        coefficientMap i.inv.hom X.left)
    · obtain ⟨i⟩ := hO
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom X.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint X.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.padicIntegersRingObj ℓ E.1) X.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_padicIntegers
          X.left ℓ E.1
      exact htri_of_iso (coefficientMap i.inv.hom X.left)
    · obtain ⟨i⟩ := hE
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom X.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint X.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.continuousMapRingObj E) X.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_continuous
          X.left ℓ E
      exact htri_of_iso (coefficientMap i.inv.hom X.left)
    · obtain ⟨i⟩ := hQ
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom X.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint X.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_padicAlgCl
          X.left ℓ
      exact htri_of_iso (coefficientMap i.inv.hom X.left)
  have tY : (boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated := by
    rcases hΛ with hA | hO | hE | hQ
    · obtain ⟨i⟩ := hA
      let A := PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)
      have : Finite A := by
        dsimp [A]
        rw [hπ]
        infer_instance
      let : TopologicalSpace A := ⊥
      have : DiscreteTopology A := ⟨rfl⟩
      let φ : IntegralModelsEmbedded.discreteObj.{u} A ⟶
          Profinite.continuousMapRingObj.{u} A :=
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous A)
      have : IsIso (IntegralModelsEmbedded.constantToContinuous A) := by
        let J := coherentTopology Profinite.{u}
        let g := Profinite.constantToContinuousRing.{u} A
        have : Presheaf.IsLocallyInjective J g :=
          ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
            (Profinite.constantToContinuousAb.{u} A) a b h⟩
        have : Presheaf.IsLocallySurjective J g :=
          ⟨fun a ↦ Presheaf.imageSieve_mem J (Profinite.constantToContinuousAb.{u} A) a⟩
        have hg : J.W g := J.W_of_isLocallyBijective g
        have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map g) := (J.W_iff g).mp hg
        unfold IntegralModelsEmbedded.constantToContinuous
        rw [Adjunction.homEquiv_counit]
        change IsIso (_ ≫ (presheafToSheaf J RingCat.{u + 1}).map g ≫ _)
        infer_instance
      have : IsIso φ := by dsimp [φ]; infer_instance
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom Y.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint Y.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.continuousMapRingObj A) Y.left)).IsTriangulated :=
        AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_finiteDiscreteRingObj
          Y.left A
      have : IsIso (Mon.mkIso' (asIso φ)).inv.hom :=
        inferInstanceAs (IsIso ((Mon.forget _).map (Mon.mkIso' (asIso φ)).inv))
      have : IsIso (coefficientMap (Mon.mkIso' (asIso φ)).inv.hom Y.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint Y.left).map
          (Mon.mkIso' (asIso φ)).inv.hom))
      exact htri_of_iso (coefficientMap (Mon.mkIso' (asIso φ)).inv.hom Y.left ≫
        coefficientMap i.inv.hom Y.left)
    · obtain ⟨i⟩ := hO
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom Y.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint Y.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.padicIntegersRingObj ℓ E.1) Y.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_padicIntegers
          Y.left ℓ E.1
      exact htri_of_iso (coefficientMap i.inv.hom Y.left)
    · obtain ⟨i⟩ := hE
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom Y.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint Y.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.continuousMapRingObj E) Y.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_continuous
          Y.left ℓ E
      exact htri_of_iso (coefficientMap i.inv.hom Y.left)
    · obtain ⟨i⟩ := hQ
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom Y.left) :=
        inferInstanceAs (IsIso ((upperStarFromPoint Y.left).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) Y.left)).IsTriangulated :=
        isTriangulated_boundedConstructible_ellAdic_padicAlgCl
          Y.left ℓ
      exact htri_of_iso (coefficientMap i.inv.hom Y.left)
  let := tX
  let := tY
  refine ⟨tX, tY, ?_⟩
  dsimp
  let cf : (restrictedCondensedPullback Λ f.left).CommShift ℤ := by
    unfold restrictedCondensedPullback
    infer_instance
  let cX : (restrictedCondensedPullback Λ eX.hom).CommShift ℤ := by
    unfold restrictedCondensedPullback
    infer_instance
  let cY : (restrictedCondensedPullback Λ eY.hom).CommShift ℤ := by
    unfold restrictedCondensedPullback
    infer_instance
  refine ⟨cf, cX, cY, ?_⟩
  have hf : NatTrans.CommShift
      (restrictedCondensedPullbackCompatibility Λ f.left).hom ℤ := by
    exact Functor.CommShift.ofComp_compatibility _ _
  have hx : NatTrans.CommShift
      (restrictedCondensedPullbackCompatibility Λ eX.hom).hom ℤ := by
    exact Functor.CommShift.ofComp_compatibility _ _
  have hy : NatTrans.CommShift
      (restrictedCondensedPullbackCompatibility Λ eY.hom).hom ℤ := by
    exact Functor.CommShift.ofComp_compatibility _ _
  have ht (S T : Scheme.{u}) (g : S ⟶ T) :=
    (module_derived_functors_exact_and_comparison_shifts Λ g).1
  have hc (S T : Scheme.{u}) (g : S ⟶ T) :=
    (module_derived_functors_exact_and_comparison_shifts Λ g).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold restrictedCondensedPullbackTermwiseComparison
    infer_instance
  · unfold restrictedCondensedPullbackTermwiseComparison
    infer_instance
  · unfold restrictedCondensedPullbackTermwiseComparison
    infer_instance
  · exact (Functor.isTriangulated_iff_comp_right
      (restrictedCondensedPullbackCompatibility Λ f.left)).2 inferInstance
  · exact (Functor.isTriangulated_iff_comp_right
      (restrictedCondensedPullbackCompatibility Λ eX.hom)).2 inferInstance
  · exact (Functor.isTriangulated_iff_comp_right
      (restrictedCondensedPullbackCompatibility Λ eY.hom)).2 inferInstance
  · have hs : NatTrans.CommShift
        (modulePullbackSquareComparison Λ f.left eX.hom eY.hom f.left h.symm).hom ℤ := by
      constructor
      intro m
      ext K
      exact (module_pullback_square_shift Λ f.left eX.hom eY.hom f.left h.symm K m).symm
    unfold restrictedCondensedPullbackSquareComparison
    infer_instance

end WeilConjectures
