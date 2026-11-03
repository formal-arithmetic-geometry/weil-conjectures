/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import all WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCoefficientIso
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-! # Finite admissible Brown hypotheses in all characteristics

Source: `det-ctf-finite-compact-etale` and `det-ctf-finite-compact-proetale`, followed by
the independent thickness, essential-smallness and orthogonal-generation argument of
`det-ctf-finite-compact-generators`. The coefficient comparison below is the proved
finite-cd argument of `BrownHypothesesFiniteCdFiniteCompact`, without its unused positivity
hypothesis. Private helpers retain its explicit constructions.
(blueprint: det-ctf-finite-compact-brown-cd)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace CategoryTheory

/-- For a finite discrete admissible coefficient, finite ℓ-cohomological dimension of the
base field gives the objectwise compactness clause in the Noetherian Brown criterion.

Source: blueprint `det-ctf-finite-compact-etale` and `sk-lem-brown-hypotheses.proof.md`,
compactness paragraph. Proof: transport a bounded constructible finite-Tor complex to the
finite-coefficient étale model, apply the finite-coefficient compactness argument using the
finite torsion cohomological-dimension bound supplied by
`cohomologicalDimension_lt_top_of_finiteType`, and transport compactness back through the
finite discrete coefficient equivalence. The construction is uniform in the finite ring,
the scheme, and the object; the empty scheme and zero ring are included. -/
private theorem brownHypotheses_compact_of_finite_cd_no_hp
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hpl : p ≠ ℓ)
    (hcd : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) :
    ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
      letI := hSums
      ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
        (constantModelBoundedConstructible Λ X K.obj ∧
          DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K := by
  classical
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  obtain ⟨A, _, _, _, _, hA, ⟨r, hr⟩, ⟨e⟩⟩ := hΛ
  let _ := hA
  let B := ULift.{u} A
  have hpB : (ℓ ^ r : ULift.{u + 1} B) = 0 := by
    apply ULift.ext
    apply ULift.ext
    change (ℓ : A) ^ r = 0
    simpa using hr 1
  have hbase := module_cd_of_prime_cd ℓ k hcd (ULift.{u + 1} B) r hpB
  let _ : HasInvertibleExponent (ULift.{u + 1} B) (Spec (.of k)) := by
    refine ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos _, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hpB
    · have hℓ : (ℓ : k) ≠ 0 :=
        CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hpl
      simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom
  let _ : HasInvertibleExponent (ULift.{u + 1} B) X :=
    HasInvertibleExponent.of_hom aX
  obtain ⟨ea⟩ := finiteCoefficientLiftIso.{u} A
  let R := Profinite.continuousCoefficientRingObj B
  have hR : IsLocalizingAdmissibleCoefficient ℓ R := by
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨r, hr⟩, ⟨ea.symm⟩⟩
  have hBR : BrownHypothesesFor R X := by
    obtain ⟨E, hE, _⟩ :=
      FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence B
    obtain ⟨_, _, _, _, hctf, _, _, _, hloc⟩ := hE X
    let d := (E X).fixedDerived
    let L := localizingClosureProEtale R X
    let P := (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).localizingClosure
    have hLP : P.inverseImage d.functor = L := by
      funext K
      apply propext
      have hprop : FiniteDiscreteOrdinary.ordinaryCtf B X =
          AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} B)) X := by
        funext K
        exact propext (ordinary_ctf_iff B X K)
      have h := hloc K
      rw [hprop] at h
      have hclosure : CategoryTheory.localizingClosure
          (AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} B)) X) = P := by
        let Q := AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
        funext M
        apply propext
        constructor
        · intro hm
          exact hm P ⟨inferInstance, inferInstance, fun {I} F hF hFP ↦ by
            let _ := hF
            let _ := closedUnderCoproducts_of_small P (fun _ ↦ inferInstance) I
            exact P.prop_of_isColimit (colimit.isColimit F) (fun i ↦ hFP i.as)⟩
            Q.le_localizingClosure
        · intro hm T ht hQT
          let _ := ht.1
          let _ := ht.2.1
          have hbig (I : Type (u + 2)) :
              T.IsClosedUnderColimitsOfShape (Discrete I) := by
            apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
            rintro _ ⟨F, hF⟩
            exact ht.2.2 F inferInstance (fun i ↦ hF ⟨i⟩)
          have _ (I : Type (u + 1)) :
              T.IsClosedUnderColimitsOfShape (Discrete I) :=
            ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
              (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
          exact hm T hQT { isClosedUnderColimitsOfShape_discrete := fun _ ↦ inferInstance }
      rw [hclosure] at h
      exact h.symm
    let dL := d.congrFullSubcategory hLP
    have _ : dL.functor.Additive :=
      ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
        (d.functor.map_add (f := f.hom) (g := g.hom))⟩
    have _ : dL.inverse.Additive :=
      ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
        (d.inverse.map_add (f := f.hom) (g := g.hom))⟩
    have _ : dL.symm.functor.Additive := inferInstanceAs dL.inverse.Additive
    obtain ⟨_, _, _, _, hSums, _⟩ := brownHypotheses_structural R X
    apply (brownHypothesesFor_iff_compact_of_noetherian ℓ X R hR).mpr
    refine ⟨hSums, fun K hK ↦ ?_⟩
    have hc : BrownRepresentability.IsCompactObj (dL.functor.obj K) := by
      apply AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor
        hbase aX
      exact (ordinary_ctf_iff B X _).mp ((hctf K.obj).mp hK)
    exact (isCompactObject_iff_isCompactObj K).mpr
      ((hc.of_adjunction dL.symm.toAdjunction).of_iso (dL.unitIso.app K))
  have hB := (brownHypothesesFor_coefficientIso_iff (e ≪≫ ea) X).mpr hBR
  exact ((brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ
    (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨r, hr⟩, ⟨e⟩⟩)).mp hB)


/-- Finite admissible Brown hypotheses over a field of finite ℓ-cohomological dimension.

Source: finite-coefficient étale compactness and its pro-étale transfer, followed by the
thickness/smallness and generation paragraphs of `det-ctf-finite-compact-generators`.
(blueprint: det-ctf-finite-compact-brown-cd).

Proof: the torsion cohomological-dimension bound gives a uniform vanishing bound for ordinary
module sheaves after forgetting coefficients. Lift the finite ring to the site universe;
its exponent is invertible because the field characteristic differs from ℓ. The explicit
finite discrete coefficient equivalence identifies constant local models, finite Tor
amplitude and localizing closures. Apply ordinary pro-étale compactness and transport it
back along this equivalence and the explicit coefficient-ring isomorphism. The Noetherian
Brown criterion supplies the remaining structural, thickness, smallness and generation
clauses. No positivity assumption on the field characteristic is used. -/
theorem brownHypotheses_finite_admissible_of_cd
    (ℓ : ℕ) [Fact ℓ.Prime]
    {p : ℕ} {k : Type u} [Field k] [CharP k p]
    (hℓ : p ≠ ℓ)
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    {X : Scheme.{u}} (aX : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) :
    BrownHypothesesFor (Profinite.continuousMapRingObj.{u} A) X := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let _ : Fact (ringChar k ≠ ℓ) := ⟨(ringChar.eq k p) ▸ hℓ⟩
  have hcd' : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤ := hcd
  exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X
    (Profinite.continuousMapRingObj.{u} A)
    (Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA,
      ⟨Iso.refl _⟩⟩)).mpr
    (brownHypotheses_compact_of_finite_cd_no_hp ℓ p hℓ hcd' aX
      (Profinite.continuousMapRingObj.{u} A)
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA,
        ⟨Iso.refl _⟩⟩)

end CategoryTheory
