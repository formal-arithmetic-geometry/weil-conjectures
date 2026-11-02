/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Finite constructible realization without a fixed Tor interval -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- Realization identifies the unions of all finite constructible Tor intervals.
Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i)
(blueprint: lem-sf-finite-condensed-ctf-equivalence).

Proof: enlarge any Tor endpoints c,d to min(c,d),max(c,d). Apply finite constructible
realization on this ordered interval. Its compatibility isomorphism gives preservation
and essential surjectivity for the union domains. The derived site pullback is fully
faithful when the second argument is bounded below, as each bounded constructible
argument is. The encoding is an equivalence, so the restricted realization is fully
faithful and essentially surjective. Its induced equivalence has the required ambient
compatibility. In particular no common Tor interval for every object is chosen. -/
theorem finiteCondensedCtfEquivalence
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (enc : ∀ X : Scheme.{u}, Encoding A X)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ hF : ∀ K : (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} A) T ⊓ _root_.DerivedCategory.finiteTorAmplitude _).FullSubcategory,
        (constantModelBoundedConstructible (coefficient A) T ⊓
          _root_.DerivedCategory.finiteTorAmplitude _)
            ((internalEtaleRealization A T (enc T)).obj K.obj),
      (ObjectProperty.lift
        (constantModelBoundedConstructible (coefficient A) T ⊓
          _root_.DerivedCategory.finiteTorAmplitude _)
        (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} A) T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) ⋙
            internalEtaleRealization A T (enc T)) hF).IsEquivalence := by
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := constantModelBoundedConstructible (coefficient A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let S := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let H := P.ι ⋙ S.mapDerivedCategory
  have hplus (K : P.FullSubcategory) :
      _root_.DerivedCategory.TStructure.t.plus K.obj := by
    obtain ⟨_, c, d, _, hv⟩ := K.property.1
    exact ⟨c, (_root_.DerivedCategory.isGE_iff K.obj c).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩
  have : H.Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).surjective f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have : H.Faithful := ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
    ((bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).injective h)⟩
  have : LocallyOfFiniteType (Over.mk a).hom := ‹LocallyOfFiniteType a›
  have : QuasiCompact (Over.mk a).hom := ‹QuasiCompact a›
  have : IsSeparated (Over.mk a).hom := ‹IsSeparated a›
  have : (constantModelBoundedConstructible (coefficient A) T).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficient A) T).2.1
  have intervals := (finiteCtfInternalEtaleRealization ℓ p k
    (Fact.out : p.Prime).pos hpℓ A enc).1 (Over.mk a)
  have mem (K : P.FullSubcategory) :
      Q ((internalEtaleRealization A T (enc T)).obj K.obj) := by
    obtain ⟨c, d, ht⟩ := K.property.2
    have ht' := ht.mono (min_le_left c d) (le_max_right c d)
    obtain ⟨e, ⟨he⟩⟩ := intervals (min c d) (max c d) min_le_max
    let K' : ObjectProperty.FullSubcategory
        (fun M ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T M ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T
            (min c d) (max c d) M) :=
      ⟨K.obj, K.property.1,
        Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr ht'⟩
    have h := (e.functor.obj K').property
    refine ⟨(constantModelBoundedConstructible (coefficient A) T).prop_of_iso
      (he.app K') h.1, min c d, max c d, ?_⟩
    exact (_root_.DerivedCategory.torAmplitudeIn _ _ _).prop_of_iso (he.app K') h.2
  let R := Q.lift (H ⋙ (enc T).fixedDerived.inverse) mem
  have : R.Full := by dsimp [R]; infer_instance
  have : R.Faithful := by dsimp [R]; infer_instance
  have : R.EssSurj := by
    constructor
    intro K
    obtain ⟨c, d, ht⟩ := K.property.2
    have ht' := ht.mono (min_le_left c d) (le_max_right c d)
    obtain ⟨e, ⟨he⟩⟩ := intervals (min c d) (max c d) min_le_max
    let K' : ObjectProperty.FullSubcategory
        (fun M ↦ constantModelBoundedConstructible (coefficient A) T M ∧
          _root_.DerivedCategory.torAmplitudeIn (Internal A T) (min c d) (max c d) M) :=
      ⟨K.obj, K.property.1, ht'⟩
    let L := e.inverse.obj K'
    let L' : P.FullSubcategory := ⟨L.obj, L.property.1, min c d, max c d,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp L.property.2⟩
    refine ⟨L', ⟨Q.isoMk ((he.app L).symm ≪≫ ?_)⟩⟩
    exact (ObjectProperty.ι _).mapIso (e.counitIso.app K')
  have : R.IsEquivalence := {}
  exact ⟨mem, inferInstanceAs R.IsEquivalence⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
