/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.FieldTheory.MakeSeparable
import Sheaf.RingTheory.JZeroFiniteTypeDomainDescent
import Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent

/-!
# The domain case of the residue-field criterion for J-2

Source: Stacks Project, More on Algebra, Tag 07PC, implication (4) to (2)
(blueprint: lem-exc-j2-residue-field-criterion-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

private theorem separablyGenerated_algEquiv
    {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (e : E ≃ₐ[k] F) (h : Algebra.IsSeparablyGenerated k E) :
    Algebra.IsSeparablyGenerated k F := by
  obtain ⟨s, hs, hsep⟩ := h
  let t : Set F := e '' s
  have ht : IsTranscendenceBasis k ((↑) : t → F) :=
    (e.isTranscendenceBasis hs).to_subtype_range' (by
      rw [Set.range_comp, Subtype.range_coe])
  refine ⟨t, ht, ?_⟩
  let d : IntermediateField.adjoin k s ≃ₐ[k] IntermediateField.adjoin k t :=
    ((IntermediateField.adjoin k s).equivMap e.toAlgHom).trans
      (IntermediateField.equivOfEq (IntermediateField.adjoin_map k s e.toAlgHom))
  let := hsep
  exact Algebra.IsSeparable.of_equiv_equiv d.toRingEquiv e.toRingEquiv (by ext; rfl)

private theorem separablyGenerated_baseEquiv
    {k l E : Type*} [Field k] [Field l] [Field E] [Algebra k E] [Algebra l E]
    (e : k ≃+* l) (he : (algebraMap l E).comp e.toRingHom = algebraMap k E)
    (h : Algebra.IsSeparablyGenerated l E) : Algebra.IsSeparablyGenerated k E := by
  have hai (t : Set E) :
      AlgebraicIndependent l ((↑) : t → E) ↔
        AlgebraicIndependent k ((↑) : t → E) := by
    simpa only [RingHom.coe_id, Function.id_comp] using
      (algebraicIndependent_ringHom_iff_of_comp_eq e (RingHom.id E)
        Function.injective_id he)
  obtain ⟨s, hs, hsep⟩ := h
  refine ⟨s, ⟨(hai _).mp hs.1, ?_⟩, ?_⟩
  · intro t ht hst
    exact hs.2 t ((hai _).mpr ht) hst
  · have hrange : Set.range (algebraMap k E) = Set.range (algebraMap l E) := by
      rw [← he, RingHom.coe_comp, Set.range_comp,
        (show Function.Surjective e.toRingHom from e.surjective).range_eq, Set.image_univ]
    have hfields : (IntermediateField.adjoin l s).toSubfield =
        (IntermediateField.adjoin k s).toSubfield := by
      simp only [IntermediateField.adjoin_toSubfield, hrange]
    let d := RingEquiv.subfieldCongr hfields
    let := hsep
    exact Algebra.IsSeparable.of_equiv_equiv d (RingEquiv.refl E) (by ext; rfl)

private theorem separable_of_injective
    {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (f : E →ₐ[k] F) (h : Algebra.IsSeparableExtension k F) :
    Algebra.IsSeparableExtension k E := by
  classical
  intro T hT
  have hmap : (T.map f).FG := by
    obtain ⟨t, ht⟩ := hT
    refine ⟨t.image f, ?_⟩
    rw [Finset.coe_image, ← IntermediateField.adjoin_map, ht]
  exact separablyGenerated_algEquiv (T.equivMap f).symm (h (T.map f) hmap)

private theorem separable_baseEquiv
    {k l E : Type*} [Field k] [Field l] [Field E] [Algebra k E] [Algebra l E]
    (e : k ≃+* l) (he : (algebraMap l E).comp e.toRingHom = algebraMap k E)
    (h : Algebra.IsSeparableExtension l E) : Algebra.IsSeparableExtension k E := by
  intro T hT
  have hrange : Set.range (algebraMap k E) = Set.range (algebraMap l E) := by
    rw [← he, RingHom.coe_comp, Set.range_comp,
      (show Function.Surjective e.toRingHom from e.surjective).range_eq, Set.image_univ]
  let U : IntermediateField l E :=
    { T.toSubfield with
      algebraMap_mem' := fun x ↦ by
        obtain ⟨y, rfl⟩ := e.surjective x
        change ((algebraMap l E).comp e.toRingHom) y ∈ T.toSubfield
        rw [he]
        exact T.algebraMap_mem y }
  have hU : U.FG := by
    obtain ⟨t, ht⟩ := hT
    refine ⟨t, ?_⟩
    apply IntermediateField.toSubfield_injective
    change Subfield.closure (Set.range (algebraMap l E) ∪ (t : Set E)) = T.toSubfield
    rw [← hrange]
    exact congrArg IntermediateField.toSubfield ht
  let : Algebra l T := inferInstanceAs (Algebra l U)
  have hcompat : (algebraMap l T).comp e.toRingHom = algebraMap k T := by
    ext x
    exact DFunLike.congr_fun he x
  exact separablyGenerated_baseEquiv e hcompat (h U hU)

/-- A finite type domain over a Noetherian ring has a nonempty regular open when the
residue-field finite-model hypothesis holds.

Source: Stacks Project, More on Algebra, Tag 07PC, lemma-J-2, implication (4) to (2).
The proof constructs the residue field of the kernel of `R → S`, applies the finite
purely inseparable separable-model construction, forms the image of `S ⊗[R] B` in the
resulting field, and applies the separable ascent and finite-type descent lemmas.
The fraction field of the tensor-image domain is the compositum of the two original
fraction fields; restricting the separability hypothesis to this intermediate field
supplies the ascent lemma. (blueprint: lem-exc-j2-residue-field-criterion-domain)
-/
theorem exists_nonempty_regular_open_of_residueField_finite_models_domain
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hmodels : ∀ (p : Ideal R) [p.IsPrime] (L : Type (max u v)) [Field L]
      [Algebra p.ResidueField L] [Algebra R L] [IsScalarTower R p.ResidueField L]
      [Module.Finite p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        (∀ x : L, ∃ b c : B, (c : L) ≠ 0 ∧ x = (b : L) / (c : L)) ∧
        ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ U.Nonempty ∧
          ∀ q ∈ U, IsRegularLocalRing (Localization.AtPrime q.asIdeal))
    (S : Type (max u v)) [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S] :
    ∃ U : Set (PrimeSpectrum S), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  classical
  let K := FractionRing S
  let p := RingHom.ker (algebraMap R K)
  let : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  have hf : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    exact isUnit_iff_ne_zero.mpr hr
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap R K) le_rfl hf
  let : Algebra p.ResidueField K := f.toAlgebra
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) le_rfl hf r).symm)
  let : Algebra.EssFiniteType S K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors S)
  let : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R S K
  let : Algebra.EssFiniteType p.ResidueField K := Algebra.EssFiniteType.of_comp R _ _
  obtain ⟨L, K', hL, hK', akL, akK', aLK', aKK', htL, htK, hfinL, hpiL,
      hfinK, hpiK, hsep⟩ :=
    Algebra.exists_finite_purelyInseparable_separable_extension p.ResidueField K
      (IntermediateField.fg_top _ _)
  let := hL
  let := hK'
  let := akL
  let := akK'
  let := aLK'
  let := aKK'
  let := htL
  let := htK
  let := hfinL
  let := hpiL
  let : Algebra R L := ((algebraMap p.ResidueField L).comp
    (algebraMap R p.ResidueField)).toAlgebra
  let : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, hBfin, hBfrac, hBreg⟩ := hmodels p L
  let := hBfin
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : IsFractionRing B L := IsFractionRing.of_field (R := B) L (fun x ↦ by
    obtain ⟨b, c, _, h⟩ := hBfrac x
    exact ⟨b, c, h⟩)
  let : Algebra S K' := ((algebraMap K K').comp (algebraMap S K)).toAlgebra
  let : IsScalarTower S K K' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R K' := ((algebraMap S K').comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S K' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap S K' (algebraMap R S r) =
      algebraMap K K' (algebraMap R K r)
    rw [IsScalarTower.algebraMap_apply R S K]
    rfl)
  let : IsScalarTower R p.ResidueField K' := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R K K',
      IsScalarTower.algebraMap_eq R p.ResidueField K,
      IsScalarTower.algebraMap_eq p.ResidueField K K']
    rfl)
  let : IsScalarTower R L K' := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R p.ResidueField K',
      IsScalarTower.algebraMap_eq R p.ResidueField L,
      IsScalarTower.algebraMap_eq p.ResidueField L K']
    rfl)
  let : Algebra B K' := inferInstance
  let : IsScalarTower B L K' := inferInstance
  let : IsScalarTower R B K' := inferInstance
  let t : B ⊗[R] S →ₐ[B] K' :=
    AlgHom.liftEquiv R B S K' (IsScalarTower.toAlgHom R S K')
  let C := t.range
  let : Algebra.FiniteType B C := Algebra.FiniteType.of_surjective
    t.rangeRestrict t.rangeRestrict_surjective
  let : Algebra.FiniteType R B := inferInstance
  let g : S →ₐ[R] C :=
    { __ := (t.rangeRestrict.restrictScalars R).comp Algebra.TensorProduct.includeRight }
  let : Algebra S C := g.toRingHom.toAlgebra
  let : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let : Algebra.FiniteType R C := Algebra.FiniteType.trans (S := B)
    inferInstance inferInstance
  let : Algebra.FiniteType S C := Algebra.FiniteType.of_restrictScalars_finiteType R S C
  have hg (s : S) : (g s : K') = algebraMap S K' s := by
    change t (1 ⊗ₜ[R] s) = _
    simp [t]
  have hinj : Function.Injective g := by
    intro x y h
    apply IsFractionRing.injective S K
    apply (algebraMap K K').injective
    change algebraMap S K' x = algebraMap S K' y
    rw [← hg, ← hg, h]
  have hBinj : Function.Injective (algebraMap B C) := by
    intro x y h
    apply Function.Injective.comp (algebraMap L K').injective
      (IsFractionRing.injective B L)
    change algebraMap L K' (algebraMap B L x) =
      algebraMap L K' (algebraMap B L y)
    rw [← IsScalarTower.algebraMap_apply B L K',
      ← IsScalarTower.algebraMap_apply B L K', ← C.val.commutes, ← C.val.commutes, h]
  let e : FractionRing B ≃ₐ[B] L :=
    IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) L
  let a : Algebra (FractionRing B) (FractionRing C) :=
    (IsFractionRing.map (K := FractionRing B) (L := FractionRing C) hBinj).toAlgebra
  let : Algebra (FractionRing B) K' :=
    ((algebraMap L K').comp e.toRingHom).toAlgebra
  let j : FractionRing C →+* K' := IsFractionRing.lift (g := C.val.toRingHom) Subtype.val_injective
  have hj : j.comp (algebraMap (FractionRing B) (FractionRing C)) =
      algebraMap (FractionRing B) K' := by
    apply IsFractionRing.ringHom_ext (A := B)
    intro b
    change j (IsFractionRing.map hBinj (algebraMap B (FractionRing B) b)) =
      algebraMap L K' (e (algebraMap B (FractionRing B) b))
    rw [e.commutes]
    change j (IsLocalization.map _ _ _ (algebraMap B (FractionRing B) b)) = _
    rw [IsLocalization.map_eq, IsFractionRing.lift_algebraMap]
    exact C.val.commutes b
  let j' : FractionRing C →ₐ[FractionRing B] K' :=
    { __ := j
      commutes' := fun x ↦ DFunLike.congr_fun hj x }
  have hsep' : Algebra.IsSeparableExtension (FractionRing B) K' :=
    separable_baseEquiv e.toRingEquiv rfl hsep
  have hC := Algebra.exists_nonempty_open_regular_of_separable_fractionRing B C
    hBinj (separable_of_injective j' hsep') hBreg
  exact RingHom.exists_nonempty_regular_open_of_finiteType S C g.toRingHom hinj
    (show g.toRingHom.FiniteType from inferInstanceAs (Algebra.FiniteType S C)) hC
