/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Sober
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism

import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.RingTheory.StrictHenselizationIrreducibleTransport
import WeilConjectures.RingTheory.UnramifiedInjectiveUnibranchEtale

/-! # Pointwise dominant unramified morphisms are etale

Source: Stacks Project, More on Morphisms, Tag 0GS8,
lemma-unramified-dominant-unibranch-is-etale
(blueprint: lem-dl-a1-pointwise-unramified-dominant-etale).

The image point `x` is written as `f z`. Geometric unibranchness at that point is
expressed by irreducibility of the spectrum of a strict henselization of its stalk.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type morphism to an integral scheme, geometrically unibranch at
`f z`, is etale at `z` if it is unramified there and `z` has a generalization over the
generic point. The strict henselization is supplied with its recorded colimit presentation.

Source: Stacks Project, More on Morphisms, Tag 0GS8, with the algebraic argument of
More on Algebra, Tag 0GSC expanded
(blueprint: lem-dl-a1-pointwise-unramified-dominant-etale).

Proof:
1. Choose affine charts around f z and z. Their section map is finite type, and its
   prime localizations are the stalk map. The open-immersion diagonal of the given
   unramified neighbourhood makes its stalk map formally unramified. Compose with
   the inverse open-restriction stalk isomorphism to obtain formal unramifiedness
   for the original stalk map. The affine stalk identifications and localization
   then give formal unramifiedness of B_q over A.
2. The generalization z' is in the affine source chart. Its prime q' is contained
   in q and contracts to zero because f z' is generic in the integral target.
   If a maps to zero in B_q, some s outside q annihilates its image in B. Since
   s is outside q', primality puts the image of a in q', so a = 0.
3. Identify the target stalk with A_(q ∩ A) by the universal property of
   localization. Transport irreducibility of the chosen strict henselization
   to every presentation at that localization using
   lem-dl-a1-strict-henselization-irreducible-transport.
4. Apply lem-dl-a1-unramified-injective-unibranch-etale to obtain g outside q
   with B[1/g] etale over A. Its spectrum is the principal neighbourhood of z
   in the source chart. The localization algebra equivalence identifies its
   ring map with the restriction of f. The affine etale criterion and composition
   with the target open immersion give the asserted etale neighbourhood. -/
theorem etale_at_of_pointwise_unramified_dominant
    {Z X : Scheme.{u}} (f : Z ⟶ X) (z : Z) [IsIntegral X] [LocallyOfFiniteType f]
    (K H : Type (max u v)) [Field K]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk (f z))) K]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk (f z))) K]
    [Algebra (X.presheaf.stalk (f z)) K]
    [IsScalarTower (X.presheaf.stalk (f z))
      (IsLocalRing.ResidueField (X.presheaf.stalk (f z))) K]
    [CommRing H] [Algebra (X.presheaf.stalk (f z)) H]
    (_P : Algebra.StrictHenselizationPresentationIn.{u, v} (X.presheaf.stalk (f z)) K H)
    [IrreducibleSpace (PrimeSpectrum H)]
    (_hdominant : ∃ z' : Z, z' ⤳ z ∧ IsGenericPoint (f z') Set.univ)
    (_hunramified : ∃ U : Z.Opens, z ∈ U ∧ IsUnramified (U.ι ≫ f)) :
    ∃ U : Z.Opens, z ∈ U ∧ Etale (U.ι ≫ f) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, e⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hfxU (f ⁻¹ᵁ U).isOpen
  let A := Γ(X, U)
  let B := Γ(Z, V)
  let := (f.appLE U V e).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f z, e hzV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
  have : Nonempty U := ⟨⟨f z, e hzV⟩⟩
  have : IsDomain A := inferInstance
  have : Algebra.FiniteType A B := f.finiteType_appLE hU hV e
  have hqp : q.under A = p :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hzV).1)
  have hunram : (f.stalkMap z).hom.FormallyUnramified := by
    obtain ⟨O, hzO, _, hd⟩ := _hunramified
    have := hd
    have : FormallyUnramified (O.ι ≫ f) := inferInstance
    let y : O := ⟨z, hzO⟩
    have h := FormallyUnramified.stalkMap (O.ι ≫ f) y
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at h
    have h' := h.comp (RingHom.FormallyUnramified.of_surjective
      (ConcreteCategory.bijective_of_isIso (O.stalkIso y).hom).2)
    change ((f.stalkMap z ≫ O.ι.stalkMap y) ≫ (O.stalkIso y).hom).hom.FormallyUnramified at h'
    rw [Category.assoc, ← Scheme.Opens.stalkIso_inv, Iso.inv_hom_id,
      Category.comp_id] at h'
    exact h'
  have : q.LiesOver p := ⟨hqp.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hu : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV e hzV)).mp hunram
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    .of_isLocalization p.primeCompl
  have : Algebra.IsUnramifiedAt A q :=
    Algebra.FormallyUnramified.comp A (Localization.AtPrime p) _
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) := by
    obtain ⟨z', hz'z, hgen⟩ := _hdominant
    have hz'V : z' ∈ V := hz'z.mem_open V.isOpen hzV
    let q' := hV.primeIdealOf ⟨z', hz'V⟩
    have hle : q'.asIdeal ≤ q := by
      apply (PrimeSpectrum.le_iff_specializes _ _).mpr
      exact (Topology.IsInducing.subtypeVal.specializes_iff.mp hz'z).map hV.isoSpec.hom.continuous
    have hzero : q'.asIdeal.under A = ⊥ := by
      have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hz'V
      have hz' : f z' = genericPoint X := hgen.eq (genericPoint_spec X)
      have hgp : hU.primeIdealOf ⟨f z', e hz'V⟩ = (⊥ : PrimeSpectrum A) := by
        have hx : (⟨f z', e hz'V⟩ : U) =
            ⟨genericPoint X, hz' ▸ e hz'V⟩ := Subtype.ext hz'
        rw [hx]
        simpa only [genericPoint_eq_bot_of_affine] using hU.primeIdealOf_genericPoint
      exact congr($(h.trans hgp).1)
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    have ha' : algebraMap B (Localization.AtPrime q) (algebraMap A B a) = 0 := by
      simpa only [← IsScalarTower.algebraMap_apply] using ha
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl
      (Localization.AtPrime q) (algebraMap A B a)).mp ha'
    have has : algebraMap A B a ∈ q'.asIdeal :=
      (q'.isPrime.mem_or_mem_of_mul_eq_zero hs).resolve_left (fun h ↦ s.2 (hle h))
    have : a ∈ q'.asIdeal.under A := has
    simpa only [hzero, Ideal.mem_bot] using this
  let := X.presheaf.algebra_section_stalk ⟨f z, e hzV⟩
  have := hU.isLocalization_stalk ⟨f z, e hzV⟩
  let ep : X.presheaf.stalk (f z) ≃+* Localization.AtPrime (q.under A) :=
    IsLocalization.ringEquivOfRingEquiv
      (M := p.primeCompl) (T := (q.under A).primeCompl)
      (X.presheaf.stalk (f z)) (Localization.AtPrime (q.under A))
      (RingEquiv.refl A) (by
        change p.primeCompl.map (MonoidHom.id A) = (q.under A).primeCompl
        rw [Submonoid.map_id]
        ext a
        change a ∉ p ↔ a ∉ q.under A
        rw [hqp])
  have hgeom := Algebra.irreducible_strictHenselization_of_equiv
    (X.presheaf.stalk (f z)) (Localization.AtPrime (q.under A)) ep K H _P
  obtain ⟨g, hg, hge⟩ :=
    Algebra.exists_etale_away_of_unramified_injective_unibranch A B q hinj hgeom
  let W := Z.basicOpen g
  have hW : IsAffineOpen W := hV.basicOpen g
  have hzW : z ∈ W := by
    have hmem : hV.primeIdealOf ⟨z, hzV⟩ ∈ PrimeSpectrum.basicOpen g := hg
    rw [← hV.fromSpec_preimage_basicOpen] at hmem
    change hV.fromSpec (hV.primeIdealOf ⟨z, hzV⟩) ∈ Z.basicOpen g at hmem
    rwa [hV.fromSpec_primeIdealOf] at hmem
  have heW : W ≤ f ⁻¹ᵁ U := (Z.basicOpen_le g).trans e
  have hres : Etale (f.resLE U W heW) := by
    have : IsAffine (Scheme.Opens.toScheme U) := hU
    have : IsAffine W.toScheme := hW
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    apply (RingHom.Etale.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U W heW)).mpr
    let := (f.appLE U W heW).hom.toAlgebra
    have := hge
    have := hV.isLocalization_basicOpen g
    have : IsScalarTower A B Γ(Z, W) := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      change (f.appLE U W heW) r =
        (Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op) ((f.appLE U V e) r)
      exact congr($(f.appLE_map e (homOfLE (Z.basicOpen_le g)).op) r).symm
    rw [← RingHom.algebraMap_toAlgebra (f.appLE U W heW).hom,
      RingHom.etale_algebraMap]
    exact Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
        Γ(Z, W)).restrictScalars A)
  have : Etale ((f.resLE U W heW) ≫ Scheme.Opens.ι U) :=
    MorphismProperty.comp_mem @Etale _ _ hres inferInstance
  exact ⟨W, hzW, by simpa only [Scheme.Hom.resLE_comp_ι] using this⟩

end AlgebraicGeometry
