/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Ideal.GoingUp
import Sheaf.AlgebraicGeometry.FiniteAffineSectionCover
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite
import Sheaf.RingTheory.WLocalStalkIsomorphismRetraction

/-! # Finite algebras over extremally disconnected affine schemes -/

@[expose] public section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Pullback

/-- The residue-field calculation used in the pointwise pullback step below. An algebraic
extension of a separably closed field is purely inseparable; its tensor-product spectrum
is therefore homeomorphic to the spectrum of the other field. -/
private theorem subsingleton_primeSpectrum_tensor_of_isSepClosed
    (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsSepClosed k] [Algebra.IsAlgebraic k K] :
    Subsingleton (PrimeSpectrum (K ⊗[k] L)) := by
  have : IsPurelyInseparable k K := inferInstance
  have h := PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
    (K := k) (R := k) (S := L) K
  let e := Algebra.TensorProduct.lid k L
  have he := PrimeSpectrum.isHomeomorph_comap_of_bijective e.toRingEquiv.bijective
  have : Subsingleton (PrimeSpectrum (k ⊗[k] L)) :=
    he.bijective.surjective.subsingleton
  exact h.bijective.injective.subsingleton

/-- A compatible pair of scheme points has at most one lift when the indicated residue
extension is integral over a separably closed field. -/
private theorem tripletTensor_subsingleton {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (t : Scheme.Pullback.Triplet f g)
    (hsep : IsSepClosed (Z.residueField t.s))
    (halg : ((Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x).hom.IsIntegral) :
    Subsingleton (Spec t.tensor) := by
  let A := Z.residueField t.s
  let B := X.residueField t.x
  let C := Y.residueField t.y
  let φ := (Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x
  let ψ := (Z.residueFieldCongr t.hy).inv ≫ g.residueFieldMap t.y
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra A C := ψ.hom.toAlgebra
  have : IsSepClosed A := hsep
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp halg
  have : Algebra.IsAlgebraic A B := Algebra.isAlgebraic_iff_isIntegral.mpr inferInstance
  let e : t.tensor ≅ CommRingCat.of (B ⊗[A] C) :=
    IsColimit.coconePointUniqueUpToIso (IsPushout.of_hasPushout φ ψ).isColimit
      (CommRingCat.pushoutCoconeIsColimit A B C)
  have : Subsingleton (PrimeSpectrum (B ⊗[A] C)) :=
    subsingleton_primeSpectrum_tensor_of_isSepClosed A B C
  have he := PrimeSpectrum.isHomeomorph_comap_of_bijective
    e.commRingCatIsoToRingEquiv.bijective
  exact he.bijective.surjective.subsingleton

private theorem pullbackPoint_ext {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsep : ∀ z : Z, IsSepClosed (Z.residueField z))
    (halg : ∀ t : Triplet f g,
      ((Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x).hom.IsIntegral)
    (a b : ↑(Limits.pullback f g)) (ha : pullback.fst f g a = pullback.fst f g b)
    (hb : pullback.snd f g a = pullback.snd f g b) : a = b := by
  apply carrierEquiv.injective
  apply carrierEquiv_eq_iff.mpr
  have heq : (carrierEquiv a).1 = (carrierEquiv b).1 := Triplet.ext ha hb
  refine ⟨heq, ?_⟩
  have : Subsingleton (Spec (carrierEquiv b).1.tensor) :=
    tripletTensor_subsingleton _ (hsep _) (halg _)
  exact Subsingleton.elim _ _

private theorem isClopen_of_isConstructible {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] {s : Set T} (hs : Topology.IsConstructible s) : IsClopen s := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U ho hc => exact ⟨hc.isCompact.isClosed, ho⟩
  | union s hs t ht ihs iht => exact ihs.union iht
  | compl s hs ih => exact ih.compl

private theorem extremallyDisconnected_of_isOpenEmbedding
    {T V : Type*} [TopologicalSpace T] [TopologicalSpace V]
    [ExtremallyDisconnected V] {i : T → V} (hi : Topology.IsOpenEmbedding i) :
    ExtremallyDisconnected T := by
  constructor
  intro U hU
  rw [hi.isEmbedding.isInducing.closure_eq_preimage_closure_image]
  exact (ExtremallyDisconnected.open_closure _ (hi.isOpenMap _ hU)).preimage hi.continuous

private theorem extremallyDisconnected_of_open_cover
    {T : Type*} [TopologicalSpace T] {ι : Type*} (U : ι → Set T)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ x, ∃ i, x ∈ U i)
    (he : ∀ i, ExtremallyDisconnected (U i)) : ExtremallyDisconnected T := by
  constructor
  intro V hV
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨i, hi⟩ := hc x
  have := he i
  have h := ExtremallyDisconnected.open_closure
    (Subtype.val ⁻¹' V : Set (U i)) (hV.preimage continuous_subtype_val)
  rw [← (ho i).isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val V] at h
  have himg := (ho i).isOpenEmbedding_subtypeVal.isOpenMap _ h
  apply Filter.mem_of_superset (himg.mem_nhds ⟨⟨x, hi⟩, hx, rfl⟩)
  rintro y ⟨z, hz, rfl⟩
  exact hz

private theorem t2Space_of_finite {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffine X] [IsAffine Y] [IsFinite f] [T2Space X] : T2Space Y := by
  have hx : T2Space (PrimeSpectrum Γ(X, ⊤)) := X.isoSpec.hom.homeomorph.t2Space
  have hf := f.finite_appTop
  have hy := Spec.profinite_of_isMaximal Γ(Y, ⊤) (fun q hq ↦ by
    have : q.IsPrime := hq
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f.appTop.hom hf.to_isIntegral
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal
      ⟨q.comap f.appTop.hom, inferInstance⟩).mp isClosed_singleton)
  have : T2Space (Spec Γ(Y, ⊤)) := hy.2.1
  exact Y.isoSpec.inv.homeomorph.t2Space

private theorem locallyOfFinitePresentation_of_comp_affine
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
  apply RingHom.FinitePresentation.of_comp_finiteType g.appTop.hom
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      (f ≫ g).finitePresentation_appTop
  · exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

private theorem isClopen_range_of_finitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [T2Space Y]
    [LocallyOfFinitePresentation f] [QuasiCompact f] : IsClopen (Set.range f) := by
  apply isClopen_of_isConstructible
  simpa only [Set.image_univ] using f.isConstructible_image Topology.IsConstructible.univ

private theorem extremallyDisconnected_pullback_of_sections
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B] [T2Space C]
    [ExtremallyDisconnected A]
    (r : B → C) (hr : Continuous r) (σ : A → C) (hσ : Continuous σ)
    {ι : Type*} (V : ι → Set B) (hV : ∀ i, IsClopen (V i))
    (hcover : ∀ b, ∃ i, b ∈ V i)
    (hlocal : ∀ i, Topology.IsOpenEmbedding (fun b : V i ↦ r b)) :
    ExtremallyDisconnected {ba : B × A | r ba.1 = σ ba.2} := by
  let P := {ba : B × A | r ba.1 = σ ba.2}
  have hP : IsClosed {ba : B × A | r ba.1 = σ ba.2} :=
    isClosed_eq (hr.comp continuous_fst) (hσ.comp continuous_snd)
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isCompact
  let U (i : ι) : Set P := {z | z.val.1 ∈ V i}
  have hU (i : ι) : IsClopen (U i) :=
    (hV i).preimage (continuous_fst.comp continuous_subtype_val)
  apply extremallyDisconnected_of_open_cover U (fun i ↦ (hU i).2)
    (fun z ↦ hcover z.val.1)
  intro i
  have : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hU i).1.isCompact
  let D : Set A := σ ⁻¹' Set.range (fun b : V i ↦ r b)
  have hD : IsOpen D := (hlocal i).isOpen_range.preimage hσ
  have : ExtremallyDisconnected D :=
    extremallyDisconnected_of_isOpenEmbedding hD.isOpenEmbedding_subtypeVal
  let e : U i → D := fun z ↦
    ⟨z.val.val.2, ⟨⟨z.val.val.1, z.property⟩, z.val.property⟩⟩
  have hecont : Continuous e :=
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have heinj : Function.Injective e := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hzw : z.val.val.2 = w.val.val.2 := congrArg Subtype.val h
      have : (⟨z.val.val.1, z.property⟩ : V i) = ⟨w.val.val.1, w.property⟩ :=
        (hlocal i).injective (z.val.property.trans (hzw ▸ w.val.property.symm))
      exact congrArg Subtype.val this
    · exact congrArg Subtype.val h
  have hesurj : Function.Surjective e := by
    rintro ⟨a, b, hb⟩
    exact ⟨⟨⟨(b.val, a), hb⟩, b.property⟩, rfl⟩
  let homeo := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective e ⟨heinj, hesurj⟩) hecont
  exact extremallyDisconnected_of_homeo homeo.symm

private theorem openEmbedding_on_preimage_section
    {B C D E : Type*} [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] [TopologicalSpace E]
    (j : B → C) (hj : Topology.IsOpenEmbedding j) (p : C → D)
    (i : E → C) (hi : Topology.IsOpenEmbedding i) (hpi : Topology.IsOpenEmbedding (p ∘ i)) :
    Topology.IsOpenEmbedding (fun b : j ⁻¹' Set.range i ↦ p (j b)) := by
  let e := hi.isEmbedding.toHomeomorph
  let l : (j ⁻¹' Set.range i) → E := fun b ↦ e.symm ⟨j b, b.property⟩
  have hil (b : j ⁻¹' Set.range i) : i (l b) = j b :=
    congrArg Subtype.val (e.apply_symm_apply ⟨j b, b.property⟩)
  have hjl : Topology.IsOpenEmbedding (i ∘ l) := by
    convert hj.comp (hi.isOpen_range.preimage hj.continuous).isOpenEmbedding_subtypeVal
      using 1
    funext b
    exact hil b
  have hl : Topology.IsOpenEmbedding l := hi.of_comp l hjl
  convert hpi.comp hl using 1
  funext b
  exact congrArg p (hil b).symm

set_option backward.isDefEq.respectTransparency false in
/-- Transport finiteness along the canonical affine stalk isomorphisms. -/
private theorem finite_spec_residueFieldMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : PrimeSpectrum S)
    (h : (Ideal.ResidueField.map (x.comap φ.hom).asIdeal x.asIdeal φ.hom rfl).Finite) :
    ((Spec.map φ).residueFieldMap x).hom.Finite := by
  have : IsLocalHom (Spec.stalkIso S x).inv.hom :=
    isLocalHom_of_iso (Spec.stalkIso S x).symm
  have : IsLocalHom (Spec.stalkIso R (x.comap φ.hom)).hom.hom :=
    isLocalHom_of_iso (Spec.stalkIso R (x.comap φ.hom))
  change (IsLocalRing.ResidueField.map ((Spec.map φ).stalkMap x).hom).Finite
  simp only [← Scheme.localRingHom_comp_stalkIso φ x, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rw [IsLocalRing.ResidueField.map_comp, IsLocalRing.ResidueField.map_comp]
  apply RingHom.Finite.comp
  · exact (RingHom.Finite.of_surjective _ (IsLocalRing.ResidueField.mapEquiv
      (Spec.stalkIso S x).symm.commRingCatIsoToRingEquiv).surjective).comp h
  · exact RingHom.Finite.of_surjective _ (IsLocalRing.ResidueField.mapEquiv
      (Spec.stalkIso R (x.comap φ.hom)).commRingCatIsoToRingEquiv).surjective

private theorem finite_residueFieldMap_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [T2Space (PrimeSpectrum S)] (q : PrimeSpectrum S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q).hom.Finite := by
  apply finite_spec_residueFieldMap
  have : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp isClosed_singleton
  let p := (q.comap (algebraMap R S)).asIdeal
  let φ := Ideal.ResidueField.map p q.asIdeal (algebraMap R S) rfl
  let : Algebra p.ResidueField q.asIdeal.ResidueField := φ.toAlgebra
  have : IsScalarTower R p.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (Ideal.ResidueField.map_algebraMap
      p q.asIdeal (algebraMap R S) rfl a).symm
  have : Module.Finite R q.asIdeal.ResidueField := Module.Finite.trans S _
  exact RingHom.finite_algebraMap.mpr (Module.Finite.of_restrictScalars_finite
    R p.ResidueField q.asIdeal.ResidueField)

private theorem isSepClosed_of_ringEquiv {K L : Type*} [Field K] [Field L]
    [IsSepClosed L] (e : K ≃+* L) : IsSepClosed K := by
  constructor
  intro f hf
  have h := (IsSepClosed.splits_of_separable (f.map e.toRingHom) (hf.map)).map
    e.symm.toRingHom
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id K := by
    ext x
    exact e.symm_apply_apply x
  simpa only [Polynomial.map_map, he, Polynomial.map_id] using h

/-- A finite finitely presented algebra over a ring with Hausdorff extremally disconnected
spectrum and separably closed residue fields has extremally disconnected spectrum.
Source: Stacks Project, Lemma 61.11.5 (Tag 0985), finite case
(blueprint: lem-ce-finite-algebra-extremally-disconnected).

Proof: Put X = Spec R and Y = Spec S. The finite affine section-cover theorem
(Tag 03HW) supplies a surjective finite locally free a : X' → X, an affine finite locally
free p : W → X', a closed immersion j : Y' = Y ×_X X' → W over X', and finitely many
closed immersions iₖ : Zₖ → W covering W with iₖ ≫ p isomorphisms.
The affine spaces X', W, Y and Y' are compact Hausdorff: primes above maximal primes
are maximal by integrality, and `Spec.profinite_of_isMaximal` applies.
If a composite of affine morphisms is finitely presented and its second map is of finite
type, its first map is finitely presented by `RingHom.FinitePresentation.of_comp_finiteType`.
Apply this to j ≫ p and to each iₖ ≫ p. Chevalley makes the images of j and iₖ constructible.
In a compact Hausdorff space a constructible set is clopen, by induction on its Boolean
expression in retrocompact opens. Thus j and each iₖ are open embeddings on points.
The clopen sets Vₖ = j⁻¹(image iₖ) cover Y', and Y' → X' restricts to an open embedding
on each Vₖ, since its composite there with the section chart iₖ is an isomorphism.
Projectivity supplies a continuous section σ : X → X' of a. Form the topological pullback
P = {(y',x) | snd(y') = σ(x)}. Above each Vₖ its second projection is a continuous
bijection to the open set σ⁻¹(snd(Vₖ)), hence a homeomorphism by compactness and
Hausdorffness. Open subspaces of extremally disconnected spaces are extremally disconnected,
and this property is local on an open cover. Therefore P is extremally disconnected.
The first projection P → Y is surjective by existence of scheme pullback points.
Its injectivity follows from `pullbackPoint_ext`: finite residue extensions over the
separably closed κ(x) are purely inseparable, so the spectrum of their tensor product
with κ(x') is a singleton. Hence P → Y is a continuous bijection between compact
Hausdorff spaces and is a homeomorphism. Transport extremal disconnectedness along it.
This argument needs neither a disjoint refinement nor equality loci of the sections.
Empty spectra, empty section charts, nilpotents and nonflat finite algebras are included. -/
theorem extremallyDisconnected_spectrum_of_finite_finitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    [T2Space (PrimeSpectrum R)] [ExtremallyDisconnected (PrimeSpectrum R)]
    (hsep : ∀ p : PrimeSpectrum R, IsSepClosed p.asIdeal.ResidueField) :
    ExtremallyDisconnected (PrimeSpectrum S) := by
  classical
  let X : Scheme.{u} := Spec (CommRingCat.of R)
  let Y : Scheme.{u} := Spec (CommRingCat.of S)
  let f : Y ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
    (inferInstance : Module.Finite R S))
  have : LocallyOfFinitePresentation f := (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : T2Space X := (inferInstance : T2Space (PrimeSpectrum R))
  have : ExtremallyDisconnected X :=
    (inferInstance : ExtremallyDisconnected (PrimeSpectrum R))
  have : T2Space Y := t2Space_of_finite f
  have : T2Space (PrimeSpectrum S) := (inferInstance : T2Space Y)
  have hsepX (x : X) : IsSepClosed (X.residueField x) := by
    have := hsep x
    exact isSepClosed_of_ringEquiv
      (Scheme.Spec.residueFieldIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv
  obtain ⟨X', a, hXa, ha, hfa, W, p, j, hW, hfp, hj, hjp,
    ⟨n, Z, i, hi, hcover⟩, _, _⟩ := exists_finite_affine_section_cover f
  have : IsAffine X' := hXa
  have : Surjective a := ha
  have : a.IsFiniteLocallyFree := hfa
  have : IsAffine W := hW
  have : p.IsFiniteLocallyFree := hfp
  have : IsClosedImmersion j := hj
  have : IsAffine (pullback f a) := inferInstance
  have : T2Space X' := t2Space_of_finite a
  have : T2Space W := t2Space_of_finite p
  have : T2Space ↑(Limits.pullback f a) := t2Space_of_finite (pullback.snd f a)
  have : LocallyOfFinitePresentation (j ≫ p) := hjp ▸ inferInstance
  have : LocallyOfFinitePresentation j := locallyOfFinitePresentation_of_comp_affine j p
  have hjopen : Topology.IsOpenEmbedding j :=
    ⟨j.isClosedEmbedding.isEmbedding, (isClopen_range_of_finitePresentation j).2⟩
  have hiopen (k : Fin n) : Topology.IsOpenEmbedding (i k) := by
    have : IsClosedImmersion (i k) := (hi k).1
    have : IsIso (i k ≫ p) := (hi k).2
    have : IsAffine (Z k) := IsAffine.of_isIso (i k ≫ p)
    have : LocallyOfFinitePresentation (i k) :=
      locallyOfFinitePresentation_of_comp_affine (i k) p
    exact ⟨(i k).isClosedEmbedding.isEmbedding,
      (isClopen_range_of_finitePresentation (i k)).2⟩
  obtain ⟨σ, hσ, hσa⟩ := RingHom.exists_continuous_section_of_surjective
    a a.continuous ha.surj
  let V (k : Fin n) : Set ↑(Limits.pullback f a) := j ⁻¹' Set.range (i k)
  have hV (k : Fin n) : IsClopen (V k) := by
    have : IsClosedImmersion (i k) := (hi k).1
    exact ⟨(i k).isClosedEmbedding.isClosed_range.preimage j.continuous,
      (hiopen k).isOpen_range.preimage j.continuous⟩
  have hVc (y' : ↑(Limits.pullback f a)) : ∃ k, y' ∈ V k := by
    obtain ⟨k, z, hz⟩ := hcover (j y')
    exact ⟨k, z, hz⟩
  have hVl (k : Fin n) :
      Topology.IsOpenEmbedding (fun b : V k ↦ pullback.snd f a b) := by
    have : IsIso (i k ≫ p) := (hi k).2
    have h := openEmbedding_on_preimage_section j hjopen p (i k) (hiopen k)
      (i k ≫ p).homeomorph.isOpenEmbedding
    convert h using 1
    funext b
    exact congrArg (fun m : pullback f a ⟶ X' ↦ m b) hjp.symm
  let P := {ba : ↑(Limits.pullback f a) × X | pullback.snd f a ba.1 = σ ba.2}
  have hPclosed : IsClosed
      {ba : ↑(Limits.pullback f a) × X | pullback.snd f a ba.1 = σ ba.2} :=
    isClosed_eq ((pullback.snd f a).continuous.comp continuous_fst)
      (hσ.comp continuous_snd)
  have : CompactSpace P := isCompact_iff_compactSpace.mp hPclosed.isCompact
  have : ExtremallyDisconnected P := extremallyDisconnected_pullback_of_sections
    (pullback.snd f a) (pullback.snd f a).continuous σ hσ V hV hVc hVl
  let b : P → Y := fun z ↦ pullback.fst f a z.val.1
  have hbcont : Continuous b :=
    (pullback.fst f a).continuous.comp (continuous_fst.comp continuous_subtype_val)
  have halg (t : Triplet f a) :
      ((X.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x).hom.IsIntegral := by
    have hf := finite_residueFieldMap_of_finite R S t.x
    exact (hf.comp (RingHom.Finite.of_surjective _
      (X.residueFieldCongr t.hx).commRingCatIsoToRingEquiv.symm.surjective)).to_isIntegral
  have hb_inj : Function.Injective b := by
    intro z w h
    have hx (v : P) : f (b v) = v.val.2 := by
      change (pullback.fst f a ≫ f) v.val.1 = v.val.2
      rw [pullback.condition]
      change a (pullback.snd f a v.val.1) = v.val.2
      rw [v.property, hσa]
    have hxzw : z.val.2 = w.val.2 := (hx z).symm.trans ((congrArg f h).trans (hx w))
    apply Subtype.ext
    apply Prod.ext
    · apply pullbackPoint_ext hsepX halg _ _ h
      exact z.property.trans ((congrArg σ hxzw).trans w.property.symm)
    · exact hxzw
  have hb_surj : Function.Surjective b := by
    intro y
    obtain ⟨y', hy', hx'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := a) y (σ (f y)) (hσa (f y)).symm
    exact ⟨⟨(y', f y), hx'⟩, hy'⟩
  let e := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective b ⟨hb_inj, hb_surj⟩) hbcont
  exact extremallyDisconnected_of_homeo e
