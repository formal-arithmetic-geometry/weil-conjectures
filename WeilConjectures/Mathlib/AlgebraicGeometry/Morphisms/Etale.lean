/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.Topology.Sets.Opens

/-!
# Two facts about étale morphisms

## Lifting along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `p : W ⟶ Z` an étale morphism. Then `W` is,
in a neighbourhood of any of its points, the base change along `i` of a scheme étale over `X`.

This is the geometric counterpart of the ring theoretic statement that a standard étale algebra
over a quotient `R ⧸ I` is the base change of a standard étale algebra over `R`
(`Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor`): everything is local on `X` and on
`W`, so the lift is produced inside a single affine chart and no gluing is involved.

## Étale covers of a normal scheme with separably closed function field

Let `S` be an integral normal scheme whose function field is separably closed, and let
`p : V ⟶ S` be separated and étale. Then `V` is a disjoint union of open subschemes of `S`. This
is rendered as: there is an index type `ι` and a family of opens `U : ι → V.Opens` which are
pairwise disjoint, cover `V`, and are such that each composite `(U i).ι ≫ p` is an open
immersion. Normality of `S` is not a notion available in Mathlib at the level of schemes, so it
is taken as the explicit hypothesis that every stalk of `S` is integrally closed; together with
`[IsIntegral S]` this says exactly that `S` is an integral normal scheme.

## Main results

- `AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`: for every point `w` of `W`
  there is an open neighbourhood `W₀` of `w` in `W` and an étale morphism `q : V ⟶ X` such that
  `W₀` is the fibre product `V ×[X] Z`, compatibly with `p`.
- `AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`: the pointed form. Given a
  morphism `s : Spec Ω ⟶ W` with `Ω` a field — in the application a geometric point of `W` — there
  is an étale `q : V ⟶ X` and a morphism `V ×[X] Z ⟶ W` over `Z` through which `s` factors.
- `AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: a
  separated étale scheme over an integral normal base with separably closed function field is a
  disjoint union of opens of the base.
- `AlgebraicGeometry.Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField`: the
  same statement with finitely many pieces when the source is quasi-compact.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- **Étale morphisms lift locally along a closed immersion.** If `i : Z ⟶ X` is a closed
immersion and `p : W ⟶ Z` is étale, then every point `w` of `W` has an open neighbourhood `W₀`
which is the base change along `i` of a scheme `V` étale over `X`, in a way compatible with `p`:
the square
```
W₀ ------- a -------> V
|                     |
W₀.ι ≫ p              q
↓                     ↓
Z ------- i --------> X
```
is cartesian. -/
theorem Etale.exists_isPullback_of_isClosedImmersion {X Z W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (p : W ⟶ Z) [Etale p] (w : W) :
    ∃ W₀ : W.Opens, w ∈ W₀ ∧ ∃ (V : Scheme.{u}) (q : V ⟶ X) (_ : Etale q)
      (a : W₀.toScheme ⟶ V), IsPullback a (W₀.ι ≫ p) q i := by
  -- an affine chart `U` of `X` around the image of `w`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := i.base (p.base w)) (U := ⊤) trivial
  -- an affine chart `W'` of `W` around `w`, mapping into the preimage of `U`
  obtain ⟨W', hW', hwW', hW'le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W) (x := w) (U := p ⁻¹ᵁ (i ⁻¹ᵁ U)) hxU
  replace hW'le : W' ≤ p ⁻¹ᵁ (i ⁻¹ᵁ U) := hW'le
  -- the closed immersion `i ⁻¹ᵁ U ⟶ U ≅ Spec Γ(X, U)` presents `i ⁻¹ᵁ U` as `Spec (Γ(X, U) ⧸ I)`
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := (i ∣_ U) ≫ hU.isoSpec.hom)).mp
    inferInstance
  -- the restriction of `p` to the two charts, read as a homomorphism `Γ(X, U) ⧸ I ⟶ Γ(W, W')`
  let ψ : CommRingCat.of (↥Γ(X, U) ⧸ I) ⟶ Γ(W, W') :=
    Spec.preimage (hW'.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le ≫ e.hom)
  have hψ : Spec.map ψ = hW'.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le ≫ e.hom :=
    Spec.map_preimage _
  have hψet : Etale (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  let _ : Algebra (↥Γ(X, U) ⧸ I) ↥Γ(W, W') := ψ.hom.toAlgebra
  have : Algebra.Etale (↥Γ(X, U) ⧸ I) ↥Γ(W, W') := HasRingHomProperty.Spec_iff.mp hψet
  -- shrink `W'` to a basic open on which `Γ(W, -)` is standard étale over `Γ(X, U) ⧸ I`, and
  -- lift that standard étale algebra to `Γ(X, U)`
  obtain ⟨a, ha, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := ↥Γ(X, U) ⧸ I) (hW'.primeIdealOf ⟨w, hwW'⟩).asIdeal
  obtain ⟨T, _, _, hT, ⟨E⟩⟩ := Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor
    (R := ↥Γ(X, U)) (Localization.Away a) I
  have hw₀ : w ∈ W.basicOpen a := by
    have : hW'.primeIdealOf ⟨w, hwW'⟩ ∈ hW'.fromSpec ⁻¹ᵁ W.basicOpen a := by
      rwa [hW'.fromSpec_preimage_basicOpen a]
    rwa [Scheme.Hom.mem_preimage, hW'.fromSpec_primeIdealOf ⟨w, hwW'⟩] at this
  have hloc : IsLocalization.Away a ↥Γ(W, W.basicOpen a) := hW'.isLocalization_basicOpen a
  -- `Γ(W, W.basicOpen a)` is the base change of `T` along `Γ(X, U) ⟶ Γ(X, U) ⧸ I`
  let ε : ((↥Γ(X, U) ⧸ I) ⊗[↥Γ(X, U)] T) ≃+* ↥Γ(W, W.basicOpen a) :=
    E.toRingEquiv.trans
      (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a)
        ↥Γ(W, W.basicOpen a)).toRingEquiv
  have hε : ∀ x : ↥Γ(X, U) ⧸ I, ε (algebraMap _ _ x) =
      (W.presheaf.map (homOfLE (W.basicOpen_le a)).op).hom (ψ.hom x) := by
    intro x
    change (IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a)
        ↥Γ(W, W.basicOpen a)) (E (algebraMap _ _ x)) = _
    rw [E.commutes, IsScalarTower.algebraMap_apply (↥Γ(X, U) ⧸ I) ↥Γ(W, W') (Localization.Away a),
      AlgEquiv.commutes]
    rfl
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(X, U) (↥Γ(X, U) ⧸ I)))
      (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T))
      (ψ ≫ W.presheaf.map (homOfLE (W.basicOpen_le a)).op)
      (CommRingCat.ofHom
        (ε.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ↥Γ(X, U))
          (A := ↥Γ(X, U) ⧸ I) (B := T)).toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct ↥Γ(X, U) (↥Γ(X, U) ⧸ I) T).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ε.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      simpa using hε x
    · ext x
      simp
  have hW₀ : IsAffineOpen (W.basicOpen a) := hW'.basicOpen a
  have hle : W.basicOpen a ≤ p ⁻¹ᵁ (i ⁻¹ᵁ U) := (W.basicOpen_le a).trans hW'le
  -- passing to `Spec` turns the restriction `Γ(W, W') ⟶ Γ(W, W.basicOpen a)` into the inclusion
  have h1 : Spec.map (W.presheaf.map (homOfLE (W.basicOpen_le a)).op) ≫ hW'.isoSpec.inv
      = hW₀.isoSpec.inv ≫ W.homOfLE (W.basicOpen_le a) := by
    rw [← cancel_epi hW₀.isoSpec.hom, ← Category.assoc, IsAffineOpen.isoSpec_hom,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
    simp
  -- hence the left hand vertical map of the affine square is the restriction of `p`
  have hkey : Spec.map (ψ ≫ W.presheaf.map (homOfLE (W.basicOpen_le a)).op)
      = hW₀.isoSpec.inv ≫ p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle ≫ e.hom := by
    have h2 : W.homOfLE (W.basicOpen_le a) ≫ p.resLE (i ⁻¹ᵁ U) W' hW'le
        = p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle := Scheme.Hom.map_resLE _ _ _
    rw [Spec.map_comp, hψ, ← Category.assoc, h1, Category.assoc, ← Category.assoc _ _ e.hom, h2]
  have hqet : Etale (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  -- the affine square, transported along the charts
  have hsq : IsPullback
      (hW₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (ε.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ↥Γ(X, U))
          (A := ↥Γ(X, U) ⧸ I) (B := T)).toRingHom)))
      (p.resLE (i ⁻¹ᵁ U) (W.basicOpen a) hle)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(X, U) T)) ≫ hU.isoSpec.inv)
      (i ∣_ U) := by
    refine ((isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip).of_iso
      hW₀.isoSpec.symm (Iso.refl _) e.symm hU.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · rw [hkey]
      simp
    · simp
    · simp only [Iso.symm_hom, Ideal.Quotient.algebraMap_eq]
      rw [eq_comm, Iso.inv_comp_eq, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  -- paste with the cartesian square expressing `i ⁻¹ᵁ U = Z ×[X] U`
  have hpaste := hsq.paste_vert (isPullback_morphismRestrict i U)
  rw [Scheme.Hom.resLE_comp_ι] at hpaste
  exact ⟨W.basicOpen a, hw₀, Spec (CommRingCat.of T), _, inferInstance, _, hpaste⟩

/-- The pointed form of `AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`: if
`i : Z ⟶ X` is a closed immersion, `p : W ⟶ Z` is étale and `s : Spec Ω ⟶ W` is a point of `W`
with values in a field `Ω`, then there is an étale morphism `q : V ⟶ X` together with a morphism
`g : V ×[X] Z ⟶ W` over `Z` through which `s` factors. -/
theorem Etale.exists_pullback_hom_of_isClosedImmersion {X Z W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (p : W ⟶ Z) [Etale p] {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ W) :
    ∃ (V : Scheme.{u}) (q : V ⟶ X) (_ : Etale q) (g : pullback q i ⟶ W),
      g ≫ p = pullback.snd q i ∧
        ∃ t : Spec (CommRingCat.of Ω) ⟶ pullback q i, t ≫ g = s := by
  obtain ⟨W₀, hw₀, V, q, hq, α, hpb⟩ :=
    Etale.exists_isPullback_of_isClosedImmersion i p (s.base default)
  have hrange : Set.range s.base ⊆ Set.range W₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hw₀
  refine ⟨V, q, hq, hpb.isoPullback.inv ≫ W₀.ι, ?_,
    IsOpenImmersion.lift W₀.ι s hrange ≫ hpb.isoPullback.hom, ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Category.assoc, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

/-- An étale morphism `p : V ⟶ S` into an integral normal scheme `S` with separably closed
function field is a local isomorphism: every point of `V` has an open neighbourhood mapping
isomorphically onto an open of `S`. Normality of `S` is the hypothesis `hS` that every stalk of
`S` is integrally closed.

Over affine charts `Spec A ⊆ S` and `Spec B ⊆ V` this is
`Algebra.Etale.exists_algHom_localizationAway_comap_eq`: every point of `Spec B` lies on a
section of `Spec B → Spec A` over a basic open of `Spec A`, and a section of an étale morphism
over an open is an open immersion (`AlgebraicGeometry.FormallyUnramified.isOpenImmersion_of_comp`).
-/
theorem Etale.isLocalIso_of_isSepClosed_functionField {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [Etale p] : IsLocalIso p := by
  refine ⟨fun x ↦ ?_⟩
  -- affine charts `U ∋ p x` of `S` and `W ∋ x` of `V` with `W ⊆ p ⁻¹ U`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := p.base x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V) (x := x) (U := p ⁻¹ᵁ U) hxU
  replace hWle : W ≤ p ⁻¹ᵁ U := hWle
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : IsIntegrallyClosed Γ(S, U) :=
    Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk hS U
  have : IsFractionRing Γ(S, U) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S U hU
  let _ : Algebra Γ(S, U) Γ(V, W) := (p.appLE U W hWle).hom.toAlgebra
  have : Algebra.Etale Γ(S, U) Γ(V, W) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.appLE @Etale p ‹_› ⟨U, hU⟩ ⟨W, hW⟩ hWle)
  -- the point `x` lies on a section `σ` of `p` over a basic open of `U`
  obtain ⟨a, ψ, P, hP, hPq⟩ := Algebra.Etale.exists_algHom_localizationAway_comap_eq
    (A := Γ(S, U)) S.functionField (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  let j : Spec (.of (Localization.Away a)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Localization.Away a))) ≫ hU.fromSpec
  let σ : Spec (.of (Localization.Away a)) ⟶ V :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec
  have hσ : σ ≫ p = j := by
    simp only [σ, j, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW hWle,
      ← Spec.map_comp_assoc]
    congr 2
    ext y
    exact ψ.commutes y
  have : IsOpenImmersion (σ ≫ p) := by
    rw [hσ]
    infer_instance
  have : IsOpenImmersion σ := FormallyUnramified.isOpenImmersion_of_comp p σ
  refine ⟨σ.opensRange, ⟨⟨P, hP⟩, ?_⟩, ?_⟩
  · have h1 : (Spec.map (CommRingCat.ofHom ψ.toRingHom)).base ⟨P, hP⟩ =
        hW.primeIdealOf ⟨x, hxW⟩ := PrimeSpectrum.ext hPq
    simp only [σ, Scheme.Hom.comp_base, TopCat.comp_app, h1]
    exact hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  · rw [← σ.isoOpensRange_inv_comp, Category.assoc, hσ]
    infer_instance

/-- **Étale covers of a normal scheme with separably closed function field**
(blueprint `sbc-lem-etale-over-normal`). Let `S` be an integral normal scheme — normality being
the hypothesis `hS` that every stalk of `S` is integrally closed — with separably closed function
field. Then

1. every separated étale morphism `p : V ⟶ S` is a disjoint union of open immersions: there are
  nonempty, pairwise disjoint opens `U i` covering `V` with every `(U i).ι ≫ p` an open
  immersion;
2. every local ring of `S` is strictly henselian: it is henselian with separably closed residue
  field. -/
@[stacks 09Z9]
theorem Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk {S : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] :
    (∀ (V : Scheme.{u}) (p : V ⟶ S) [IsSeparated p] [Etale p],
      ∃ (ι : Type u) (U : ι → V.Opens), (∀ i, (U i : Set V).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ i, U i) = ⊤ ∧
        ∀ i, IsOpenImmersion ((U i).ι ≫ p)) ∧
      ∀ x : S, HenselianLocalRing (S.presheaf.stalk x) ∧ IsSepClosed (S.residueField x) := by
  refine ⟨fun V p _ _ ↦ ?_, fun x ↦ ⟨Scheme.henselianLocalRing_stalk_of_isSepClosed_functionField
    hS x, Scheme.isSepClosed_residueField_of_isSepClosed_functionField hS x⟩⟩
  have := Etale.isLocalIso_of_isSepClosed_functionField hS p
  exact IsLocalIso.exists_opens_isOpenImmersion p

/-- **Étale covers of a normal scheme with separably closed function field.** Let `S` be an
integral normal scheme — normality being spelled out as the hypothesis `hS` that every stalk of
`S` is integrally closed — whose function field `S.functionField` is separably closed, and let
`p : V ⟶ S` be separated and étale. Then `V` is the disjoint union of a family of opens `U i`
each of which maps isomorphically onto an open of `S`. -/
@[stacks 09Z9]
theorem Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] :
    ∃ (ι : Type u) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) := by
  obtain ⟨ι, U, -, hU⟩ :=
    (Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk hS).1 V p
  exact ⟨ι, U, hU⟩

/-- The quasi-compact refinement of
`AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: if `V` is
in addition quasi-compact, then finitely many opens suffice. -/
@[stacks 09Z9]
theorem Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] [CompactSpace V] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) := by
  obtain ⟨ι, U, hne, hdisj, hcov, hU⟩ :=
    (Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk hS).1 V p
  exact ⟨ι, TopologicalSpace.Opens.finite_of_compactSpace_of_pairwiseDisjoint U hne hdisj hcov,
    U, hdisj, hcov, hU⟩

end AlgebraicGeometry
