/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-!
# Étale morphisms lift locally along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and `p : W ⟶ Z` an étale morphism. Then `W` is,
in a neighbourhood of any of its points, the base change along `i` of a scheme étale over `X`.

This is the geometric counterpart of the ring theoretic statement that a standard étale algebra
over a quotient `R ⧸ I` is the base change of a standard étale algebra over `R`
(`Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor`): everything is local on `X` and on
`W`, so the lift is produced inside a single affine chart and no gluing is involved.

## Main results

- `AlgebraicGeometry.Etale.exists_isPullback_of_isClosedImmersion`: for every point `w` of `W`
  there is an open neighbourhood `W₀` of `w` in `W` and an étale morphism `q : V ⟶ X` such that
  `W₀` is the fibre product `V ×[X] Z`, compatibly with `p`.
- `AlgebraicGeometry.Etale.exists_pullback_hom_of_isClosedImmersion`: the pointed form. Given a
  morphism `s : Spec Ω ⟶ W` with `Ω` a field — in the application a geometric point of `W` — there
  is an étale `q : V ⟶ X` and a morphism `V ×[X] Z ⟶ W` over `Z` through which `s` factors.

We also record that for an étale morphism `q : V ⟶ Spec B` and an affine open `W` of `V`, the
induced ring map `B →+* Γ(V, W)` is étale
(`AlgebraicGeometry.IsAffineOpen.etale_ringHomOfSpec`), and deduce the pointed affine form
`AlgebraicGeometry.Etale.exists_algebraMap_hom_of_point`: a scheme étale over `Spec B` is, in
a neighbourhood of any of its points with values in a field, `Spec` of an étale `B`-algebra.
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

/-- The ring map `B →+* Γ(V, W)` induced by an affine open `W` of `V` is étale if
`q : V ⟶ Spec B` is, since `Spec` of it is `Spec Γ(V, W) ⟶ V ⟶ Spec B` and the first map is an
open immersion. -/
lemma IsAffineOpen.etale_ringHomOfSpec {B : Type u} [CommRing B] {V : Scheme.{u}}
    (q : V ⟶ Spec (.of B)) [Etale q] {W : V.Opens} (hW : IsAffineOpen W) :
    (hW.ringHomOfSpec q).Etale := by
  have : Etale (Spec.map (CommRingCat.ofHom (hW.ringHomOfSpec q))) := by
    rw [hW.SpecMap_ringHomOfSpec q]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp this

/-- **A scheme étale over `Spec B` is affine and étale over `B` near a point.** For an étale
morphism `q : V ⟶ Spec B` and a morphism `pt : Spec Ω ⟶ V` with `Ω` a field there is an étale
`B`-algebra `C` and a morphism `j : Spec C ⟶ V` over `Spec B` through which `pt` factors:
```
Spec Ω --pt--→ V --------q--------→ Spec B
      ╲        ↑                      ↑
        ╲      j                      ‖
   Spec ψ ↘    |                      ‖
             Spec C --Spec (algebraMap B C)--→ Spec B
```
-/
theorem Etale.exists_algebraMap_hom_of_point {B : Type u} [CommRing B] {V : Scheme.{u}}
    (q : V ⟶ Spec (.of B)) [Etale q] {Ω : Type u} [Field Ω] (pt : Spec (.of Ω) ⟶ V) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Algebra.Etale B C)
      (j : Spec (.of C) ⟶ V) (ψ : C →+* Ω),
      j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap B C)) ∧
        Spec.map (CommRingCat.ofHom ψ) ≫ j = pt := by
  obtain ⟨W, hW, hpt, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V) (x := pt.base default) (U := ⊤) trivial
  have hrange : Set.range pt.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hpt
  let _ : Algebra B Γ(V, W) := (hW.ringHomOfSpec q).toAlgebra
  refine ⟨Γ(V, W), inferInstance, inferInstance,
    RingHom.etale_algebraMap.mp (hW.etale_ringHomOfSpec q), hW.fromSpec,
    (Spec.preimage (IsOpenImmersion.lift hW.fromSpec pt hrange)).hom,
    (hW.SpecMap_ringHomOfSpec q).symm, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry
