/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.RingTheory.Etale.ResidueField
public import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Étale slices of a smooth morphism

Ingredients of the slicing of a smooth morphism (Stacks `0EY4`), which is
`AlgebraicGeometry.Smooth.exists_etaleCover_factorization` in
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingSmooth`. In each fibre of a smooth morphism
`f : X ⟶ S` the closed points with finite separable residue field are dense (Stacks `056U`), and
through each of them passes an étale slice `ι : Z ⟶ X`, that is, `ι ≫ f` is étale (Stacks
`057G`).

## Main statements

- `AlgebraicGeometry.Smooth.exists_mem_etale_residueFieldMap`: in every fibre of a smooth
  morphism, the points with finite separable residue field extension are dense.
- `AlgebraicGeometry.AffineSpace.exists_etale_comp_of_etale_residueFieldMap`: étale slices of
  affine space.
- `AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap`: through a point with
  finite separable residue field extension passes an étale slice.

## References

- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
- Stacks Project, Tags `056U`, `057G`
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

/-- A point of the fibre of `f` over `s` whose residue field is finite separable over `κ(s)`
maps to a point of `X` whose residue field is finite separable over `κ(s)`. -/
lemma Scheme.Hom.etale_residueFieldMap_fiberι {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (y : f.fiber s) (hy : ((f.fiberToSpecResidueField s).residueFieldAlgebraMap y).Etale) :
    (f.residueFieldMap (f.fiberι s y)).hom.Etale := by
  have h : f (f.fiberι s y) = s := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  let a := (f.fiberToSpecResidueField s).residueFieldAlgebraMap y
  let e := (S.residueFieldCongr h.symm).hom
  let b := f.residueFieldMap (f.fiberι s y)
  let c := (f.fiberι s).residueFieldMap y
  have hac : a = (e ≫ b ≫ c).hom := by
    have h1 : Spec.map (CommRingCat.ofHom a) ≫ S.fromSpecResidueField s =
        (f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s ≫
          S.fromSpecResidueField s :=
      (congrArg (· ≫ S.fromSpecResidueField s)
        ((f.fiberToSpecResidueField s).specMap_residueFieldAlgebraMap y)).trans
        (Category.assoc _ _ _)
    have h2 : Spec.map (e ≫ b ≫ c) ≫ S.fromSpecResidueField s =
        (f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s ≫
          S.fromSpecResidueField s := by
      rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
        S.residueFieldCongr_fromSpecResidueField h.symm,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Scheme.Hom.fiber_fac]
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective ((cancel_mono (S.fromSpecResidueField s)).mp (h1.trans h2.symm)))
  -- the residue field of `f.fiberι s y` is finite separable over `κ(s)`
  have key : (e ≫ b).hom.Etale := by
    refine RingHom.Etale.of_comp_of_field (e ≫ b).hom c.hom ?_
    rw [← CommRingCat.hom_comp, Category.assoc, ← hac]
    exact hy
  have hb : b.hom = (e ≫ b).hom.comp
      (S.residueFieldCongr h).commRingCatIsoToRingEquiv.toRingHom := by
    ext r
    change b.hom r = b.hom (((S.residueFieldCongr h).hom ≫ (S.residueFieldCongr h).inv).hom r)
    rw [Iso.hom_inv_id]
    rfl
  change b.hom.Etale
  rw [hb]
  exact RingHom.Etale.respectsIso.2 _ _ key

/-- **Density of separable points** (Stacks `056U`). Let `f : X ⟶ S` be smooth. Every open
`U` of `X` meeting the fibre through `x` contains a point `x'` of that fibre whose residue field
is finite separable over `κ(f x)`, that is, `κ(f x) ⟶ κ(x')` is étale. This is
`AlgebraicGeometry.Scheme.Hom.dense_setOf_isClosed_finite_isSeparable` applied to the fibre,
which is smooth over `κ(f x)`. -/
@[stacks 056U]
theorem Smooth.exists_mem_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ x' ∈ U, f x' = f x ∧ (f.residueFieldMap x').hom.Etale := by
  have : Smooth (f.fiberToSpecResidueField (f x)) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hd := @Scheme.Hom.dense_setOf_isClosed_finite_isSeparable _
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x))) _ (f.fiberToSpecResidueField (f x)) this
  obtain ⟨y, hyU, -, hy⟩ := hd.inter_open_nonempty
      (f.fiberι (f x) ⁻¹ᵁ U) (f.fiberι (f x) ⁻¹ᵁ U).2
      ⟨f.asFiber x, by simpa [Scheme.Hom.fiberι_asFiber] using hx⟩
  refine ⟨f.fiberι _ y, hyU, ?_, f.etale_residueFieldMap_fiberι y ?_⟩
  · rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  · let _ := ((f.fiberToSpecResidueField (f x)).residueFieldAlgebraMap y).toAlgebra
    obtain ⟨_, _⟩ := hy
    exact RingHom.etale_algebraMap.mpr .of_finite_of_isSeparable

/-- Let `w` be a point of the affine space `𝔸(n; U)` over an affine scheme `U`, `n` finite, whose
residue field is finite separable over that of its image in `U`. Then some affine scheme `Z`,
étale over `U`, maps to `𝔸(n; U)` over `U` with `w` in its image. -/
theorem AffineSpace.exists_etale_comp_of_etale_residueFieldMap {n : Type u} [Finite n]
    {U : Scheme.{u}} [IsAffine U] (w : 𝔸(n; U))
    (hw : ((𝔸(n; U) ↘ U).residueFieldMap w).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ 𝔸(n; U)) (z : Z), IsAffine Z ∧ Etale (ι ≫ (𝔸(n; U) ↘ U)) ∧
      ι z = w := by
  set iso := AffineSpace.isoOfIsAffine n U
  let φ : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of (MvPolynomial n Γ(U, ⊤)) :=
    CommRingCat.ofHom C
  have hE : 𝔸(n; U) ↘ U = iso.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over, Iso.hom_inv_id_assoc]
  set q := iso.hom w
  have : q.asIdeal.IsPrime := q.2
  have hq : ((Spec.map φ).residueFieldMap q).hom.Etale := by
    rw [Scheme.Hom.etale_residueFieldMap_congr hE,
      Scheme.Hom.etale_residueFieldMap_comp_iff_left,
      Scheme.Hom.etale_residueFieldMap_comp_iff_right] at hw
    exact hw
  have : ((Spec.map φ) q).asIdeal.IsPrime := ((Spec.map φ) q).2
  have h := Spec.residueFieldMap_residueFieldIso_hom φ q
  have h' := (RingHom.Etale.respectsIso.cancel_right_isIso _
    (Scheme.Spec.residueFieldIso _ q).hom).mpr hq
  rw [← CommRingCat.hom_comp, h, CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso] at h'
  obtain ⟨B, _, _, _, ψ, Q, _, hQ⟩ := MvPolynomial.exists_etale_comap_eq q.asIdeal _ _ h'
  refine ⟨Spec (.of B), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ iso.inv, ⟨Q, ‹_›⟩,
    inferInstance, ?_, ?_⟩
  · have hψ : CommRingCat.ofHom C ≫ CommRingCat.ofHom ψ.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(U, ⊤) B) := by
      ext r
      exact ψ.commutes r
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) B))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    rw [Category.assoc, AffineSpace.isoOfIsAffine_inv_over, ← Category.assoc, ← Spec.map_comp,
      hψ]
    infer_instance
  · have hz : Spec.map (CommRingCat.ofHom ψ.toRingHom) ⟨Q, ‹_›⟩ = q := PrimeSpectrum.ext hQ
    change iso.inv (Spec.map (CommRingCat.ofHom ψ.toRingHom) ⟨Q, ‹_›⟩) = w
    rw [hz]
    change (iso.hom ≫ iso.inv) w = w
    simp

/-- **Étale slices** (Stacks `057G`). Let `f : X ⟶ S` be smooth and let `x : X` have finite
separable residue field over `κ(f x)`, so that `x` is a closed point of its fibre. Then there is
an affine scheme `Z`, a point `z : Z` and a morphism `ι : Z ⟶ X` through `x` such that `ι ≫ f`
is étale.

By the normal form `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus`,
`X` is near `x` étale over an affine space `𝔸ⁿ_U`, and the image of `x` there still has finite
separable residue field over `U`. For affine space the slice is
`AlgebraicGeometry.AffineSpace.exists_etale_comp_of_etale_residueFieldMap`, and it pulls back to
`X`. -/
@[stacks 057G]
theorem Smooth.exists_etale_comp_of_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] {x : X} (hx : (f.residueFieldMap x).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (z : Z), IsAffine Z ∧ Etale (ι ≫ f) ∧ ι z = x := by
  obtain ⟨d, U, V, hU, hV, -, hxV, hVU, e, he, hge⟩ :=
    f.exists_etale_to_affineSpace_of_mem_smoothLocus (x := x)
      (by rw [f.smoothLocus_eq_top]; trivial)
  have : IsAffine U := hU
  have : IsAffine V := hV
  let x₀ : V.toScheme := ⟨x, hxV⟩
  set π := 𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme
  -- the residue field of `x₀` is finite separable over that of its image in `U`
  have h0 : ((f.resLE U V hVU).residueFieldMap x₀).hom.Etale := by
    rw [← Scheme.Hom.etale_residueFieldMap_comp_iff_right _ U.ι,
      Scheme.Hom.etale_residueFieldMap_congr (Scheme.Hom.resLE_comp_ι f hVU),
      Scheme.Hom.etale_residueFieldMap_comp_iff_left]
    exact hx
  rw [← hge, Scheme.residueFieldMap_comp] at h0
  have hw := RingHom.Etale.of_comp_of_field (π.residueFieldMap (e x₀)).hom
    (e.residueFieldMap x₀).hom h0
  obtain ⟨Z₀, ι₀, z₀, hZ₀, hι₀, hz₀⟩ :=
    AffineSpace.exists_etale_comp_of_etale_residueFieldMap _ hw
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := ι₀) x₀ z₀ hz₀.symm
  refine ⟨pullback e ι₀, pullback.fst e ι₀ ≫ V.ι, z, inferInstance, ?_, by simp [hz, x₀]⟩
  have : pullback.fst e ι₀ ≫ V.ι ≫ f = pullback.snd e ι₀ ≫ (ι₀ ≫ π) ≫ U.ι := by
    rw [← Scheme.Hom.resLE_comp_ι f hVU, ← hge]
    simp only [Category.assoc]
    rw [pullback.condition_assoc]
  rw [Category.assoc, this]
  infer_instance

end AlgebraicGeometry
