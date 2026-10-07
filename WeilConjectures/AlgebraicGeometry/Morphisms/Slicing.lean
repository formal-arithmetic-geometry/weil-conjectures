/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Slicing a smooth morphism

A smooth morphism `f : X ⟶ S` becomes, after an étale covering of `X`, a smooth morphism of
affine schemes with geometrically connected fibres and a section, over a scheme étale over `S`
(Stacks `0EY4`).

The proof follows Stacks. In each fibre of `f` the closed points with finite separable residue
field are dense (Stacks `056U`), and through each of them passes an étale slice `ι : Z ⟶ X`,
that is, `ι ≫ f` is étale (Stacks `057G`). The base change `X ×_S Z ⟶ Z` then has a section,
whose relative connected component is open with geometrically irreducible fibres (Stacks `055R`).
The projection to `X` maps connected components of fibres onto connected components, so these
relative components cover `X`. A second slicing after shrinking to an affine open makes all the
schemes affine.

## Main statements

- `AlgebraicGeometry.Smooth.exists_mem_etale_residueFieldMap`: in every fibre of a smooth
  morphism, the points with finite separable residue field extension are dense.
- `AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap`: through a point with
  finite separable residue field extension passes an étale slice.
- `AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section`: the relative connected
  component of a section of a smooth morphism is open, with geometrically irreducible fibres.
- `AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`: the slicing near one point.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the slicing of a smooth morphism.

## References

- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
- Stacks Project, Tags `056U`, `057G`, `055R`
-/

@[expose] public section

universe u

open CategoryTheory Limits

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
  -- the residue field of `x` is finite separable over `κ(s)`
  have key : (e ≫ b).hom.Etale := by
    let _ : Algebra (S.residueField s) ((f.fiber s).residueField y) := a.toAlgebra
    let _ := (e ≫ b).hom.toAlgebra
    let φ : X.residueField (f.fiberι s y) →ₐ[S.residueField s] (f.fiber s).residueField y :=
      { toRingHom := c.hom
        commutes' := fun r ↦ by
          change c.hom ((e ≫ b).hom r) = a r
          rw [hac]
          rfl }
    have : Algebra.Etale (S.residueField s) ((f.fiber s).residueField y) :=
      RingHom.etale_algebraMap.mp hy
    have : Algebra.IsSeparable (S.residueField s) ((f.fiber s).residueField y) :=
      (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
    have : Module.Finite (S.residueField s) ((f.fiber s).residueField y) :=
      Algebra.FormallyUnramified.finite_of_free _ _
    have : Algebra.IsSeparable (S.residueField s) (X.residueField (f.fiberι s y)) :=
      Algebra.IsSeparable.of_algHom _ _ φ
    have : Module.Finite (S.residueField s) (X.residueField (f.fiberι s y)) :=
      Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
    exact RingHom.etale_algebraMap.mpr .of_finite_of_isSeparable
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

/-- **Étale slices** (Stacks `057G`). Let `f : X ⟶ S` be smooth and let `x : X` have finite
separable residue field over `κ(f x)`, so that `x` is a closed point of its fibre. Then there is
an affine scheme `Z`, a point `z : Z` and a morphism `ι : Z ⟶ X` through `x` such that `ι ≫ f`
is étale. -/
@[stacks 057G]
theorem Smooth.exists_etale_comp_of_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] {x : X} (hx : (f.residueFieldMap x).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (z : Z), IsAffine Z ∧ Etale (ι ≫ f) ∧ ι z = x :=
  sorry

/-- **The relative connected component of a section** (Stacks `055R`, `055P`). Let `g : P ⟶ T`
be smooth with a section `σ`. The points `p` lying in the connected component of `σ (g p)` in
their fibre form an open `P⁰` of `P`, here an open `U` containing them. Its fibres over `T` are
the connected components through the rational points `σ t` of the smooth fibres, hence
geometrically connected and, being smooth, geometrically irreducible. -/
@[stacks 055R]
theorem Smooth.exists_geometricallyIrreducible_of_section {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : P.Opens, Set.range σ ⊆ U ∧ GeometricallyIrreducible (U.ι ≫ g) ∧
      ∀ p : P, p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p)) → p ∈ U :=
  sorry

/-- **Slicing a smooth morphism at a point.** Let `f : X ⟶ S` be smooth and `x : X`. Then there
are an étale `p : U ⟶ X` with `x` in its image and a factorisation `p ≫ f = q ≫ r` with
`r : V ⟶ S` étale and `q : U ⟶ V` a smooth morphism of affine schemes with geometrically connected
fibres and a section.

The proof follows Stacks `0EY4`. Choose `x'` in the connected component of `x` in its fibre with
`κ(x')` finite separable over `κ(f x)`, and an étale slice `ι : Z ⟶ X` through `x'`. The base
change `X ×_S Z ⟶ Z` has the section `(ι, 𝟙)`, whose relative connected component `P₀` is open
with geometrically irreducible fibres, and contains a point over `x` because the projection maps
connected components of fibres onto connected components. Finally an affine open `A` of `P₀`
around that point is smooth with geometrically irreducible fibres over its open image `T`, and a
second étale slice `ι' : Z' ⟶ A` provides the section of `A ×_T Z' ⟶ Z'`. -/
theorem Smooth.exists_etale_factorization_of_mem {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Smooth q ∧ IsAffine U ∧ IsAffine V ∧
      GeometricallyConnected q ∧ (∃ s : V ⟶ U, s ≫ q = 𝟙 V) ∧ q ≫ r = p ≫ f := by
  -- a point `x'` with finite separable residue field in the connected component of `x`
  obtain ⟨W, hxW, hW⟩ := f.exists_opens_inter_preimage_subset_connectedComponentIn x
  obtain ⟨x', hx'W, hfx', hx'⟩ := Smooth.exists_mem_etale_residueFieldMap f W hxW
  have hxx' : x ∈ connectedComponentIn (f ⁻¹' {f x}) x' := by
    rw [← connectedComponentIn_eq (hW ⟨hx'W, hfx'⟩)]
    exact mem_connectedComponentIn rfl
  -- an étale slice `ι : Z ⟶ X` through `x'`, and the section `σ` of `X ×_S Z ⟶ Z`
  obtain ⟨Z, ι, z, hZ, hιf, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap f hx'
  let σ : Z ⟶ pullback f (ι ≫ f) := pullback.lift ι (𝟙 Z) (by rw [Category.id_comp])
  have hσ : σ ≫ pullback.snd f (ι ≫ f) = 𝟙 Z := pullback.lift_snd _ _ _
  rw [← hfx'] at hxx'
  have hσz : pullback.snd f (ι ≫ f) (σ z) = z := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  have hσx : pullback.fst f (ι ≫ f) (σ z) = ι z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨p₀, hp₀, hp₀x⟩ := connectedComponentIn_subset_image_pullback_fst f (ι ≫ f) (σ z) hσz
    (by rwa [hσx, Scheme.Hom.comp_apply])
  have hp₀z : pullback.snd f (ι ≫ f) p₀ = z := 
    connectedComponentIn_subset (pullback.snd f (ι ≫ f) ⁻¹' {z}) _ hp₀
  -- the relative connected component `P₀` of `σ`
  obtain ⟨P₀, -, hP₀, hP₀'⟩ :=
    Smooth.exists_geometricallyIrreducible_of_section (pullback.snd f (ι ≫ f)) σ hσ
  have hp₀P₀ : p₀ ∈ P₀ := hP₀' p₀ (by rwa [hp₀z])
  -- an affine open `A` of `P₀` around `p₀`, and its open image `T` in `Z`
  set h := P₀.ι ≫ pullback.snd f (ι ≫ f)
  obtain ⟨A, hA, hp₀A, -⟩ := exists_isAffineOpen_mem_and_subset (X := P₀.toScheme) (U := ⊤)
    (x := (⟨p₀, hp₀P₀⟩ : P₀.toScheme)) trivial
  let T : Z.Opens := ⟨h '' A, h.isOpenMap _ A.2⟩
  have hAT : A ≤ h ⁻¹ᵁ T := fun a ha ↦ ⟨a, ha, rfl⟩
  let k := h.resLE T A hAT
  have : IsAffine A := hA
  have : Surjective k := ⟨by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, Subtype.ext (by simp [k, -Scheme.Hom.comp_base])⟩⟩
  have : GeometricallyIrreducible k := by
    have : Surjective (P₀.toScheme.homOfLE hAT ≫ h ∣_ T) := ‹Surjective k›
    exact inferInstanceAs (GeometricallyIrreducible (P₀.toScheme.homOfLE hAT ≫ h ∣_ T))
  -- a second étale slice `ι' : Z' ⟶ A`, through a point of the fibre of `A ⟶ T` containing `p₀`
  obtain ⟨a', -, hka', ha'⟩ :=
    Smooth.exists_mem_etale_residueFieldMap k ⊤ (x := ⟨⟨p₀, hp₀P₀⟩, hp₀A⟩) trivial
  obtain ⟨Z', ι', z', hZ', hι'k, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap k ha'
  have : IsAffineHom (k ≫ T.ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  have : IsAffineHom k := IsAffineHom.of_comp k T.ι
  refine ⟨pullback k (ι' ≫ k), pullback.fst _ _ ≫ A.ι ≫ P₀.ι ≫ pullback.fst f (ι ≫ f), Z',
    pullback.snd _ _, ι' ≫ k ≫ T.ι ≫ ι ≫ f, inferInstance, ?_, ?_, inferInstance,
    inferInstance, hZ', inferInstance,
    ⟨pullback.lift ι' (𝟙 Z') (Category.id_comp _).symm, pullback.lift_snd _ _ _⟩, ?_⟩
  · obtain ⟨u, hu, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := k) (g := ι' ≫ k)
      ⟨⟨p₀, hp₀P₀⟩, hp₀A⟩ z' (by simpa using hka'.symm)
    exact ⟨u, by simp [hu, hp₀x]⟩
  · have : Etale (ι' ≫ k ≫ T.ι) := by
      rw [← Category.assoc]
      infer_instance
    rw [← Category.assoc, ← Category.assoc]
    infer_instance
  · have H := pullback.condition (f := f) (g := ι ≫ f)
    rw [← Category.assoc ι' k, ← pullback.condition_assoc]
    simp only [k, h, Scheme.Hom.resLE_comp_ι_assoc, Category.assoc] at H ⊢
    rw [← H]

/-- **Slicing a smooth morphism** (blueprint `sbc-lem-slicing`). Let `f : X ⟶ S` be smooth.
Then there is an étale covering `p i : U i ⟶ X` of `X` such that each composite `p i ≫ f`
factors as `q i ≫ r i` with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` a smooth morphism of
affine schemes with geometrically connected fibres admitting a section:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```

This is Stacks `0EY4`, assembled pointwise from
`AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`. -/
@[stacks 0EY4]
theorem Smooth.exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Smooth (q i)) ∧ (∀ i, IsAffine (U i)) ∧
      (∀ i, IsAffine (V i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) := by
  choose U p V q r hp hx hr hq hU hV hqc hs hqr using Smooth.exists_etale_factorization_of_mem f
  exact ⟨X, U, p, V, q, r, hp, fun x ↦ ⟨x, hx x⟩, hr, hq, hU, hV, hqc, hs, hqr⟩

end AlgebraicGeometry
