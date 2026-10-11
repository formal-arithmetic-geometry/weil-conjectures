/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
public import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Slicing a smooth morphism

A smooth morphism `f : X ⟶ S` becomes, after an étale covering of `X`, a smooth morphism of
affine schemes with geometrically connected fibres and a section, over a scheme étale over `S`
(Stacks `0EY4`, blueprint `sbc-lem-slicing`).

The proof follows Stacks. In each fibre of `f` the closed points with finite separable residue
field are dense (Stacks `056U`), and through each of them passes an étale slice `ι : Z ⟶ X`,
that is, `ι ≫ f` is étale (Stacks `057G`); see
`AlgebraicGeometry.Smooth.exists_mem_etale_residueFieldMap` and
`AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap`. The base change
`X ×_S Z ⟶ Z` then has a section, whose relative connected component is open (Stacks `055R`,
`AlgebraicGeometry.isOpen_setOf_mem_connectedComponentIn_preimage_singleton`) with geometrically
connected, hence, being smooth, geometrically irreducible fibres. The projection to `X` maps
connected components of fibres onto connected components, so these relative components cover
`X`. A second slicing after shrinking to an affine open makes all the schemes affine.

## Main statements

- `AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section`: the relative connected
  component of a section of a smooth morphism of affine schemes is open, with geometrically
  irreducible fibres.
- `AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`: the slicing near one point.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the slicing of a smooth morphism.

## References

- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
- Stacks Project, Tags `055R`, `04KV`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **The relative connected component of a section** (Stacks `055R`). Let `g : P ⟶ T` be a
smooth morphism of affine schemes with a section `σ`. The points `p` lying in the connected
component of `σ (g p)` in their fibre form an open `U` of `P`
(`AlgebraicGeometry.isOpen_setOf_mem_connectedComponentIn_preimage_singleton`, as `g` is flat of
finite presentation with geometrically reduced fibres). Its fibres over `T` are the connected
components through the rational points `σ t` of the fibres, hence geometrically connected
(Stacks `04KV`) and, being smooth, geometrically irreducible. -/
@[stacks 055R]
theorem Smooth.exists_geometricallyIrreducible_of_section {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [IsAffine P] [IsAffine T] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : P.Opens, Set.range σ ⊆ U ∧ GeometricallyIrreducible (U.ι ≫ g) ∧
      ∀ p : P, p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p)) → p ∈ U := by
  have := GeometricallyReduced.of_smooth g
  have hgσ (t : T) : g (σ t) = t := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  let U : P.Opens := ⟨{p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))},
    isOpen_setOf_mem_connectedComponentIn_preimage_singleton g σ hσ⟩
  have hU (t : T) : (U : Set P) ∩ g ⁻¹' {t} = connectedComponentIn (g ⁻¹' {t}) (σ t) := by
    ext p
    refine ⟨fun ⟨hp, hpt⟩ ↦ ?_, fun hp ↦ ?_⟩
    · obtain rfl : g p = t := hpt
      exact hp
    · obtain rfl : g p = t := connectedComponentIn_subset (g ⁻¹' {t}) _ hp
      exact ⟨hp, rfl⟩
  have hσU : Set.range σ ⊆ U := by
    rintro _ ⟨t, rfl⟩
    refine (hU t).ge (mem_connectedComponentIn ?_) |>.1
    simp [hgσ]
  -- the fibres of `U ⟶ T` are connected with a rational point, hence geometrically connected
  have : GeometricallyConnected (U.ι ≫ g) := by
    refine GeometricallyConnected.of_isPreconnected_preimage_singleton _
      (IsOpenImmersion.lift U.ι σ (by rwa [Scheme.Opens.range_ι]))
      (by rw [IsOpenImmersion.lift_fac_assoc, hσ]) fun t ↦ ?_
    rw [← U.ι.isOpenEmbedding.isInducing.isPreconnected_image, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι, Set.inter_comm, hU]
    exact isPreconnected_connectedComponentIn
  exact ⟨U, hσU, GeometricallyIrreducible.of_smooth_of_geometricallyConnected _, fun p hp ↦ hp⟩

/-- The slicing of a smooth morphism `f` near a point, for `X` and `S` affine; see
`AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`. -/
private theorem exists_etale_factorization_of_mem_aux {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsAffine X] [IsAffine S] (x : X) :
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

/-- **Slicing a smooth morphism at a point.** Let `f : X ⟶ S` be smooth and `x : X`. Then there
are an étale `p : U ⟶ X` with `x` in its image and a factorisation `p ≫ f = q ≫ r` with
`r : V ⟶ S` étale and `q : U ⟶ V` a smooth morphism of affine schemes with geometrically connected
fibres and a section.

After shrinking `X` and `S` to affine opens, the proof follows Stacks `0EY4`. Choose `x'` in the
connected component of `x` in its fibre with `κ(x')` finite separable over `κ(f x)`, and an
étale slice `ι : Z ⟶ X` through `x'`. The base change `X ×_S Z ⟶ Z` has the section `(ι, 𝟙)`,
whose relative connected component `P₀` is open with geometrically irreducible fibres, and
contains a point over `x` because the projection maps connected components of fibres onto
connected components. Finally an affine open `A` of `P₀`
around that point is smooth with geometrically irreducible fibres over its open image `T`, and a
second étale slice `ι' : Z' ⟶ A` provides the section of `A ×_T Z' ⟶ Z'`. -/
theorem Smooth.exists_etale_factorization_of_mem {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Smooth q ∧ IsAffine U ∧ IsAffine V ∧
      GeometricallyConnected q ∧ (∃ s : V ⟶ U, s ≫ q = 𝟙 V) ∧ q ≫ r = p ≫ f := by
  obtain ⟨S', hS', hxS', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
  obtain ⟨X', hX', hxX', hX'S'⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ S') (x := x) hxS'
  have : IsAffine S' := hS'
  have : IsAffine X' := hX'
  obtain ⟨U, p, V, q, r, hp, ⟨u, hu⟩, hr, hq, hU, hV, hqc, hs, hqr⟩ :=
    exists_etale_factorization_of_mem_aux (f.resLE S' X' hX'S') ⟨x, hxX'⟩
  refine ⟨U, p ≫ X'.ι, V, q, r ≫ S'.ι, inferInstance, ⟨u, by simp [hu]⟩, inferInstance, hq, hU,
    hV, hqc, hs, ?_⟩
  rw [← Category.assoc, hqr, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

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

This is Stacks `0EY4`, the smooth case of the slicing in blueprint `sk-prop-normal-form`,
assembled pointwise from
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
