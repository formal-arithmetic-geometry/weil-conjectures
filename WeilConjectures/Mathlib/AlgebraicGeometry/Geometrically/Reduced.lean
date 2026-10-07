/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Morphisms with geometrically reduced fibres

Three facts about morphisms whose geometric fibres are reduced.

The first is that a smooth morphism has geometrically reduced fibres: its geometric fibres
are smooth varieties, hence regular, hence reduced. Together with the instances
`Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` of
`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, this is what makes a smooth morphism
satisfy the hypotheses of the statements below and of degree-zero flat base change.

The second is that precomposing with an étale morphism preserves geometrically reduced fibres,
an étale scheme over a reduced scheme being reduced. It makes the hypotheses of the third
statement stable under passing to the objects of the small étale site of the source.

The third is the étale-local slicing of such a morphism: a flat morphism, locally of
finite presentation, with geometrically reduced fibres admits an étale covering of its
source along which it factors through an étale morphism to the base, the remaining leg
being flat, locally of finite presentation, affine, with geometrically connected fibres
and admitting a section. The covering is recorded as an index type together with a jointly
surjective family of étale morphisms rather than as a bundled `Scheme.OpenCover`, since
the members of an étale cover are not open subschemes of the source.

## Main statements

- `AlgebraicGeometry.isReduced_of_smooth`: a scheme smooth over a field is reduced.
- `AlgebraicGeometry.Smooth.geometricallyReduced`: a smooth morphism has geometrically
  reduced fibres.
- `AlgebraicGeometry.GeometricallyReduced.comp_of_etale`: an étale morphism followed by a
  morphism with geometrically reduced fibres has geometrically reduced fibres.
- `AlgebraicGeometry.exists_etaleCover_factorization`: the étale-local slicing of a flat,
  locally finitely presented morphism with geometrically reduced fibres.
- `AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`: the étale-local slicing of a
  smooth morphism near a single point.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the étale-local slicing of a
  smooth morphism, through smooth morphisms of affine schemes.

## References

- Stacks Project, More on Morphisms, Lemma 37.46.3,
  <https://stacks.math.columbia.edu/tag/0EY5>
- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme `X` smooth over a field `K` is reduced: on an affine open cover, the rings of
sections are smooth `K`-algebras, which are reduced by `Algebra.Smooth.isReduced_of_field`. -/
theorem isReduced_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] : IsReduced X := by
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) := by
    have : Smooth (X.affineCover.f i ≫ f) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineCover.f i ≫ f)
    have : Smooth (Spec.map φ) := by rwa [hφ]
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at this
    algebraize [φ.hom]
    exact (affine_isReduced_iff _).mpr (Algebra.Smooth.isReduced_of_field K _)
  exact IsReduced.of_openCover X X.affineCover

/-- **Smooth morphisms have geometrically reduced fibres** (blueprint
`sbc-lem-smooth-geometrically-reduced`). For a field `K` and `Spec K ⟶ S`, the base change
`X ×_S Spec K` is smooth over `Spec K` (Stacks `01VB`), hence reduced (Stacks `056T`, here
`AlgebraicGeometry.isReduced_of_smooth`). -/
instance Smooth.geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  exact isReduced_of_smooth (Limits.pullback.snd f y)

/-- An étale morphism followed by a morphism with geometrically reduced fibres has
geometrically reduced fibres: for a field `K` and `Spec K ⟶ Z`, the scheme `X ×_Z Spec K` is
étale over the reduced scheme `Y ×_Z Spec K`, and a scheme étale over a reduced scheme is
reduced. -/
theorem GeometricallyReduced.comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale f] [GeometricallyReduced g] : GeometricallyReduced (f ≫ g) :=
  sorry

/-- Let `f : X ⟶ S` be flat, locally of finite presentation and with geometrically reduced
fibres. Then there is an étale covering `p i : U i ⟶ X` of `X`, that is, a family of étale
morphisms whose images cover `X`, such that each composite `p i ≫ f` factors as `q i ≫ r i`
with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` flat, locally of finite presentation and
affine, with geometrically connected fibres, and admitting a section:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```

A smooth morphism satisfies the hypotheses, by `AlgebraicGeometry.Smooth.geometricallyReduced`
and the instances `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation`; that special
case is Stacks `0EY4`, in which the first leg `q i` is moreover smooth. -/
@[stacks 0EY5]
theorem exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Flat (q i)) ∧ (∀ i, LocallyOfFinitePresentation (q i)) ∧
      (∀ i, IsAffineHom (q i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) :=
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
  obtain ⟨Z, ι, z, hZ, -, hιf, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap f hx'
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
  obtain ⟨Z', ι', z', hZ', -, hι'k, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap k ha'
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
