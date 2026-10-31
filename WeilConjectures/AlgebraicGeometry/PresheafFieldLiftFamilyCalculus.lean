/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Field-extension lifting calculus for families of presheaves

Source: Stacks Project, Topologies on Algebraic Spaces, Tag 041F, parts (1)-(3),
with the field-valued point conventions preceding Properties of Spaces, Tag 03BU
(blueprint: lem-trf-presheaf-field-lift-family-calculus).

The statement uses the field-extension lifting predicate on arbitrary presheaves.
For base change, Mathlib's `PullbackCone.combine` assembles the explicit type-level
compatible-pair cones, so the presheaf has exactly the specified objectwise values.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Field-extension lifting is preserved by isomorphisms, composition of families,
and objectwise compatible-pair pullbacks. The last clause uses `Types.pullbackCone`
whose points are pairs with equal images, and `PullbackCone.combine` whose maps are
restriction of both coordinates. There are no sheaf, representability or étale hypotheses.
Source: Stacks Project, Tag 041F, parts (1)-(3), and the field-valued representatives
preceding Tag 03BU (blueprint: lem-trf-presheaf-field-lift-family-calculus).

Proof:
(1) For a field-valued section of `F`, evaluate `e.inv` to obtain its preimage in `G`.
Use the unique singleton index, the same field, and its identity embedding. The inverse
identity and the presheaf identity law give the required equality.
(2) Apply `IsJointlySurjective` to the outer family to lift over an extension `K → L`.
Apply the inner family's lifting condition to that section over `L`, obtaining an index
and a lift over `L → M`. Use their composite embedding and the corresponding sigma index.
The spectrum map reverses composition, so the two induced base maps to `S` agree.
Naturality and the presheaf composition law identify the image with restriction to `M`.
Both successive extension fields remain in the fixed test universe.
(3) The explicit type pullback consists of compatible pairs. Naturality shows that
restriction of both coordinates preserves compatibility; identity and composition hold
coordinatewise, and first projection commutes with restriction. These are the cones and
restriction maps assembled by `PullbackCone.combine`. For a section `x'` over a field,
lift `a(x')` using the original family's condition. Naturality identifies its restriction
with `a` of the restriction of `x'`. Pair that restricted section with the lift to obtain
a compatible pair. Its first projection is the required restriction of `x'`.
(4) Empty index sets cause no exception: the empty family's lifting condition forces
all target field-valued sections to be absent. An empty inner index similarly forbids
the corresponding outer lift. For an empty base-changed family, a target section would
map to a forbidden section of the original target. No field-valued point of `S` is assumed.
All lifting steps use [def-trf-algebraic-space-jointly-surjective-family]; the remaining
steps are inverse identities, naturality, and functor laws. -/
theorem presheaf_field_lift_family_calculus (S : Scheme.{u}) :
    (∀ (F G : (Over S)ᵒᵖ ⥤ Type u) (e : G ≅ F),
      IsJointlySurjective (fun _ : Unit ↦ e.hom)) ∧
    (∀ (I : Type v) (J : I → Type w) (F : (Over S)ᵒᵖ ⥤ Type u)
      (G : I → (Over S)ᵒᵖ ⥤ Type u)
      (H : ∀ i : I, J i → (Over S)ᵒᵖ ⥤ Type u)
      (f : ∀ i : I, G i ⟶ F) (g : ∀ (i : I) (j : J i), H i j ⟶ G i),
      IsJointlySurjective f → (∀ i : I, IsJointlySurjective (g i)) →
        IsJointlySurjective (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1)) ∧
    (∀ (I : Type v) (F F' : (Over S)ᵒᵖ ⥤ Type u)
      (G : I → (Over S)ᵒᵖ ⥤ Type u)
      (f : ∀ i : I, G i ⟶ F) (a : F' ⟶ F),
      IsJointlySurjective f →
        IsJointlySurjective (fun i : I ↦
          (PullbackCone.combine a (f i)
            (fun T ↦ Types.pullbackCone (a.app T) ((f i).app T))
            (fun T ↦ (Types.pullbackLimitCone (a.app T) ((f i).app T)).isLimit)).fst)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F G e K _ s x
    refine ⟨(), K, inferInstance, RingHom.id K, ?_⟩
    refine ⟨e.inv.app _ (F.map
      (Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.id K))) rfl).op x), ?_⟩
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app _) _
  · intro I J F G H f g hf hg K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hf K s x
    obtain ⟨j, M, hM, d, z, hz⟩ := hg i L _ y
    let r₁ : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk s :=
      Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
    change (f i).app _ y = F.map r₁.op x at hy
    let r₂ : Over.mk (Spec.map (CommRingCat.ofHom d) ≫
        Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ Over.mk (Spec.map
          (CommRingCat.ofHom e) ≫ s) :=
      Over.homMk (Spec.map (CommRingCat.ofHom d)) rfl
    let r : Over.mk (Spec.map (CommRingCat.ofHom (d.comp e)) ≫ s) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom d) ≫
          Spec.map (CommRingCat.ofHom e) ≫ s) :=
      Over.homMk (𝟙 _) (by
        change Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom e) ≫ s =
          Spec.map (CommRingCat.ofHom (d.comp e)) ≫ s
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc])
    refine ⟨⟨i, j⟩, M, hM, d.comp e, (H i j).map r.op z, ?_⟩
    change (f i).app _ ((g i j).app _ ((H i j).map r.op z)) = _
    have hn (A B : (Over S)ᵒᵖ ⥤ Type u) (t : A ⟶ B)
        {T U : (Over S)ᵒᵖ} (q : T ⟶ U) (a : A.obj T) :
        t.app U (A.map q a) = B.map q (t.app T a) :=
      ConcreteCategory.congr_hom (t.naturality q) a
    rw [hn _ _ (g i j) r.op z, hz,
      hn _ _ (f i) r.op _, hn _ _ (f i) r₂.op _, hy]
    rw [← types_comp_apply, ← F.map_comp,
      ← types_comp_apply, ← F.map_comp]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom d) ≫
      Spec.map (CommRingCat.ofHom e)) = Spec.map (CommRingCat.ofHom (d.comp e))
    rw [Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  · intro I F F' G f a hf K _ s x
    obtain ⟨i, L, hL, e, y, hy⟩ := hf K s (a.app _ x)
    refine ⟨i, L, hL, e, ?_⟩
    refine ⟨⟨⟨F'.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x, y⟩,
      ?_⟩, rfl⟩
    rw [hy]
    exact ConcreteCategory.congr_hom (a.naturality _) x

end AlgebraicGeometry.AlgebraicSpace
