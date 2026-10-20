/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Braided sheaf tensor and its sheafification generators

Source: blueprint `sec-proetale-coefficients`,
`sk-def-sfb-module-pushforward-pullback/lem-sfb-pushforward-comp-monoidal.proof.md`,
first sentence (blueprint: lem-sfb-braided-sheaf-tensor-generators).

The structure below packages the entire conclusion, including the specified tensor
bifunctor, canonical comparisons, and both universal generator tests. No choice of a
monoidal structure is made from an unproved existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe w uA uC vC

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

/-- The data asserted by the braided sheaf tensor lemma, on the prescribed sheafified
pointwise tensor. Source: blueprint `lem-sfb-pushforward-comp-monoidal.proof.md`, first
sentence, expanded by `lem-sfb-braided-sheaf-tensor-generators`, clauses 1--4
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

`tensorObj_eq`, `tensorHom_heq`, and `tensorUnit_eq` prescribe the actual bifunctor
and unit. Heterogeneous equality only transports between the equal objects prescribed
by these equations. `cotensorator_heq` specifies the canonical inverse tensorator,
namely sheafification of the tensor of the two adjunction units. The tensorator is
therefore its unique inverse. `unitComparison_heq` specifies the identity comparison.
The presheaf generator maps used below are exactly `toSheafify`, whose type already
contains naturality in the site variable. -/
structure BraidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] where
  monoidal : MonoidalCategory (Sheaf J A)
  braided : @BraidedCategory (Sheaf J A) _ monoidal
  sheafification :
    @Functor.Braided (Cᵒᵖ ⥤ A) _ _ _ (Sheaf J A) _ monoidal braided
      (presheafToSheaf J A)
  tensorObj_eq : ∀ F G : Sheaf J A,
    monoidal.tensorObj F G = (presheafToSheaf J A).obj (F.obj ⊗ G.obj)
  tensorHom_heq : ∀ {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G'),
    HEq (@tensorHom (Sheaf J A) _ monoidal.toMonoidalCategoryStruct _ _ _ _ f g)
      ((presheafToSheaf J A).map (f.hom ⊗ₘ g.hom))
  tensorUnit_eq : monoidal.tensorUnit = (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A))
  braiding_heq : ∀ F G : Sheaf J A,
    HEq (@BraidedCategory.braiding (Sheaf J A) _ monoidal braided F G).hom
      ((presheafToSheaf J A).map (β_ F.obj G.obj).hom)
  cotensorator_heq : ∀ P Q : Cᵒᵖ ⥤ A,
    HEq (@Functor.OplaxMonoidal.δ (Cᵒᵖ ⥤ A) _ _ (Sheaf J A) _ monoidal
      (presheafToSheaf J A) sheafification.toMonoidal.toOplaxMonoidal P Q)
      ((presheafToSheaf J A).map (toSheafify J P ⊗ₘ toSheafify J Q))
  unitComparison_heq :
    HEq (@Functor.LaxMonoidal.ε (Cᵒᵖ ⥤ A) _ _ (Sheaf J A) _ monoidal
      (presheafToSheaf J A) sheafification.toMonoidal.toLaxMonoidal)
      (𝟙 ((presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A))))
  tensorGenerators_naturality :
    ∀ {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G'),
      (f.hom ⊗ₘ g.hom) ≫ toSheafify J (F'.obj ⊗ G'.obj) =
        toSheafify J (F.obj ⊗ G.obj) ≫
          ((presheafToSheaf J A).map (f.hom ⊗ₘ g.hom)).hom
  tensorHom_bijective : ∀ F G H : Sheaf J A,
    Function.Bijective
      (fun h : (presheafToSheaf J A).obj (F.obj ⊗ G.obj) ⟶ H ↦
        toSheafify J (F.obj ⊗ G.obj) ≫ h.hom)
  unitHom_bijective : ∀ H : Sheaf J A,
    Function.Bijective
      (fun h : (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A)) ⟶ H ↦
        toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ h.hom)
  tensorHom_ext : ∀ (F G H : Sheaf J A)
      (f g : (presheafToSheaf J A).obj (F.obj ⊗ G.obj) ⟶ H),
    toSheafify J (F.obj ⊗ G.obj) ≫ f.hom =
      toSheafify J (F.obj ⊗ G.obj) ≫ g.hom → f = g
  unitHom_ext : ∀ (H : Sheaf J A)
      (f g : (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A)) ⟶ H),
    toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ f.hom =
      toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ g.hom → f = g

/-- Closed braided Grothendieck coefficients give the canonical braided structure on
exactly the sheafified pointwise tensor, together with its two generator tests.
Source: blueprint `lem-sfb-pushforward-comp-monoidal.proof.md`, first sentence
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

Proof. 1. The coefficient tensor, associator, unitors and braiding act pointwise on
presheaves; all coherence equations hold at each object.
2. The sheafification adjunction identifies the Hom-defined local maps with maps
inverted by sheafification. Its unit is local and its counit is invertible, since
sheaves form a full subcategory.
3. Grothendieck coefficients with morphisms in universe `w` have all `w`-small limits
(`lem-coef-grothendieck-small-limits`). The internal-hom end construction and
`lem-sfb-local-equivalences-braided-tensor` show that local maps are stable under
both tensorings, using the braiding without symmetry. In particular the tensor of
two sheafification units becomes invertible after sheafification.
4. The reflector is a localization: a functor inverting local maps extends by
composition with the inclusion, and its unit and counit give inverse equivalences
on the corresponding functor categories, also on natural transformations.
5. Apply `lem-sfb-braided-monoidal-localization` to obtain the localized braided
structure with unit the sheafification of the constant tensor unit.
6. The localization tensor is naturally isomorphic to the prescribed bifunctor
`(F,G) ↦ a(UF ⊗ UG)` via the inverse tensorator followed by the two counits.
Conjugate associators, unitors and braiding by this comparison. On a coherence
path the successive comparison and inverse-comparison factors cancel, reducing
pentagon, triangle and both hexagons to the localized equations.
7. Naturality of the old tensorator and the adjunction triangle identities show
that the new inverse tensorator is `a(η_P ⊗ η_Q)`, the unit comparison is the
identity, and the braiding is `a(β_(UF,UG))`. Transport of the old functor coherence
equations proves that sheafification is strong braided monoidal.
8. The maps `t` and `u` are the actual sheafification units. Their types make them
presheaf natural transformations, and naturality of the adjunction unit at
`Uf ⊗ Ug` gives simultaneous sheaf naturality of `t`. The adjunction Hom equivalence
at `UF ⊗ UG` and at the constant unit gives both displayed bijections. Their
injectivity gives the two equality tests. -/
theorem nonempty_braidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] : Nonempty (BraidedTensorGenerators J A) := by
  sorry

/-- The same assertions for an essentially small site, explicitly after passage to its
small skeleton with the induced topology. Source: blueprint
`lem-sfb-pushforward-comp-monoidal.proof.md`, first sentence; the small-skeleton clause
of `lem-sfb-braided-sheaf-tensor-generators`
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

Proof (step 9 of the node). Take `Skeleton (SmallModel C)`, using
`skeletonEquivalence` and the inverse of
`equivSmallModel C` to include it into the original site. Pull the topology back along
this composite equivalence, and apply the small-site
assertion `nonempty_braidedTensorGenerators` there. All ends and Hom tests are now
indexed in universe `w`; no ends over the original large object type are required. -/
theorem nonempty_braidedTensorGenerators_smallSkeleton
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A] :
    Nonempty (BraidedTensorGenerators
      (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A) := by
  sorry

end CategoryTheory.Sheaf
