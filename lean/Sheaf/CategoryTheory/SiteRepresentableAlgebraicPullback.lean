/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteInverseImageTensor
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Yoneda

/-!
# Normalized inverse image of represented diagrams

Source: Stacks Project, Sites and Sheaves, Tag 04D3,
`lemma-pullback-representable-sheaf`, expanded by adjunction and Yoneda
(blueprint: lem-pur-site-representable-algebraic-pullback).

The comparison is the existing `Adjunction.uliftYonedaCompIso`. Its adjunct is
specified sectionwise, and its finite-limit and group-object compatibilities
are stated with Mathlib's canonical comparisons. The lift by `uliftYoneda`
places representables in the larger sheaf universe without changing their sections.
-/

@[expose] public section

universe u v₁ v₂ w z

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The map on represented sheaves induced by the action of the site functor on arrows.
This uses the existing presheaf map `uliftYonedaMap` and fullness of sheaves.
Source: Stacks Project, Sites, Tag 04D3, normalized adjunction/Yoneda argument
(blueprint: lem-pur-site-representable-algebraic-pullback). -/
noncomputable def siteRepresentableArrowMap
    {C : Type v₁} {D : Type v₂} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    J.uliftYoneda.{max u v₁ v₂ w}.obj V ⟶
      (U.sheafPushforwardContinuous (Type (max u v₁ v₂ w)) J K).obj
        (K.uliftYoneda.{max u v₁ v₂ w}.obj (U.obj V)) :=
  ObjectProperty.homMk (uliftYonedaMap.{max u v₁ v₂ w} U V)

/-- The normalized representable comparison, its diagram and finite-limit compatibilities,
and its lift to a natural isomorphism of represented group sheaves.

Source: Stacks Project, Sites, Tag 04D3, `lemma-pullback-representable-sheaf`
(blueprint: lem-pur-site-representable-algebraic-pullback).

Proof:
1. By subcanonicity, representables are sheaves. Adjunction followed by the two
   Yoneda bijections identifies Hom(L h_V, F) with Hom(h_(U V), F).
   For r : h_(U V) -> F, the adjunct of c_V followed by r evaluates at id_V
   to r(id_(U V)), so this bijection is inverse to precomposition by c_V.
   This uses lem-weil-pbc-left-exact-site-inverse-image-tensor and
   lem-galois-yoneda-hom-bijection, with the full sheaf categories of
   def-weil-pbc-sites-and-cohomology.
2. Take F = L h_V to obtain a left inverse of c_V. Injectivity of precomposition
   for F = h_(U V) gives the other inverse identity. The adjunct is precisely
   the action of U on arrows; its value at id_V is id_(U V).
3. For a : V -> V', the two naturality composites have adjuncts sending b to
   U.map (b followed by a) and U.map b followed by U.map a. Functoriality
   identifies them; injectivity of adjunction proves naturality, hence the
   identification of every finite diagram.
4. Yoneda sends limit cones to limit cones: compatible arrows into the diagram
   uniquely give an arrow to its limit. U and the geometric inverse image L
   preserve finite limits. Naturality on the limit projections then identifies
   c at the limit with the map induced on limits by its diagram components.
   This includes the empty diagram and the unique comparison of terminal objects.
5. Apply the product comparison from step 4 and naturality from step 3 to the
   multiplication, unit and inverse of a group object. They say c preserves
   all three operations; composition with its inverse gives the same for its
   inverse. Group identities are preserved by finite products and functoriality.
   Naturality on every group homomorphism gives the natural group isomorphism.
   Under finite-limit preservation, `Functor.isContinuous_iff_coverPreserving`
   identifies the continuity binder with the covering-preservation hypothesis.
   Mathlib's cartesian monoidal structures encode choices of finite products;
   their functor monoidal structures are unique and use the canonical comparisons.
-/
theorem siteRepresentableAlgebraicPullback
    {C : Type v₁} {D : Type v₂} [Category.{u} C] [Category.{u} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [PreservesFiniteLimits U]
    [U.IsContinuous J K]
    (L : Sheaf J (Type (max u v₁ v₂ w)) ⥤ Sheaf K (Type (max u v₁ v₂ w)))
    [PreservesFiniteLimits L]
    (adj : L ⊣ U.sheafPushforwardContinuous (Type (max u v₁ v₂ w)) J K) :
    (∀ V : C,
      IsIso (adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app V) ∧
      adj.homEquiv _ _ (adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app V) =
        siteRepresentableArrowMap J K U V ∧
      (adj.homEquiv _ _ (adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app V)).hom.app
        (op V) (ULift.up (𝟙 V)) = ULift.up (𝟙 (U.obj V)) ∧
      ∀ (W : C) (a : W ⟶ V),
        (siteRepresentableArrowMap J K U V).hom.app (op W) (ULift.up a) =
          ULift.up (U.map a)) ∧
    (∀ (V V' : C) (a : V ⟶ V'),
      L.map (J.uliftYoneda.{max u v₁ v₂ w}.map a) ≫
          adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app V' =
        adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app V ≫
          K.uliftYoneda.{max u v₁ v₂ w}.map (U.map a)) ∧
    (∀ (I : Type z) [SmallCategory I] [FinCategory I] (V : I ⥤ C),
      (preservesLimitIso (J.uliftYoneda.{max u v₁ v₂ w} ⋙ L) V).hom ≫
          lim.map (Functor.whiskerLeft V adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom) =
        adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app (limit V) ≫
          (preservesLimitIso (U ⋙ K.uliftYoneda.{max u v₁ v₂ w}) V).hom) ∧
    (∀ [CartesianMonoidalCategory C]
      [CartesianMonoidalCategory (Sheaf K (Type (max u v₁ v₂ w)))]
      [(J.uliftYoneda.{max u v₁ v₂ w} ⋙ L).Monoidal]
      [(U ⋙ K.uliftYoneda.{max u v₁ v₂ w}).Monoidal],
      ∃ e : (J.uliftYoneda.{max u v₁ v₂ w} ⋙ L).mapGrp ≅
          (U ⋙ K.uliftYoneda.{max u v₁ v₂ w}).mapGrp,
        (∀ G : Grp C, (e.hom.app G).hom.hom =
          adj.uliftYonedaCompIso.{max u v₁ v₂ w}.hom.app G.X) ∧
        (∀ G : Grp C, (e.inv.app G).hom.hom =
          adj.uliftYonedaCompIso.{max u v₁ v₂ w}.inv.app G.X)) :=
  sorry

end CategoryTheory
