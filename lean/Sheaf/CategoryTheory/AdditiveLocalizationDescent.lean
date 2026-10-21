module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Additivity descends through an additive localization

Source: Stacks Project, Categories, Tag 04VG; Homological Algebra, Tags 00ZY, 0103,
0104, 0105 and 0DLP. The descent argument is the agent-written biproduct argument
recorded in the DAG, without a calculus of fractions.
(blueprint: lem-pur-additive-localization-descent)
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

/-- Additivity descends along an additive localization, with essential surjectivity
explicitly assumed. Source: Stacks Project, Categories, Tag 04VG (localization);
Homological Algebra, Tags 00ZY, 0103, 0104, 0105 and 0DLP (additivity and biproducts).
(blueprint: lem-pur-additive-localization-descent)

Proof (the agent-written argument recorded in the node):
1. Put `H = q ⋙ G`. Naturality of `e` expresses `H.map f` as `U.map f` conjugated by
   components of `e`. Bilinearity of composition and additivity of `U` show that `H`
   is additive. Additive maps on Hom groups preserve zero; this applies to `q` too.
2. Choose a biproduct of `X` and `Y` in `C`. Both `q` and `H` preserve its five
   biproduct relations, by functoriality, preservation of zero and additivity.
3. These relations show that each image cone is a product: the lift of `(a,b)` is
   the sum of the two image injections composed with `a,b`. Its projections are
   `a,b`, and the sum-of-injection-projection identity proves uniqueness.
4. For arbitrary objects of `D`, use essential surjectivity to choose isomorphisms
   from `q.obj X` and `q.obj Y`. Transport the product cone in step 3 along them.
   Its image under `G` is a product by the same construction. Any other product
   cone is uniquely isomorphic to this one, and `G` preserves that isomorphism.
   Thus `G` preserves all binary products, without assuming fullness of `q`.
5. On image objects, `G.map 0 = H.map 0 = 0` because `q.map 0 = 0`.
   For arbitrary objects, transport the zero map through the isomorphisms in
   step 4; bilinearity and functoriality give preservation of zero by `G`.
6. Apply `Functor.additive_of_preserves_binary_products`
   (blueprint node `lem-sfb-products-zero-additive`) to steps 4 and 5. No fraction
   representation, or further use of the localization hypothesis, is needed.
-/
theorem Functor.additive_of_additive_localization
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (W : MorphismProperty C) (q : C ⥤ D) [q.Additive] [q.IsLocalization W]
    [q.EssSurj] (U : C ⥤ E) [U.Additive] (G : D ⥤ E) (e : q ⋙ G ≅ U) :
    G.Additive := by
  classical
  have : (q ⋙ G).Additive := Functor.additive_of_iso e.symm
  have : PreservesLimitsOfShape (Discrete WalkingPair) G := by
    constructor
    intro K
    let F : Discrete WalkingPair ⥤ C :=
      Discrete.functor (fun j ↦ q.objPreimage (K.obj ⟨j⟩))
    have : PreservesLimit (F ⋙ q) G :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves q (limit.isLimit F))
        (isLimitOfPreserves (q ⋙ G) (limit.isLimit F))
    exact preservesLimit_of_iso_diagram G
      (show F ⋙ q ≅ K from Discrete.natIso (fun j ↦ q.objObjPreimageIso (K.obj j)))
  have : G.PreservesZeroMorphisms := by
    constructor
    intro X Y
    rw [← cancel_mono (G.map (q.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (q.objObjPreimageIso X).hom)]
    simp only [← G.map_comp, zero_comp, comp_zero]
    rw [← q.map_zero]
    exact (q ⋙ G).map_zero _ _
  exact G.additive_of_preserves_binary_products

end CategoryTheory
