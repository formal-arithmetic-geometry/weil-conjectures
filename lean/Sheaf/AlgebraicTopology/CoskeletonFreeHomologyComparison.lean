/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Homology comparison for coskeletal simplicial presheaves

Source: Stacks Project, Hypercoverings, Lemma 01GD
(blueprint: lem-weil-pbc-coskeleton-free-homology-comparison).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Simplicial

-- Infer preservation of cover-indexed colimits from preservation at the coefficient universe.
attribute [local instance] preservesFilteredColimitsOfSize_shrink

namespace CategoryTheory.SimplicialObject

/-- Stacks Project, Hypercoverings, Lemma 01GD, with free modules over a commutative ring.
(blueprint: lem-weil-pbc-coskeleton-free-homology-comparison)

Proof route:
1. Replace degree `n` of the truncation of `K` by the image of `f` and coskeletonize,
   obtaining `K'` and a factorization `L → K' → K`. The image is stable under the
   simplicial operators since the lower-degree components of `f` are isomorphisms.
   Use lem-weil-pbc-truncated-coskeleton-finite-limits for the counit and functoriality.
2. The image inclusion in degree `n` becomes both mono and epi after sheafification,
   hence an isomorphism (lem-weil-pbc-sheaf-sets-mono-epi-iso). Sheafification preserves
   finite limits (lem-weil-pbc-sheafification-sets-exact), so `K' → K` becomes an
   isomorphism in every degree, by lem-weil-pbc-truncated-coskeleton-finite-limits.
3. By lem-weil-pbc-free-module-sheaf-sheafify-first, the free-module sheaf complexes
   of `K'` and `K` are isomorphic, hence so are their homology sheaves.
4. Evaluate `L → K'` at each object of the site. Evaluation preserves the finite
   limits computing coskeleta, so lem-weil-pbc-coskeletal-map-trivial-kan applies:
   the map is a trivial Kan fibration, bijective below `n` and surjective at `n`.
5. By lem-weil-pbc-trivial-kan-homotopy-equivalence it has a simplicial homotopy
   inverse. By lem-weil-pbc-simplicial-homotopy-free-chain-homotopy, the induced
   free-module chain map is a chain homotopy equivalence, hence a homology isomorphism.
6. Homology of module presheaves is objectwise and exact sheafification commutes with
   homology (lem-weil-pbc-site-module-presheaf-sheafification-exact). Thus `L → K'`
   induces isomorphisms on homology sheaves; the objectwise inverses need not be natural.
7. Compose these isomorphisms with those of `K' → K` to obtain the conclusion.
-/
theorem isIso_homologyMap_of_local_surjective_coskeletal
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v w)) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n)
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))} (f : L ⟶ K)
    (hlow : ∀ i : ℕ, i < n → IsIso (f.app (Opposite.op ⦋i⦌)))
    (hsurj : Epi ((presheafToSheaf J (Type (max u v w))).map
      (f.app (Opposite.op ⦋n⦌))))
    (hL : IsIso ((coskAdj n).unit.app L))
    (hK : IsIso ((coskAdj n).unit.app K)) :
    ∀ i : ℕ, IsIso
      (((SimplicialObject.whiskering _ _).obj
          ((whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙
            presheafToSheaf J (ModuleCat.{max u v w} R)) ⋙
        AlgebraicTopology.alternatingFaceMapComplex (Sheaf J (ModuleCat.{max u v w} R)) ⋙
        HomologicalComplex.homologyFunctor (Sheaf J (ModuleCat.{max u v w} R))
          (ComplexShape.down ℕ) i).map
          f) := sorry

end CategoryTheory.SimplicialObject
