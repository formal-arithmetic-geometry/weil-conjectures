/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Locally covering fibred functors detect exactness

Source: Stacks Project, stacks-sheaves.tex, Tag 06XD
(blueprint: lem-sfb-fibred-cover-detects-exactness).

The inherited big etale precoverage is `Scheme.etalePrecoverage.comap` along the
projection to schemes. The equality of underlying presheaf complexes specifies
precomposition on all three objects and both arrows, without choosing a second
inverse-image construction. A sheaf complex with that underlying complex is precisely
the complex of precomposed sheaves in the source statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ a

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/-- A locally covering functor of categories fibred in groupoids detects exactness
at the middle term of any three-term complex of abelian sheaves.
Source: Stacks Project, stacks-sheaves.tex, Tag 06XD
(blueprint: lem-sfb-fibred-cover-detects-exactness).

Proof plan:
1. Compute the kernel of the second arrow sectionwise, using
   lem-weil-pbc-sheafification-exact. By
   lem-weil-pbc-abelian-exact-iff-epi-kernel-lift and
   lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective, exactness says that every
   kernel section locally lifts through the first arrow.
2. Cover an object of X by objects isomorphic to images of objects of U, using
   hcover. Restrict the kernel section and transport it through these isomorphisms.
3. By exactness of L and the same local lifting criterion, lift each transported
   section after a covering in U. A based functor sends that covering to a covering
   in X: its underlying scheme family is unchanged. Compose with the isomorphisms
   and the original covering. Functoriality identifies the resulting lifted sections
   with restrictions of the original section.
4. The local lifting criterion now gives exactness of K. This includes K.X₁ = 0
   and K.X₃ = 0: the first case gives local vanishing of kernel sections, and the
   second gives local lifting of every middle-term section. No faithfulness,
   algebraicity, or representability is used. -/
theorem exact_of_fibred_etale_cover
    {S : Scheme.{u}} {U : BasedCategory.{v₁, w₁} (Over S)}
    {X : BasedCategory.{v₂, w₂} (Over S)}
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (f : BasedFunctor U X)
    (hcover : ∀ x : X.obj,
      ∃ R : Presieve x,
        R ∈ Scheme.etalePrecoverage.comap (X.p ⋙ Over.forget S) x ∧
        ∀ (y : X.obj) (r : y ⟶ x), R r →
          ∃ z : U.obj, Nonempty (f.toFunctor.obj z ≅ y))
    (K : ShortComplex (Sheaf
      (Scheme.etalePrecoverage.comap (X.p ⋙ Over.forget S)).toGrothendieck
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ a}))
    (L : ShortComplex (Sheaf
      (Scheme.etalePrecoverage.comap (U.p ⋙ Over.forget S)).toGrothendieck
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ a}))
    (hL : L.map (sheafToPresheaf _ _) =
      (K.map (sheafToPresheaf _ _)).map
        ((Functor.whiskeringLeft _ _ _).obj f.toFunctor.op))
    (hexact : L.Exact) : K.Exact := by
  sorry

end CategoryTheory
