/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.GeometricStalkAsPullback
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Geometric stalks of cohomology sheaves

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-stalks-of-cohomology.md, statement and proof
(blueprint: lem-kun-stalks-of-cohomology).

The cohomology of the inverse image at a geometric point is read in abelian groups,
using derived global sections on the algebraically closed point, as in
`AlgebraicGeometry.Scheme.geometricStalk_as_pullback`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The stalk of the degree-`q` cohomology sheaf of an unbounded derived object is
its pullback to the geometric point followed by degree-`q` cohomology. Global
sections identify sheaves on the algebraically closed point with abelian groups.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-stalks-of-cohomology.md, statement and proof
(blueprint: lem-kun-stalks-of-cohomology).

Proof: Represent `Q` by any cochain complex `C` of abelian sheaves, using
`def-weil-pbc-derived-categories`. The stalk functor of
`def-weil-pbc-geometric-stalks` is exact by
`prop-weil-pbc-geometric-stalks-exact`. Apply
`lem-sp-exact-functor-preserves-homology` to the three consecutive terms around
`q`: preservation of kernels and images identifies the stalk of `H^q(C)` with
`H^q` of the termwise stalk complex, naturally in chain maps. By
`lem-weil-pbc-exact-functor-derived-factorization`, that termwise complex
represents the derived stalk without any boundedness or resolution hypothesis.
Finally `lem-kun-stalk-as-pullback` identifies the derived stalk with inverse
image followed by derived global sections on `Spec Ω`. Naturality of the
homology comparison makes this independent of the chosen representative. -/
theorem geometricStalk_homology_pullback (T : Scheme.{u}) (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (Q : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (q : ℤ) :
    Nonempty ((pointSmallEtale t).sheafFiber.obj
        ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((AlgebraicGeometry.Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1}
          (Spec (.of Ω))).obj
          ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.obj
            Q))) := by
  sorry

end AlgebraicGeometry.Scheme
