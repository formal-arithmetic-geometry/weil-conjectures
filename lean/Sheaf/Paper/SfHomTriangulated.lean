/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Sheaf.Algebra.Homology.RingedInternalHomExactUniverses

/-! # Exactness of internal Hom on the small etale site

Source: Stacks Project, Cohomology on Sites, Lemma 21.35.4 (Tag 08JC), with the
K-injective construction of Section 21.35 (Tag 08J7)
(blueprint: lem-sf-hom-triangulated).

The module category is written as modules over the constant ring sheaf, exactly
as in the node's definition of D(X_et,A). No boundedness condition is imposed.
A triangulated functor from the opposite derived category expresses the reversed
triangle in the first variable; its shift is the negative of the original shift.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.Etale

/-- Internal Hom is triangulated in both variables on D(Mod(A_X)). In the first
variable this means a functor out of the opposite triangulated category; in the
second it is covariant. The shift-compatible triangulated structures include
precisely the shift identifications used to form the two image triangles.

Source: Stacks Project, Tag 08JC, construction in Tag 08J7; blueprint
sec-six-functors/sk-prop-sf-rf-shriek-preservation/lem-sf-hom-triangulated.md
(blueprint: lem-sf-hom-triangulated).

Proof plan:
1. Work on the small etale site with its explicit larger module universe
   (def-weil-pbc-etale-site, def-weil-size-convention). The constant commutative
   ring sheaf A_X gives D(Mod(A_X)) (def-weil-pbc-derived-categories).
   The recorded derivedInternalHomOfUniverses is computed by the Hom complex
   into a functorial K-injective replacement (def-pur-derived-internal-hom).
2. Apply the first-variable clause of ringedInternalHom_exact from
   lem-weil-pbc-ringed-internal-hom-exact-restriction, transporting along a small
   model of the site if necessary. For a fixed target M this sends the opposite
   of K' -> K -> K'' -> K'[1] to the reversed distinguished Hom triangle.
   The opposite shift gives H(L[1],M) = H(L,M)[-1], with the cone signs.
3. Apply its second-variable clause with K fixed to the distinguished triangle
   M' -> M -> M'' -> M'[1]. The covariant shift identifies H(K,M'[1]) with
   H(K,M')[1], yielding the second displayed triangle. The cone calculation
   uses only finite splittings, so neither clause needs boundedness or finite
   generation. -/
theorem sf_internalHom_triangulated (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1}
      ((sheafCompose X.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A))))] :
    (∀ M, ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{u + 1, u, u + 1, w} X.smallEtaleTopology
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A)))).flip.obj M).CommShift ℤ,
      ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{u + 1, u, u + 1, w} X.smallEtaleTopology
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A)))).flip.obj M).IsTriangulated) ∧
    (∀ K, ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{u + 1, u, u + 1, w} X.smallEtaleTopology
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A)))).obj (op K)).CommShift ℤ,
      ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{u + 1, u, u + 1, w} X.smallEtaleTopology
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A)))).obj (op K)).IsTriangulated) := by
  simpa only using
    (CategoryTheory.RingedHomUniverses.ringedInternalHom_exact.{u + 1, u, u + 1, w}
      X.smallEtaleTopology
      ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)))

end AlgebraicGeometry.Etale
