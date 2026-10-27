/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Sheaf.AlgebraicGeometry.PreorderBarTotal
import Sheaf.AlgebraicGeometry.PreorderBarFilteredAugmentation
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedModuleFiltrationTelescope

/-! # Directed module colimits in localizing subcategories

Source: Stacks Project, Algebra, Tag 00DB (`lemma-directed-colimit-exact`),
and the bar-resolution corollary assembled in the DAG proof. This is a corollary
of exactness of directed colimits, not the verbatim assertion of Tag 00DB.
(blueprint: lem-sfb-module-localizing-filtered-colimits).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A full replete triangulated subcategory of the ordinary unbounded module derived
category, closed under retracts and module-universe coproducts, contains the degree-zero
module associated to a directed colimit whenever it contains every term in degree zero.
No Noetherian assumption or injectivity of the transition maps is imposed.

Source: Stacks Project, Algebra, Tag 00DB (`lemma-directed-colimit-exact`), together
with the following agent bar-resolution argument, as recorded in the DAG.
(blueprint: lem-sfb-module-localizing-filtered-colimits).

Proof plan:
1. Compose `M` with the degree-zero complex functor. Its colimit is the degree-zero
complex of `colimit M`, since complex colimits are computed degreewise
(`def-weil-pbc-category-colimit`). The category of modules is Grothendieck abelian
(`lem-weil-pbc-ring-modules-grothendieck-abelian`), and the nonempty directed poset
is filtered, so these colimits are exact. Form its preorder bar total
(`def-sc-preorder-bar-total`). In degree `-n` it is the coproduct of `M.obj i₀`
over chains `i₀ ≤ ... ≤ iₙ`, including repetitions; positive degrees vanish.
Its canonical augmentation to the degree-zero colimit is a quasi-isomorphism by
`lem-sc-preorder-bar-filtered-augmentation`. Transition maps need not be monic.
2. Each bar term in degree zero belongs to `P`: apply
`lem-kun-grothendieck-derived-coproducts` to the family of degree-zero modules
indexed by these chains, and use coproduct closure. All chain sets lie in the
module universe.
3. Let `F n` be the brutal subcomplex in degrees `[-n, 0]`. Starting with the
zeroth bar term, induct using the degreewise split short exact sequence from
`F (n-1)` to `F n` with quotient the nth bar term shifted by `n`.
By `lem-pc-cone-short-exact-quasi-iso` its cone gives a distinguished triangle
in the derived category (`def-weil-abstract-derived-category`). Shift and
triangle closure therefore put every `Q.obj (F n)` in `P`.
4. These subcomplexes include monomorphically and exhaust the total degreewise.
Apply `lem-pc-derived-module-filtration-telescope`: its coproduct `S`, indexed
by `ULift ℕ` in the module universe, fits into the distinguished triangle
`S ⟶ S ⟶ Q.obj B ⟶ S[1]`. Coproduct and triangle closure give `P (Q.obj B)`.
5. Localization inverts the bar augmentation
(`def-weil-abstract-derived-category`). Isomorphism closure transfers membership
from `Q.obj B` to the degree-zero module of `colimit M`. -/
theorem moduleLocalizing_filtered_colimit
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (P : ObjectProperty (DerivedCategory (ModuleCat.{max u v} R)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] [P.IsStableUnderRetracts]
    [∀ J : Type (max u v), P.IsClosedUnderColimitsOfShape (Discrete J)]
    (I : Type (max u v)) [PartialOrder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (M : I ⥤ ModuleCat.{max u v} R)
    (hM : ∀ i : I, P ((singleFunctor (ModuleCat.{max u v} R) 0).obj (M.obj i))) :
    P ((singleFunctor (ModuleCat.{max u v} R) 0).obj (colimit M)) := by
  sorry

end DerivedCategory
