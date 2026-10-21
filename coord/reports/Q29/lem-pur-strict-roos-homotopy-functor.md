## Worker report

The module `Sheaf.CategoryTheory.StrictRoosHomotopyFunctor` states
`CategoryTheory.roosF_homotopy_functor` with one `sorry`. It uses the existing
`CategoryTheory.roosF`; no construction or dependency is duplicated. No statement
correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- An abelian category with countable products is `{A : Type u} [Category.{v} A]
  [Abelian A] [HasCountableProducts A]`. Object and morphism universes are independent.
  Exactness of products and existence of tower limits are not assumed.
- A strict tower complex is `CochainComplex (ℕᵒᵖ ⥤ A) ℤ`. Reindexing `n ↦ n+1`
  identifies this index with the positive integers of def-weil-inverse-system.
- Products, one minus shift, and the fixed shifted cone are the existing `roosP`,
  `roosU`, and `roosF` of StrictRoosModel. The existing `roosχ X p` identifies
  degree `p+1` with `P_X^p ⊞ P_X^(p+1)`. No arbitrary derived-limit object is used.
- The prescribed diagonal action on maps, preservation of identities and composition
  are part of the existing functor `roosF`: `roosConeFunctor.map`, `roosPmap`, and
  `roosF_map_χ`. The first conjunct `(roosF (A := A)).Additive` states its additivity.
- `f g : X ⟶ Y` are strict tower maps. `h : Homotopy f g` has degreewise
  natural-transformation components `h.hom i j`; naturality is precisely compatibility
  with every tower transition. Compatibility with adjacent transitions suffices by
  composition, so this does not strengthen the node's hypothesis. `Homotopy.comm`
  is `f = dh + hd + g`, equivalently the node's `f-g = dh+hd`.
- The second conjunct provides `H : Homotopy (roosF.map f) (roosF.map g)`.
  For every `p : ℤ` and `n : ℕ` the first equation projects the target's first
  biproduct coordinate and product factor: it is minus the source first coordinate
  followed by `(h.hom (p+1) p).app (op n)`. The second equation projects the second
  coordinate and gives the source second coordinate followed by
  `(h.hom ((p+1)+1) (p+1)).app (op n)` with positive sign. Together, by product
  and biproduct uniqueness, these equations say exactly `(-h_P y, h_P x)`.
  The running degree is `(p+1)+1`, which ranges over all integers; it omits no degree.
- `RF` has source `HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)` and target
  `HomotopyCategory A (ComplexShape.up ℤ)`. `RF.Additive` states additivity. The
  equality `quotient ⋙ RF = roosF ⋙ quotient` fixes both its object assignment
  and its action `[f] ↦ [roosF.map f]`. This is an actual quotient factorization,
  not an existential functor unrelated to the construction. Strict equality is
  available from Mathlib's `Quotient.lift_spec` and canonical quotient objects.
- The final universal quantifier over `k : Type w`, `[CommRing k]`, `[Linear k A]`
  is conditional linearity. `(roosF (A := A)).Linear k ∧ RF.Linear k` states
  preservation of multiplication of maps for both functors. No coefficient field
  or characteristic assumption is added. The existential RF precedes this
  quantifier, so the same quotient functor works for every coefficient structure.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (via StrictRoosModel).
- def-weil-inverse-system: `CategoryTheory.Functor.ofOpSequence` and
  `CategoryTheory.NatTrans.ofOpSequence`, `Mathlib.CategoryTheory.Functor.OfSequence`.
  The statement uses the functor category these declarations construct.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`
  uses the same `CochainComplex` and `HomotopyCategory` foundations. No derived
  category or localization-size assumption is needed for this homotopy-level result.
- def-weil-strict-roos-model: `CategoryTheory.roosF`, `roosP`, `roosU`, `roosPmap`,
  `roosχ`, `roosF_map_χ`, `Sheaf.CategoryTheory.StrictRoosModel`.
- def-weil-linear-category: `CategoryTheory.Linear`,
  `Mathlib.CategoryTheory.Linear.Basic`; functor linearity is `Functor.Linear`
  from `Mathlib.CategoryTheory.Linear.LinearFunctor`.
- Proof-only def-weil-category-product: `piObj`, `Pi.π`, `Pi.lift`, `Pi.map`,
  `HasCountableProducts`, Mathlib's products/countable modules, already imported
  through StrictRoosModel. All proof dependency modules are in the import closure.

Sources read: derived.tex labels definition-cone and definition-derived-limit;
the eight proof steps of the node; the full StrictRoosModel module; the signatures
and definitions of Homotopy, homotopic, HomotopyCategory.quotient, Quotient.lift,
Quotient.lift_spec, and the linearity instances on homotopy categories. The signed
cone differential yields the mixed block `Hv_X-v_YH=0`; no claim about functorial
cones of arbitrary maps in a triangulated category is made.

Edge cases checked mathematically: zero towers and zero homotopies; f=g with h=0;
constant towers; complexes concentrated in one degree; arbitrary negative degrees;
characteristic two (the two signs coincide as required); countable products that
are not exact. Every formula is an equality of morphisms, not elements of A.

Searches actually run:

- msearch.py leanfinder: "The strict Roos shifted cone is an additive functor
  preserving compatible chain homotopies and scalar multiplication" returned eight
  generic mapping-cone and spectral-object hits, no exact strict Roos theorem.
- msearch.py loogle: "CochainComplex.mappingCone.map, HomotopyCategory.lift"
  returned zero hits, unknown identifier HomotopyCategory.lift. The actual generic
  quotient constructor was found by reading Mathlib as CategoryTheory.Quotient.lift.
- msearch.py grep: "roos|def lift|lift.*[Hh]omotopy" in
  Algebra/Homology/HomotopyCategory returned nine generic lift constructors;
  none states this theorem.
- rg: "roosF|roos.*[Hh]omotopy|lem-pur-strict-roos-homotopy-functor" over
  lean/WeilConjectures and lean/Sheaf found the existing strict model and
  specialized Roos comparison/calculus modules, but no general compatible-homotopy
  formula with additive and linear quotient descent. Existing RoosConeCalculus
  assumes the ringed-site module setting and additionally treats quasi-isomorphisms,
  cone comparisons, and shift compatibility; it is not this statement.
- rg: "roosF_homotopy_functor" over dag/lean_names_upstream.json,
  lean/WeilConjectures and lean/Sheaf returned no hit.

Validation: scompile.py was invoked on the delivered file. Before elaborating it,
its local overlay failed because Mathlib.CategoryTheory.Preadditive.Basic.olean
is missing, and its server confirmation reported "Live published library is
unavailable". Compilation and delivery are pending restoration of that service. The delivery dry run
(`deliver2.py --no-push`) reproduced the same missing artifact and unavailable
published-library error, exited 1, and pushed nothing. A second direct scompile.py
attempt was also made; no tool or upstream library was modified.

## Second reading by Q29

A separate manual pass by this worker compared the node, the file, and the
StrictRoosModel and Mathlib source definitions. No independent agent was started,
as prohibited by the dispatch brief; independent review belongs to the maintainer.
The pass checked all hypotheses, the two homotopy signs and degree indices,
the equivalence of compatible levelwise homotopies with Homotopy in the functor
category, the strict quotient factorization, and conditional linearity of both
functors. No mathematical mismatch was found. Compilation remains unverified
because the compile service failed before reaching this module.

## Resumed validation

On resumption, the required first `deliver2.py Q29 lem-pur-strict-roos-homotopy-functor --no-push` and a direct `scompile.py` retry both exited 1 before elaborating the delivered module. Both failed while compiling the upstream overlay `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`: `Mathlib/CategoryTheory/Preadditive/Basic.olean` does not exist. Both server confirmations reported "Live published library is unavailable". The saved module and node were retained, and nothing was pushed. The node differs from the read clone only in `lean`; its recorded signature matches the saved source, and the source has no lines over 100 characters. No repair note exists in the read clone for this item. Restoring the published library is outside the authorized worker sandbox.

## Further resumed validation (2026-10-21)

The prescribed first dry run and the direct scompile.py retry again exited 1 before elaborating this module. Both failed in the upstream TowerTransitionEndomorphism overlay because Mathlib/CategoryTheory/Preadditive/Basic.olean is missing; both server confirmations said "Live published library is unavailable". This is not a busy-server timeout. The saved node copy had a stale lean_audit field; it was refreshed from the current read clone, retaining the saved lean record, so only lean differs. The recorded theorem signature matches the saved source verbatim, no source line exceeds 100 characters, and no repair note is present. The source and theorem are retained; no library or launcher files were modified and nothing was pushed. A final dry run after refreshing metadata was requested.

The final dry run after that metadata repair also exited 1 with the identical missing Mathlib/CategoryTheory/Preadditive/Basic.olean artifact and "Live published library is unavailable" server confirmation. Delivery remains blocked before elaboration; nothing was pushed.

## Compile service restored and import repair (2026-10-21)

The first required dry run on this resumption reached elaboration: the published
library is available again. It reported missing `Linear k` instances on complexes
of towers and their homotopy category. Added only the public import
`Mathlib.CategoryTheory.Linear.FunctorCategory`, whose
`CategoryTheory.functorCategoryLinear` supplies the componentwise linear structure
on towers. The existing homological-complex and homotopy-category instances then
apply. No hypothesis, conclusion, dependency node, or theorem signature changed.

A direct scompile.py check now passes for both the sandbox module and its final
library module, with no errors or warnings. This supersedes all earlier statements
in this report that compilation is pending or unverified. The current node differs
from the read clone only in `lean`; the signature matches the file verbatim.
There is no repair-note file for this item.

The resumed manual second reading checked the current dependency records and the
full StrictRoosModel construction. Its `roosF_map_χ` gives exactly the prescribed
diagonal product action. At source degree `(p+1)+1`, the homotopy maps to degree
`p+1`; its first projection uses `h.hom (p+1) p` with a minus sign, and its second
uses `h.hom ((p+1)+1) (p+1)` with a plus sign. Thus the two equations cover every
integer degree with the intended formula. The quotient equality still fixes the
object and morphism assignments; additivity and conditional linearity are present
for both functors. Independent object, morphism, and scalar-ring universes remain
explicit. No new mathematical mismatch was found. No other agent was started.
