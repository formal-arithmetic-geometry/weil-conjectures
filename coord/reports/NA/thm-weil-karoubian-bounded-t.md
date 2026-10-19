## Worker report

This is an `existing: true` delivery, with no new Lean module. The source already states the
whole node using two declarations:

- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`, in
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian`, lines 167–174.
- `CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`,
  in `WeilConjectures.CategoryTheory.Idempotents.TStructure`, lines 195–200.

The second is the main recorded declaration; its module publicly imports the first module.
The original item already had an incomplete attachment record naming these two declarations.
I completed that `lean` record in the required stage-2 format, preserving all other node fields.
The signature is copied verbatim from the second source declaration, up to `:=`.
No mathematical statement correction, new node, dependency repair, or disputed statement is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A triangulated category T | `C : Type u` with `Category.{v} C`, `Preadditive C`, `HasZeroObject C`, `HasShift C ℤ`, additive shift functors, `Pretriangulated C`, and `IsTriangulated C`. These are the constituent structures of a triangulated category, not extra mathematical hypotheses. |
| Has a t-structure | `(t : CategoryTheory.Triangulated.TStructure C)`. |
| The t-structure is bounded | `(ht : ∀ X : C, t.bounded X)`. Mathlib defines `bounded` as `plus ⊓ minus`, where these are respectively `∃ n : ℤ, t.IsGE X n` and `∃ n : ℤ, t.IsLE X n`. Bounds may depend on X. |
| T is idempotent complete | The first declaration concludes `CategoryTheory.IsIdempotentComplete C`. |
| Every idempotent e : K → K splits | This is exactly the field `IsIdempotentComplete.idempotents_split`: for every `X`, `p : X ⟶ X`, and `p ≫ p = p`, there are `Y`, `i : Y ⟶ X`, `e : X ⟶ Y` with `i ≫ e = 𝟙 Y` and `e ≫ i = p`. |
| The canonical functor T → Kar(T) | Both conclusions about the functor use `CategoryTheory.Idempotents.toKaroubi C`, with Mathlib's `Karoubi C`, exactly the dependency's construction. |
| Fully faithful | The unconditional Mathlib declaration `CategoryTheory.Idempotents.fullyFaithfulToKaroubi C : (toKaroubi C).FullyFaithful` identifies this same functor as fully faithful. Also, `IsEquivalence` entails full faithfulness. |
| Is an equivalence | The first conjunct of the main declaration is `(toKaroubi C).IsEquivalence`. |
| Is exact | The second conjunct is `(toKaroubi C).IsTriangulated`, meaning that, with its canonical shift comparison, it sends distinguished triangles to distinguished triangles. |

The source-note paragraph discusses the absence of this theorem from Stacks; it is provenance,
not another mathematical conclusion. Neither countable coproducts nor kernels are substituted
for the stated bounded t-structure hypothesis.

Dependency declarations read and used:

- `def-weil-karoubi-envelope` is a Mathlib leaf and has no `lean` record. Its recorded
  `mathlib_match` is `CategoryTheory.Idempotents.Karoubi` in
  `Mathlib.CategoryTheory.Idempotents.Karoubi`; its `how` also names
  `CategoryTheory.Idempotents.toKaroubi`. I read the structures `Karoubi` and `Karoubi.Hom`,
  the category instance, `id_f`, `comp_f`, `toKaroubi`, and `fullyFaithfulToKaroubi`.
  Objects are `(X,p)` with `p ≫ p = p`; morphisms have `P.p ≫ f ≫ Q.p = f`;
  composition and the inclusion's underlying map are inherited from C, and the identity is p.
- The existing theorem uses Mathlib `CategoryTheory.Triangulated.TStructure` and `bounded`
  from `Mathlib.CategoryTheory.Triangulated.TStructure.Basic` and
  `CategoryTheory.IsIdempotentComplete` from `Mathlib.CategoryTheory.Idempotents.Basic`.
- Its exactness conclusion uses the canonical Karoubi shift and pretriangulated structures,
  supplied by `WeilConjectures.CategoryTheory.Idempotents.Pretriangulated` (including
  `CategoryTheory.Idempotents.toKaroubi.isTriangulated`), publicly imported by the main module.
  I read the definition of `Functor.IsTriangulated` in Mathlib's Triangulated.Functor.

Edge cases checked against the signatures and definitions: the zero category and zero object;
zero and identity idempotents; objects concentrated in one degree; categories with no common
uniform bound on all objects; arbitrary integral shifts, including negative bounds; and
independent object and morphism universes. There is no nonzero, nonempty-family, countable-sum,
small-category, or uniform-amplitude assumption. An actually empty category cannot satisfy the
zero-object part of being triangulated, so no triangulated case is lost.

Searches actually performed:

- `msearch.py leansearch`: `bounded t-structure triangulated category idempotent complete`.
  The service returned Internal Server Error; recorded as unavailable, with no match verdict.
- `msearch.py leanfinder`: `A triangulated category carrying a bounded t-structure is
  idempotent complete and its canonical inclusion into the Karoubi envelope is an exact
  equivalence`. Eight hits included `TStructure`, `IsGE`, `IsLE`, a homological-kernel
  triangulated instance, and localization constructions, but no theorem stating this result.
- `msearch.py loogle`: `CategoryTheory.IsIdempotentComplete,
  CategoryTheory.Triangulated.TStructure`. Zero hits. An earlier unqualified query returned
  an unknown-identifier diagnostic and is not used as mathematical evidence.
- `msearch.py grep`: `IsIdempotentComplete|toKaroubi|bounded` in
  `CategoryTheory/Triangulated/TStructure`. Twelve hits concerned bounded subcategories and
  their induced structures; no idempotent-completeness theorem.
- Read-only source `rg` for `bounded.*(Karoubi|[Ii]dempotent)|[Ii]dempotent.*bounded|
  isEquivalence_toKaroubi` found precisely the existing declarations above. The exact
  blueprint-id search in `WeilConjectures` found their docstrings. Read their complete
  signatures, surrounding variables, docstrings, and proof bodies.
- The same concept search in `lean/Sheaf` found no duplicate. The DAG item's own
  `lean_audit.slopmaster2` and incomplete attachment already identify these two theorems;
  no extra definition is necessary. The source-name map search gave no additional match.
- `scompile.py --source WeilConjectures.CategoryTheory.Idempotents.TStructure` confirmed
  the current server source agrees with the local source and publicly imports Karoubian.

Validation: a sandbox scratch probe imports only the existing main module and checks both
full theorem types and `fullyFaithfulToKaroubi`. Its `#print axioms` checks report only
`propext`, `Classical.choice`, and `Quot.sound` for both theorems, with no `sorryAx`.
The first probe had one overlong `#print axioms` line; it was wrapped and recompiled.
The required `deliver2.py --no-push` check is run after this report; the second reader will
supply the independent second-reading section and perform delivery.

## Second reading by NA

I reread the node statement, its dependency, and the two recorded source declarations. The
item-by-item correspondence is:

- The category is `C : Type u` with independent morphism/object universe `v`,
  `[Category.{v} C]`, `[Preadditive C]`, `[HasZeroObject C]`, `[HasShift C ℤ]`,
  `[∀ n : ℤ, (shiftFunctor C n).Additive]`, `[Pretriangulated C]`, and
  `[IsTriangulated C]`. These are exactly the project encoding of a triangulated category.
- The t-structure is the explicit object `(t : TStructure C)`.
- Boundedness is exactly `(ht : ∀ X : C, t.bounded X)`; `t.bounded X` supplies an
  object-dependent lower and upper integral bound. No uniform bound is introduced.
- The conclusion that `C` is idempotent complete is rendered by
  `isIdempotentComplete_of_bounded ht : IsIdempotentComplete C`. Its splitting field
  quantifies every `X`, every `p : X ⟶ X`, and `p ≫ p = p`, and supplies a splitting.
- The canonical inclusion is exactly `Idempotents.toKaroubi C`, whose target is Mathlib's
  `Karoubi C` from `def-weil-karoubi-envelope`; no private envelope or arbitrary functor is used.
- The main recorded theorem has the exact conjunction
  `(toKaroubi C).IsEquivalence ∧ (toKaroubi C).IsTriangulated`. `IsEquivalence` includes
  full faithfulness, and `fullyFaithfulToKaroubi C` independently confirms that this is the
  canonical fully faithful functor. `IsTriangulated` is the Lean exactness assertion for the
  canonical shift comparison and distinguished triangles.

The hypotheses and conclusion therefore match the node without addition, omission, or
strengthening. The source-note paragraph is not a mathematical clause. The source places were
checked against the blueprint node and Stacks Tags 09SG, 09SH, and 05QV: those pages define
Karoubianity, give its splitting criterion, and give countable product/coproduct sufficient
conditions, respectively; none states the bounded-t-structure theorem. No statement
correction is warranted, so there are no citers to audit and no `statement_change`.

Edge cases checked are the zero category/zero object, zero and identity idempotents, a category
whose objects have only object-dependent bounds, negative integral shifts, `n = 0` in the
underlying boundedness definitions, and the independent universes `u` and `v`. The empty
category cannot satisfy `HasZeroObject`, so no triangulated case covered by the node is lost.
There is no index family, characteristic, nonzero assumption, countability assumption, or
uniform-amplitude assumption to exclude an edge case.

I repeated the existing-declaration searches. `msearch.py` LeanSearch was unavailable;
LeanFinder returned eight related constructions but no theorem of this form; Loogle returned
no match (and diagnosed the unqualified identifier); and grep over Mathlib, the source
`WeilConjectures`, and `lean/Sheaf` found only the two source declarations and no duplicate
project declaration. The dependency search confirmed Mathlib's `Karoubi`, `toKaroubi`, and
`fullyFaithfulToKaroubi` declarations and the exact morphism/identity conditions recorded by
`def-weil-karoubi-envelope`.

No mismatch was found and no file or node field required repair. The existing attachment's
`lean` record is complete: its primary declaration is
`CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`,
its auxiliary declaration is
`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`, and its statement is
verbatim through the colon. The required scratch probe was compiled with `scompile.py`; both
source declarations have only `propext`, `Classical.choice`, and `Quot.sound` as axioms and no
`sorryAx`.
