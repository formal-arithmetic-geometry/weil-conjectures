## Worker report

Item: `lem-weil-pbc-module-derived-complete-products-triangles`.
Module: `Sheaf.RingTheory.DerivedCompleteProductsTriangles`.
Declaration: `DerivedCategory.isDerivedComplete_products_and_triangles`.
The only theorem proof is `sorry`; no definition is introduced and nothing is proved.
The node is unchanged except for its `lean` record.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The commutative ring is `{A : Type u} [CommRing A]`; the arbitrary ideal is
  `(I : Ideal A)`, without any finite-generation or principal-ideal hypothesis.
- The ambient category is `DerivedCategory (ModuleCat.{v} A)` under the size-choice
  binder `[HasDerivedCategory.{w} (ModuleCat.{v} A)]`. Universes `u v w` are explicitly
  declared. This is the recorded unbounded module derived category, with its canonical
  triangulated structure, rather than a derived category of coefficient sheaves.
- Completeness throughout is the dependency's `DerivedCategory.IsDerivedComplete I`:
  for every `f ∈ I`, every derived limit of the constant multiplication-by-f tower is zero.
- Clause (1)'s countable family is `K : ℕ → DerivedCategory (ModuleCat.{v} A)`.
  Index `n` denotes the paper's index `n+1`, a bijective reindexing of its positive
  integers. The hypothesis is exactly `∀ n : ℕ, IsDerivedComplete I (K n)`.
- Its conclusion is `HasProduct K ∧ ∀ [HasProduct K], IsDerivedComplete I (∏ᶜ K)`.
  The first conjunct supplies product existence instead of assuming it. The second
  says the categorical product is complete for every choice of product structure;
  it uses Mathlib's product object, including its universal property and projections.
  The instance binder is inside the conclusion and is not an extra hypothesis.
- Clause (2)'s triangle is `T : Triangle (DerivedCategory (ModuleCat.{v} A))`, with
  `T ∈ distTriang (DerivedCategory (ModuleCat.{v} A))`. Its three objects are
  `T.obj₁`, `T.obj₂`, `T.obj₃`, and its last morphism has target `T.obj₁⟦1⟧`.
- The three implications explicitly render the three possible pairs: first and second
  imply third; first and third imply second; second and third imply first. There is
  no requirement that any one of these pairs already be complete outside the implication.
- No boundedness, regular-element, Noetherian, or finite-generation assumption appears.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the canonical shift, pretriangulated and triangulated
  instances. This implements `def-weil-abstract-derived-category`.
- `Sheaf.RingTheory.DerivedCompleteModuleComplex`:
  `DerivedCategory.IsDerivedComplete` (the recorded declaration of
  `def-weil-point-derived-complete-module-complex`). Its full definition was read,
  including the universal product-structure and derived-limit quantifiers.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `HasProduct`, `piObj`, `Pi.π`,
  `Pi.lift`, `Pi.map`, and the limit fan universal property;
  `Mathlib.CategoryTheory.Limits.Shapes.Countable`: `HasCountableProducts`.
  These implement the mathlib record of `def-weil-category-product`; only the
  product API used in this signature is directly imported.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`,
  `distTriang`, `Triangle`, and the TR1--TR3 fields, particularly rotation.
  The `IsTriangulated` signature in `Triangulated.lean` was also inspected.
  These implement `def-weil-triangulated-category`.
- The proof-only import is
  `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`, with the recorded
  `CategoryTheory.exists_isDerivedLimit_and_iso` and
  `CategoryTheory.derivedCategory_countableProducts_and_towerLimit`.
  Their signatures and proof docstrings were read. The future proof uses existence
  of countable products and uniqueness up to isomorphism of tower derived limits.
- `lem-weil-pbc-hom-into-triangle-exact` has a usable Mathlib match:
  `Pretriangulated.comp_distTriang_mor_zero₁₂`,
  `Pretriangulated.Triangle.coyoneda_exact₂`, and
  `Pretriangulated.Triangle.coyoneda_exact₁`, available through the public
  pretriangulated import. Their signatures match factorization and rotation.
- `lem-weil-pbc-module-localization-tower-vanishing` has neither a Lean record nor a
  Mathlib match yet. It is a proof dependency only, so no nonexistent module is
  imported; its intended use is recorded in the theorem's proof docstring.

Source and edge cases:

Read `literature/stacks-project/more-algebra.tex`, `lemma-hom-from-Af` (091P),
`definition-derived-complete` (091S), and the paragraph immediately following it.
The latter explicitly gives the triangulated subcategory and preservation under
products. It does not impose finite generation; the following proposition does,
which is a separate result. The 091P discussion explicitly handles unbounded complexes
using the two-term free resolution of A[1/f].

Checked the zero ring and zero complex: all conclusions reduce correctly to zero
objects. For `I = ⊥`, only multiplication by zero occurs, whose Roos endomorphism
is the identity, so every object is complete and closure is valid. For `I = ⊤`,
multiplication by one forces a complete object to be zero, again giving closure.
Nilpotent elements and zero divisors are allowed. No degree truncation occurs.
The node's product is indexed by positive integers, so its index set is not empty;
zero factors and an all-zero family remain allowed. The type universes follow the
recorded completeness definition without adding a size restriction.

Searches for existing statements (2026-10-15):

- `msearch.py ... leanfinder "Derived complete module complexes over a commutative
  ring are closed under countable products and distinguished triangles"`: eight hits,
  all general derived-category declarations (`HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, and boundedness/T-structure
  declarations); no closure statement for arbitrary-ideal module completeness.
- `msearch.py ... loogle "DerivedCategory, IsDerivedComplete"`: zero hits,
  unknown identifier `IsDerivedComplete` in the search index.
- `msearch.py ... grep "IsDerivedComplete|derivedComplete|DerivedComplete"`:
  zero Mathlib hits.
- `rg -n "IsDerivedComplete|derivedComplete|DerivedComplete"` in upstream
  `WeilConjectures` and project `lean/Sheaf`: the project has the reused definition
  in `DerivedCompleteModuleComplex.lean`; no product/triangle closure theorem.
  Upstream has sheaf completeness and the narrower principal-ideal comparison.
  Read `WeilConjectures/CategoryTheory/DerivedCategory/Complete/Principal.lean`,
  including `derivedComplete_iff_rightOrthogonal` and
  `isTriangulated_derivedComplete`: they concern sheaves on a site, with a principal
  ideal generated by a nonzerodivisor. They do not state this module result for any
  ideal. Read `Complete/Defs.lean` to verify its coefficient-sheaf meaning.
- `grep -rn "lem-weil-pbc-module-derived-complete-products-triangles"` in upstream
  `WeilConjectures`: zero hits.
- `rg -n "IsDerivedComplete|isDerivedComplete" dag/lean_names_upstream.json`:
  zero hits. The chosen full declaration name is new.

No statement fault, correction, or STATEMENT-DISPUTED issue was found.
All writes are confined to the assigned sandbox. Compilation uses `scompile.py`
on the server only, nice 19, two threads, 60 seconds per file. The initial server
compile passed with no errors or warnings; the final dry run verifies the final file.

## Second reading by ND

Independently read the node, the delivered module, Stacks More on Algebra
`lemma-hom-from-Af` (091P), `definition-derived-complete` (091S), and the
surrounding section. The section introduces an arbitrary ring, object of D(A),
and element f. The closure paragraph assumes no finite generation or boundedness;
finite generation first appears in the subsequent, separate proposition.
The node explicitly specializes to a commutative ring, as does the Lean.

Object/hypothesis/conclusion checklist, in node order:

- Commutative ring A: `{A : Type u} [CommRing A]`. Exact match, including the zero ring.
- Arbitrary ideal I: `(I : Ideal A)`. Exact match; no FG, principal, regularity,
  Noetherian, or characteristic hypothesis occurs.
- Ambient unbounded D(A): `DerivedCategory (ModuleCat.{v} A)` under
  `[HasDerivedCategory.{w} (ModuleCat.{v} A)]`. Read the abstract-derived-category
  dependency node and Mathlib Basic's `HasDerivedCategory`, `DerivedCategory`, `Q`,
  `mem_distTriang_iff`, and shift/triangulated instances. This is localization of
  all integer-indexed module complexes, with the node's chosen morphism universe.
  The size binder specifies the ambient category, not a mathematical restriction.
- Derived I-completeness: `DerivedCategory.IsDerivedComplete I`. Read the dependency
  node and both definitions in `Sheaf.RingTheory.DerivedCompleteModuleComplex`.
  Its predicate quantifies over f in I, all constant-tower product structures, and
  all objects satisfying `IsDerivedLimit` for transitions `f • 𝟙 K`; these must be
  `IsZero`. Read the latter's Roos-triangle definition too. This is exactly the
  node's module-complex notion, not the coefficient-sheaf completion predicate.
- Clause (1), family indexed by positive integers: `K : ℕ → DerivedCategory ...`.
  Index n corresponds bijectively to n+1, so no factor or case is lost.
- Clause (1), all factors complete: `(∀ n : ℕ, IsDerivedComplete I (K n))`.
  This hypothesis precedes the conclusion, with no hypothesis on an individual factor.
- Clause (1), product complete: `HasProduct K ∧ ∀ [HasProduct K],
  IsDerivedComplete I (∏ᶜ K)`. Read the category-product dependency record and Mathlib
  Products' `HasProduct`, `piObj`, projections and universal lift. The conjunction
  makes explicit the product existence implicit in 'its product'; the internal
  binder covers any choice, whose products are uniquely isomorphic. It assumes
  no product existence externally and adds no mathematical closure assertion.
- Clause (2), distinguished triangle: `T : Triangle ...` and
  `T ∈ distTriang ...`. Read the triangulated-category dependency and Mathlib
  `Pretriangulated`/`distTriang`, together with the derived-category instances.
  These are the prescribed objects and arrows, including the last target X[1].
- Clause (2), any two imply the third: the three conjuncts are precisely
  `(complete T.obj₁ → complete T.obj₂ → complete T.obj₃)`,
  `(complete T.obj₁ → complete T.obj₃ → complete T.obj₂)`, and
  `(complete T.obj₂ → complete T.obj₃ → complete T.obj₁)`.
  All three cases are present under the same distinguished-triangle hypothesis.
- Final absence of boundedness and finite-generation requirements: verified by
  inspecting every binder and the actual completeness definition. Exact match.

Edge cases: the node fixes a countably infinite positive-integer index set, so an
empty family is outside its quantified clause; n=0 in Lean supplies its first
factor. Zero factors, the all-zero family, zero objects in triangles, the zero
ring, I=0, I=A, nilpotent elements and zero divisors are all admitted. For I=0,
the zero-transition Roos map is the identity; for I=A, f=1 forces completeness
only for zero objects. Neither case contradicts the closure clauses. Arbitrary
integer degrees and all characteristics remain available. Universes u, v, w are
explicitly bound, independent, and follow the existing dependency signatures;
there is no forced field or fixed small ring. Empty schemes are inapplicable:
this is a statement about modules over a ring, with no scheme parameter.

Independent duplicate searches (2026-10-15):

- LeanFinder through msearch: 'Objects right orthogonal to localizations of a ring
  are closed under products and exact triangles'. Eight hits, including generic
  `ObjectProperty.instIsTriangulatedClosed₂RightOrthogonal` and
  `instIsTriangulatedRightOrthogonalOfIsStableUnderShiftInt`; these require a
  separate identification with this particular module-completeness predicate.
- Loogle through msearch: '"IsDerivedComplete"': zero hits.
- LeanSearch through msearch: 'Derived completeness for an arbitrary ideal is
  preserved by products and satisfies two out of three in exact triangles':
  unavailable (Internal Server Error), recorded as unavailable without a verdict.
- msearch grep 'derived.*[Cc]omplete|[Cc]omplete.*derived': zero Mathlib hits.
  Independent rg of upstream WeilConjectures, project lean/Sheaf, and the upstream
  name index for `IsDerivedComplete`, this theorem name, and completeness with
  products/triangles finds the reused project definition and upstream sheaf
  completeness, but no exact theorem. Read upstream Complete/Defs' predicate and
  Principal's `derivedComplete_iff_rightOrthogonal` and
  `isTriangulated_derivedComplete`, including their hϖ/hI binders. Those specialize
  to sheaves and a principal ideal generated by a nonzerodivisor; they cannot
  replace the arbitrary-ideal module result.

Proof dependencies checked: read the derived-limit-existence node and its module's
`exists_isDerivedLimit_and_iso` and
`derivedCategory_countableProducts_and_towerLimit`. They supply precisely the
existence and uniqueness assertions used in proof step 1. The Hom-exactness node
has the Mathlib matches `comp_distTriang_mor_zero₁₂`, `coyoneda_exact₂`, and
`coyoneda_exact₁`; read the latter signatures and their distinguished-triangle
context. The localization-tower-vanishing node remains unstated and is a proof
rather than statement dependency; its use is recorded in the docstring, with no
invented substitute or unavailable import. There are no new nodes or dependency
modules in this delivery, and no statement correction requiring citer review.

No mathematical or signature mismatch found; no Lean or node change was needed.
The module introduces no definitions and proves nothing: its only theorem ends
in `sorry`. Its source/blueprint docstrings reproduce all four proof steps,
including exact products, the localized Hom test, projection uniqueness, shift
stability and both triangle rotations. No private definition, local notation,
local instance, unbound variable, or extra hidden mathematical assumption occurs.
The node's `lean.statement` is verbatim the theorem signature before `:= by`.
Server compilation via scompile.py passed: nice 19, two threads, 60 seconds per
file; the delivered module compiled cleanly with no warnings or errors.
