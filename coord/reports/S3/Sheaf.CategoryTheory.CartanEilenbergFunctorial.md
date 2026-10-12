## What changed

Replaced the hole in `CategoryTheory.cartanEilenberg_lift` with a complete Lean
combination of augmented comparison, finite diagonal coproduct existence, preservation
of the first filtration by the differential, and preservation by the total map.
The original signature and all its public imports are unchanged.

Added four modules, each with one public theorem:

- `Sheaf.CategoryTheory.CartanEilenbergAugmentedComparison`: the comparison construction
  of Steps 1–3, without totalization or filtration conclusions. It does not assume
  source-column injectivity or separate bounds on the original complexes.
- `Sheaf.CategoryTheory.DoubleComplexBoundedBelowTotal`: fully proved finite diagonal
  existence from an arbitrary integer lower first-degree bound and nonnegative second
  degree. Its private coproduct helper is fully proved and its imports are Mathlib only.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationDifferential`: fully proved that the
  finite image-sum first filtration is a subcomplex, without quadrant hypotheses.
- `Sheaf.CategoryTheory.DoubleComplexFirstFiltrationMap`: fully proved preservation of
  the same filtration under any bicomplex map, without quadrant hypotheses.

The item imports these modules for proofs only. Its direct proof import of
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` moved to the augmented
comparison module, where it is needed. Updated the item's proof DAG to match this route.
All five modules compile locally without errors or warnings. The only new `sorry` is
one public theorem with source, complete proof in words, and its own node and module.

## Proved and sorry left

Closed the item's one hole, `CategoryTheory.cartanEilenberg_lift`
(node `lem-weil-pbc-cartesian-eilenberg-functorial`), by a decomposition with real,
fully proved totalization and filtration glue. This is one decomposition, not a
complete proof of the mathematical comparison theorem: one upper hole was closed and
one strictly smaller comparison hole was added, so the net hole count is zero.

Fully proved new declarations:

- `HomologicalComplex₂.hasTotal_of_boundedBelow`
  (`lem-weil-pbc-total-bounded-below`).
- `HomologicalComplex₂.firstFiltration_differential`
  (`lem-weil-pbc-total-first-filtration-differential`).
- `HomologicalComplex₂.firstFiltration_map`
  (`lem-weil-pbc-total-first-filtration-map`).

The sole `sorry` left in the delivery is
`CategoryTheory.exists_cartanEilenberg_augmented_comparison`
(`lem-weil-pbc-ce-augmented-comparison`). It covers the compatible column comparison
construction only. There are no holes in the item's module, private helpers, or
definitions. Existing holes in imported library modules are unchanged.

Edge cases: finite-diagonal existence permits a negative lower bound and the empty
diagonal n<a. The filtration proofs treat empty intervals by the finite supremum
universal property; they impose no first-quadrant assumptions. The comparison's
induction begins below a common lower bound, with the zero boundary column, and
retains each boundary comparison for its next use. It uses injectivity only in the
target columns, as required by the exact-source horseshoe lift.

## No longer needed

No whole existing DAG node or module is pruned: all three original proof dependencies
remain needed, directly or through the augmented comparison lemma.

The item's direct proof import
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` is removed from that
file, but remains imported by the augmented comparison module; it is not pruned from
the closure.

The proof does not use `HomologicalComplex₂.hasTotal_of_firstQuadrant` or
`HomologicalComplex₂.firstFiltration_subcomplex`. These declarations share the
still-needed `DoubleComplexTotal` definition module, so its node is retained.
The former's bound zero and the latter's first-quadrant hypothesis are not needed
for this item. No original public import was removed.

## Where the brief, the DAG or earlier work was wrong

The original totalization plan referred to the first-quadrant total-existence and
subcomplex interfaces, but the item allows arbitrary integer lower complex-degree
bounds. The new total-existence theorem handles those bounds directly. The new
subcomplex theorem proves the actual finite image-sum filtration formula without
any quadrant hypothesis, so no statement change or shift of indices is needed.

The original Step 3 mixed source and target names in its factorization
`I → J_B → J_Z → I`. The new comparison node says precisely that the source
factorization goes through its own boundary and cycle columns, with the analogous
target factorization and the chosen comparison squares between them.

Stacks Tags 015H and 015I describe the resolution and horseshoe construction;
015K asserts functoriality but does not spell out the full comparison proof.
The remaining lemma records the expanded argument from the existing node, including
the exact-source horseshoe lifts and the induction compatibility, rather than treating
015K as a supplied Lean comparison theorem. The proof_origin is marked agent for
these expansions. The unit `sk-prop-h2` and its realized route are unchanged.
LeanSearch returned Internal Server Error; the other search services and source
searches were used and their results recorded.

## New nodes

`lem-weil-pbc-ce-augmented-comparison` isolates the original Steps 1–3, strictly less
than the item's comparison-plus-totalization-plus-filtration conclusion. Its proof
uses the existing injective quasi-isomorphism lifting Mathlib node and exact-source
horseshoe node. Its module is
`lean/Sheaf/CategoryTheory/CartanEilenbergAugmentedComparison.lean`.

`lem-weil-pbc-total-bounded-below` is fully proved by the finite coproduct universal
property and zero-object factorization; no further hole is added. Its module is
`lean/Sheaf/CategoryTheory/DoubleComplexBoundedBelowTotal.lean`.

`lem-weil-pbc-total-first-filtration-differential` is fully proved from Mathlib's signed
total differential equations, subobject pullbacks and finite supremum inequalities.
Its module is `lean/Sheaf/CategoryTheory/DoubleComplexFirstFiltrationDifferential.lean`.

`lem-weil-pbc-total-first-filtration-map` is fully proved from
`HomologicalComplex₂.ιTotalOrZero_map` and the subobject universal properties.
Its module is `lean/Sheaf/CategoryTheory/DoubleComplexFirstFiltrationMap.lean`.

All four nodes are in `dag/nodes/sec-curve-estimates/`, with the item's chapter,
unit and blueprint ancestor. No definition or existing statement changed, so no
change record is required.

## Second reading by S3

1. Compared the existing module with the repository using `diff -u`: the entire
   `cartanEilenberg_lift` signature, docstring and public imports are byte-for-byte
   unchanged. Only its proof and private proof imports differ. All four other
   modules are new, and no existing definition or statement is changed. No change
   record is needed. Verdict: pass.

2. Independently compiled all five delivered modules with `lcompile.py --all`:
   no errors or warnings. Read every proof, including the private coproduct and
   sign-factorization helpers; scanned the delivery for forbidden declarations
   and for holes. The only new hole is the named public augmented comparison
   theorem. A scratch module printed the axioms of all five public theorems:
   `hasTotal_of_boundedBelow` uses only `propext`, `Classical.choice`, `Quot.sound`;
   the other four additionally use `sorryAx`, and no other axiom. In particular,
   the two filtration lemmas still depend on the existing open
   `firstFiltration_antitone` through the `firstFiltration` definition. Their
   own proof bodies have no holes, but they are not yet axiom-clean proofs of
   the entire import closure. The main theorem additionally uses the new
   comparison hole. No definition with holed data is added. Verdict: pass as
   a decomposition, not a completed target proof.

3. Read the comparison theorem, its complete docstring argument, its new node,
   and `exists_horseshoe_morphism_lift_exact_source` with its actual hypotheses.
   Read Stacks [015H](https://stacks.math.columbia.edu/tag/015H),
   [015I](https://stacks.math.columbia.edu/tag/015I), and
   [015K](https://stacks.math.columbia.edu/tag/015K): 015I gives the alternating
   boundary/cycle/original-object construction; 015K states functoriality but
   does not supply its comparison proof. The node correctly records the
   expanded comparison argument as agent-origin. The source need only have
   exact augmented columns; the target supplies injectivity in all four kinds
   of columns. The degreewise short exact sequences follow from the abelian
   cycle/image/homology sequences, and exact F transports them. Quasi-isomorphisms
   out of single-degree-zero complexes into nonnegative complexes are monic
   augmentations, so the injective quasi-isomorphism lift applies. The common
   lower bound makes the initial boundary column zero; all subsequent boundary
   maps are retained, so the two middle lifts use the same endpoints. This also
   covers zero complexes, different or negative lower bounds, F the identity,
   and noninjective source terms. There is no new totalization or filtration hole:
   the comparison is strictly a part of the original conclusion, and the omitted
   parts are proved by real Lean arguments. It cannot be closed in a few minutes
   merely by applying the two imported lemmas, since transporting and assembling
   the compatible column data remains to be formalized.

   Independently searched with LeanFinder for “extend morphism from exact
   augmented cochain complex into injective Cartan Eilenberg bicomplex”, and with
   Loogle for `HomologicalComplex₂, HasTotal`; the latter reported an unknown
   identifier rather than a usable result. Grep search for bounded-below,
   finite-support coproduct and injective-comparison terms, followed by targeted
   `rg` in Mathlib TotalComplex, upstream CategoryTheory and lean/Sheaf, found no
   existing full comparison. Read `horizontal_comparison_lift`: it assumes an
   existing bicomplex map and constructs a homotopy residual, so it does not
   replace this existence theorem. Mathlib's `hasTotal_of_iso` transports an
   already existing total and does not prove bounded-support existence.
   Verdict: the remaining statement is true and a genuine smaller obligation.

4. Checked the proof downward: finite support injects into [a,n], omitted
   summands are zero, and the finite coproduct has the full diagonal universal
   property. For n<a this is the empty coproduct. In the differential proof
   both signed components land at first degrees p and p+1 in [r,n+1]; in the
   map proof `ιTotalOrZero_map` keeps the same diagonal index. Pullback and
   finite-supremum inequalities then give exactly the three required equations,
   also when r>n. The four added imports are private proof imports; no
   proof-only import was made public. The original three dependencies remain
   in the proof closure: DoubleComplexTotal directly, and the exact-source
   horseshoe and injective quasi-isomorphism lift through comparison. Hence
   `No longer needed` is complete and no module is pruned. Read
   dag/units/sk-prop-h2.json: its realized statement and step lists are empty,
   and this delivery changes neither the unit nor its route. Verdict: pass.

5. Matched the main node's three proof steps to the actual comparison,
   extended vanishing/HasTotal construction, and filtration applications.
   The new total-existence node has no proof dependency beyond Mathlib; the
   two filtration nodes use the existing definition node; the comparison
   node retains the two actual comparison tools. Their proof_deps are the
   unions of their steps' uses, their proof_origin marks the expanded arguments,
   and their Lean records identify the matching statements and modules. All
   four new nodes have sources, searches, creation records, chapter/unit and
   blueprint ancestry. Verdict: pass.

Second reading changed this report only: added the independent review and the
explicit axiom limitation caused by the existing filtration definition. The
Lean proofs and node records required no repair. One original hole is closed,
one smaller hole is added; net zero, with three auxiliary proof bodies completed.
