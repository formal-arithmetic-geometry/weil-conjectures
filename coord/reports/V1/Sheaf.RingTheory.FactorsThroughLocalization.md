## What changed
Proved `Algebra.factors_through_principal_localization` directly in
`Sheaf.RingTheory.FactorsThroughLocalization`. The proof chooses a finite polynomial
presentation, clears the variable denominators using Mathlib, kills each of the finite
kernel generators after enlarging the principal denominator, and descends along the
surjective presentation. The existing signature, visibility, and docstring are byte for
byte unchanged from the repository. Added the proof-only import
`Mathlib.RingTheory.Localization.Integer`. Updated the existing node's proof outline and
proof origin to describe the actual argument; its proof dependencies remain empty.

## Proved and sorry left
Closed the one original hole: `Algebra.factors_through_principal_localization`, node
`lem-factors-through-localization-of-smooth`. Proved 1 of 1 original declarations;
0 holes added and 0 split-off statements remain. A scratch-copy `#print axioms` check
shows only `propext`, `Classical.choice`, and `Quot.sound`. This is a full proof, with
net one hole closed, rather than the first worker's one-for-one decomposition.

## No longer needed
No original imports, proof dependency nodes, or library modules were pruned: the original
node's `proof_deps` was empty. Removed the proposed proof-only import
`Sheaf.RingTheory.FactorsThroughPolynomialPresentation`, the proposed new module
`lean/Sheaf/RingTheory/FactorsThroughPolynomialPresentation.lean`, and its proposed node
`lem-factors-through-polynomial-presentation`. They never belonged to the baseline library.

## Where the brief, the DAG or earlier work was wrong
The first worker's polynomial-presentation theorem was an equivalent repackaging of the
original theorem: its extra presentation is precisely the output of
`Algebra.FinitePresentation.out`. Its proof sketch also did not isolate a strictly smaller
argument. Removed that split and implemented the denominator-clearing argument in full.
The original DAG route is valid and is followed; it did not require an additional node.

## Second reading by V1
1. Compared the delivered module with the repository using diff and an exact string check.
   The original theorem's signature and docstring are byte identical; universes, typeclass
   hypotheses, conclusion, public visibility, and both public imports are preserved.
   No existing definition or other module is changed and no change record is needed.
2. Compiled the replacement file through `lcompile.py` without errors or warnings.
   Scanned for holes and forbidden declarations: none. The scratch-copy axiom probe gives
   exactly `propext`, `Classical.choice`, and `Quot.sound`. All choices of witnesses are
   from proved Mathlib theorems; no data depends on an unproved existence theorem.
3. Rejected and removed the proposed single split-off statement because finite polynomial
   presentation is equivalent to the original finite-presentation assumption. Searched
   Mathlib through LeanFinder for localization descent, Loogle for finite-family
   localization facts, and grep for annihilator and surjective-descent interfaces. Read
   Mathlib's `Localization/Integer.lean`, `Localization/Defs.lean`,
   `Localization/Away/Basic.lean`, `FinitePresentation.lean`, and
   `Ideal/Quotient/Operations.lean`. Repository and upstream searches found no existing
   exact factorization theorem. No new statements remain to audit.
4. Checked each denominator-clearing step. The variable images have one common denominator;
   equality is checked by cancelling its unit image. A relation belongs to the kernel by
   the span identity, so its evaluated numerator maps to zero; the localization kernel
   criterion supplies an annihilator. The product denominator makes every annihilator a
   unit, killing all relations. Surjective descent then supplies the required algebra map,
   and localization extensionality and presentation surjectivity verify the composite.
   No nonzero denominator, injectivity, nonempty generators, or nonempty relations is
   assumed: empty finite families and zero rings are covered by these same interfaces.
   Imports are minimal and the sole added import is private to the proof. The original
   proof dependencies are empty, so the list of old nodes no longer used is empty.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized unit statement or
   step, and the original denominator-clearing route is retained without changing realized.
5. The existing node now records the three actual proof phases, has empty `proof_deps`
   matching their empty `uses`, and retains its source origin. No other node fields are
   changed. The proposed new node and module have been removed, so the DAG and Lean agree.

Second-reading changes: replaced the equivalent decomposition with a complete proof,
removed its new module/node/import, restored the original docstring, added the private
Mathlib integer-denominator import, and corrected the node proof outline and this report.
