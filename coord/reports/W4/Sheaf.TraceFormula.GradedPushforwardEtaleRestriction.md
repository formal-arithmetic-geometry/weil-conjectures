## What changed

Reduced `AlgebraicGeometry.AlgebraicSpace.graded_pushforward_etale_restriction_line_powers`
to two strictly smaller geometric steps and the existing general graded restriction theorem.
The Lean assembly constructs the canonical source algebra, obtains the general base-change
structure, compares its restricted powers with the actual powers, and proves the final
evaluation equation by `CategoryTheory.Adjunction.counit_naturality`.
The theorem's signature, including its line-module hypothesis, is unchanged.

Added `Sheaf.TraceFormula.CanonicalEtaleLinePowerAlgebra` and
`Sheaf.TraceFormula.EtaleLinePowerComparison`, one named theorem in each.
The first constructs canonical products using the local rank-one hypothesis; the second
compares powers for a single étale map, given those products. Neither theorem mentions
`f`, a base-change square, direct images, coproducts, or the evaluation square.
Their combination with the general theorem is the specialization, rather than a renamed
copy of the original hole.

Moved `gradedPowerChartIso`, `gradedPowerOneIso` and `HasCanonicalEtalePowerProducts`
verbatim to `Sheaf.TraceFormula.EtalePowerProductNormalization`. The original item publicly
imports that module, preserving all three public names, signatures and construction bodies.
This avoids a circular import from the new lemma modules into the theorem they support.
The change record is `coord/changes/graded-etale-power-normalization-location.md`.
No other existing Lean module changes. There are no current direct Lean importers of
the assigned item; DAG parents remain attached and still need it.

## Proved and sorry left

Original holes: 2. Closed bodies: 1. New holes: 2. This is a decomposition, not a
sorry-free geometric proof, with net progress of 1 closed minus 2 added = -1; 3 holes remain in the packet.

The body of `AlgebraicGeometry.AlgebraicSpace.graded_pushforward_etale_restriction_line_powers`
is complete. In particular, its final evaluation equation is proved by the actual
adjunction counit's naturality, for each degree.

Every hole remaining in this packet:

- `AlgebraicGeometry.AlgebraicSpace.graded_pushforward_etale_restriction`
  (`lem-trf-graded-pushforward-etale-restriction`): the general theorem is unchanged.
- `AlgebraicGeometry.AlgebraicSpace.canonical_etale_line_power_algebra`
  (`lem-trf-canonical-etale-line-power-algebra`): new canonical power-algebra construction.
- `AlgebraicGeometry.AlgebraicSpace.etale_line_power_comparison`
  (`lem-trf-etale-line-power-comparison`): new single-map tensor-power comparison.

All four modules compiled remotely with no errors or warnings (normalization 5.3 s,
canonical algebra 2.7 s, power comparison 6.9 s, assigned item 55.8 s).
A profiled single-file check also compiled the item in 20.1 s, with about 10 s of
elaboration and 6 s of type checking; the temporary profiler settings were removed.
The normalization module has zero holes. All three remaining holes are complete bodies
of named public theorems, each with a source, a proof in words and a matching node.
No new axiom or hollow definition is introduced.

## No longer needed

Removed these unused proof-only imports from the assigned module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Sheaf.AlgebraicGeometry.SpaceChartTensorRealization`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

No mathematical dependency node or module is claimed pruned: the general theorem's
unimplemented Steps 1--5 retain their planned dependencies, and the new tensor-power
lemmas still need localized tensor comparisons and the bilinear universal property.
No source-library declaration or module is removed. All original public imports stay.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool error was found. The existing proof sketch did not isolate
construction of the canonical ordinary commutative algebra on powers of a line module.
That step needs the line hypothesis: tensor powers of an arbitrary module are generally
not ordinarily commutative. The new construction lemma records that hypothesis, and the
specialization now uses its original `_hL` argument.

The final equation of the specialization needs only naturality of the already specified
adjunction counit. It needs no new chart-generation or tensor-normalization theorem.
The general theorem remains open; this packet does not claim to implement its Steps 1--5.

Read the current Stacks sources: `spaces-descent.tex`, `lemma-descending-property-ample`
(Tag 0D3C), and `sites-modules.tex`, `lemma-tensor-product-pullback` (Tag 03EL) and its
preceding tensor universal property. Checked degree zero, products with either degree
zero, the first-power unitor, a trivial line on an affine chart, the identity étale map,
and empty sites. The comparison lemma assumes a canonical source algebra and its
restricted operations, so it does not assert commutativity of arbitrary tensor powers.
No quasi-compactness, quasi-coherence, surjectivity or global section decomposition is used.

Mathlib searches ran through `msearch.py`: LeanFinder for canonical line-power algebras
and étale tensor comparison (8 unrelated differential/étale algebra hits), Loogle for
`"tensorPowNat"` (0 hits), and grep for tensor powers/canonical powers (15 unrelated
algebraic power constructions). A separate Loogle search for counit naturality found
`CategoryTheory.Adjunction.counit_naturality`, which is used directly. Searches of the
Lean roots and the imported blueprint did not find these two normalized sheaf statements.

## New nodes

`def-trf-etale-power-product-normalization` owns the three unchanged normalization
definitions extracted from the assigned module. It introduces no additional mathematical
data and has no holes.

`lem-trf-canonical-etale-line-power-algebra` constructs the canonical homogeneous algebra
on the actual tensor powers of a locally free rank-one étale module. Its proof in words
constructs the products and unit via the small-site equivalence, checks the tensor
coherence laws, and proves ordinary commutativity locally using a line generator.

`lem-trf-etale-line-power-comparison` isolates the normalized tensor-power comparison
for one étale morphism, given a canonical source algebra and its restricted products.
Its proof in words iterates the localized tensor comparison and transports the algebra,
checking products, degree zero and the first-power unitor on local tensors.

The item node retains the general proof plan and updates Step 6 to the implemented
specialization. The unit route is unchanged. The declaration relocation is recorded in
`coord/changes/graded-etale-power-normalization-location.md`.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
