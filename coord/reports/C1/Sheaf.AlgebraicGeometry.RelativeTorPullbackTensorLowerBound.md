## What changed

Proved `AlgebraicGeometry.Scheme.exists_relativeTor_pullback_tensor_lower_bound`
in `Sheaf.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound` from one new
homology-comparison theorem, imported privately. The proof unpacks the actual
relative Tor definition, chooses its lower endpoint before introducing F,
applies its vanishing assertion to the actual inverse-image module, transports
zero homology through the comparison, reflects zero through the faithful
abelian-sheaf functor, and applies `DerivedCategory.isGE_iff`.
No existing statement, definition, visibility or public import changed.
Updated the parent node to record this proof. Added a separate comparison module
and node for the unresolved scalar-restriction/derived-tensor comparison.
Both modules compile through lcompile.py in import order.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_relativeTor_pullback_tensor_lower_bound`
(node `lem-pc-relative-tor-pullback-tensor-lower-bound`).
No sorry remains in the item's module.

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.Scheme.relativeTensorPullback_homology_comparison`
(node `lem-pc-relative-tensor-pullback-homology-comparison`).
This is a decomposition: one hole closed, one added, net zero.
The new statement has no Tor-amplitude or boundedness hypothesis and concludes
an isomorphism in each individual degree, not a uniform bound or an existence
of bounds. It is strictly the comparison step of the original argument.
The finite interval extraction, its application to inverse-image modules, the
uniformity quantifiers, and the faithful reflection of homology vanishing are
proved in the original module. No sorry is placed inside a definition.

## No longer needed

None. No original import was removed. The original resolution and comparison
nodes remain needed in the proof plan of the new comparison theorem:
`lem-pc-kflat-bounded-flat-replacement`, `lem-pc-flat-complex-derived-pullback`,
`lem-pc-kflat-derived-tensor-comparison`; bounded-above K-flatness and pullback
preservation remain transitively used by the flat-complex and inverse-image
lemmas. Thus these are moved below the comparison, not pruned.
The new comparison module does not import FiniteTorDimensionOver: it does not
mention that predicate and does not depend on its interval.

## Where the brief, the DAG or earlier work was wrong

The original plan's listed declarations do not state the relative
scalar-restriction tensor comparison used in its second step. In particular,
KFlatDerivedTensorComparison compares tensors over O_X; it does not compare
with a K-flat resolution over f-inverse O_S. The new node isolates this missing
step, directly supported by Stacks Cohomology Lemma 20.27.4, Tag 08DE:
https://stacks.math.columbia.edu/tag/08DE (also used in Tag 08EV).
The repository's literature directory contains the citation lists but not the
Stacks TeX files, so the cited Stacks pages were read online.
No unit-level route has changed: the relevant unit's realized statement and
steps do not name this auxiliary node, and the same relative tensor argument
is retained. Edge cases checked mathematically: empty source and zero modules
produce zero sheaves on both sides; arbitrary unbounded K and P are allowed
because the second-factor resolution is K-flat. No flatness of O_X over the
inverse-image ring, quasi-coherence, properness or Noetherian assumption enters.

## New nodes

`lem-pc-relative-tensor-pullback-homology-comparison`, in
`dag/nodes/sec-picard-framework/`, is stated in
`lean/Sheaf/AlgebraicGeometry/RelativeTensorPullbackHomologyComparison.lean`.
It identifies underlying abelian homology sheaves for tensor with a derived
pullback and tensor computed by a specified K-flat restricted-scalars
resolution. Its docstring and node give the resolution zigzag and tensor
associativity proof, sourced to Tags 08DE and 08EV. No interface change record
is needed: existing signatures and definitions are unchanged.

## Second reading by C1

1. Compared both delivered modules and the parent node with the repository.
   The only existing Lean declaration has its signature, docstring and visibility
   byte for byte unchanged; its proof and a private import are the only changes.
   There are no definition or target changes, forced adaptations or change records.
2. Compiled both modules locally in import order. Scratch-copy `#print axioms`
   checks for both declarations report exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter is expected from the named open
   comparison and existing imported proofs. No forbidden declarations or hollow
   definitions occur. Exactly one named theorem remains sorry, as listed above.
3. Read the new comparison and its resolution-zigzag proof against the fixed
   tensor and pullback constructions and Stacks Tags 08DE and 08EV. Verdict:
   true, with no missing flatness assumption on the structure map. For identity
   maps it reduces to K-flat resolution invariance; for zero F, zero E or empty
   X both sides have zero homology. Unbounded K and P cause no problem: the
   K-flat second resolution makes tensoring the restricted resolution zigzag
   preserve quasi-isomorphisms. This is a strictly separate comparison step,
   not the original uniform lower-bound assertion under another name.
   Independent leanfinder search for derived extension-of-scalars associativity,
   loogle search for SheafOfModules.restrictScalars, and grep searches for relative
   tensor and scalar-restriction tensor comparisons found no existing exact
   theorem. Existing pullback associativity and inverse-image comparisons do
   not compare tensor over the two different rings. Closing this comparison
   requires constructing the balanced tensor complex comparison, beyond a
   short repair; it remains explicitly open.
4. Checked the proof from the interval extraction down through degreewise
   vanishing and faithful reflection. No simpler existing route was found.
   Every import supports the signature or the proof; the new comparison import
   is private. The old proof dependencies moved below the comparison are
   lem-pc-kflat-bounded-flat-replacement, lem-pc-flat-complex-derived-pullback,
   lem-pc-bounded-above-flat-kflat, lem-pc-kflat-pullback-preservation, and
   lem-pc-kflat-derived-tensor-comparison. None is pruned: bounded-above
   K-flatness is used by flatComplexDerivedPullback, and pullback K-flatness
   by exists_inverseImage_exact_kFlat. Checked the unit's realized fields:
   neither the parent nor the comparison realizes a unit statement or step;
   the unit route is unchanged.
5. Checked the two nodes against the Lean declarations. The parent's proof and
   proof_deps describe the actual interval/comparison/faithfulness argument;
   the new node records the genuinely remaining comparison, its source, full
   proof plan, declaration, searches, provenance and split status. Verdict: agree.

Second reading changed only this report by recording the independent checks.
The delivery remains a decomposition: one original hole closed, one lower
comparison hole added, net zero; no module pruned.
