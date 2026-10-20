## What changed

Retired Sheaf.AlgebraicGeometry.EtaleStratifiedFinite, the explicitly listed retirement
item, in favor of WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite. Their complete
declaration sections are byte-identical. Redirected the private import line in the
five current direct consumers: FrobeniusVectorBundleKernel,
NoetherianAffineFreePresentation, NoetherianConstructibleGaloisPartition,
NoetherianEtaleSumConstructible and Paper.CoherentSetCriterion. Rebound the existing
node's lean.module and lean.file to the adopted provider; all other node fields remain
unchanged. No source-library module is edited.

Validation: the current duplicate and all five adapted consumers compile remotely
through lcompile.py (2.5, 4.6, 3.1, 3.8, 3.4 and 4.0 seconds). A fresh copy of the complete
adopted provider compiles in 2.0 seconds and prints only propext, Classical.choice and
Quot.sound. An exact-old-signature application probe checks the replacement. The
required delivery checks are run before pushing.

The first dry run identified pre-existing imports of the policy-dropped module
Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType in
NoetherianAffineFreePresentation and NoetherianEtaleSumConstructible. Removed those two
unused private imports: their declaration occurs nowhere in the consumers, whose
main proofs remain admitted. No statement, definition or proof body changes.
All five consumers are unclaimed; this adds no adaptation to a module held elsewhere.
After those removals, all five consumers compiled again successfully (0.2, 4.4, 0.8,
3.8 and 0.9 seconds respectively in the compiler output order).

The repaired dry run passed: commit 82b59a54663 compiles and passes preflight,
classified CODEX for independent review. Its appended axiom probe for the existing
FrobeniusVectorBundleKernel consumer timed out after 60 seconds; the consumer itself
compiled successfully, and the delivery tool states that the merge reruns that probe.
The freshly compiled adopted stratification theorem and exact-signature probe both
printed only the three permitted axioms. No slow or timed-out file compilation is
being excused here; the probe limitation is reported for the independent reviewer.

Change record: coord/changes/D8-retire-etale-stratified-finite.md.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off; zero holes
left in the retiring item. AlgebraicGeometry.Scheme.exists_etale_stratified_finite
(node lem-weil-pbc-etale-stratified-finite) retains its existing complete adopted-source
proof. This is duplicate retirement, not a new proof or a decomposition. The existing
holes in untouched consumer proofs are unchanged and are not claimed as closed.

## No longer needed

Withdraw the duplicate module Sheaf.AlgebraicGeometry.EtaleStratifiedFinite, including
its three private proved helpers. Its four public imports and six proof imports are
removed with that duplicate; the adopted proof retains the same imports. They are:

- WeilConjectures.AlgebraicGeometry.LocallyClosedStratification (public).
- Mathlib.AlgebraicGeometry.Morphisms.Etale (public).
- Mathlib.AlgebraicGeometry.Morphisms.Finite (public).
- Mathlib.Topology.Constructible (public).
- WeilConjectures.AlgebraicGeometry.EtaleAffineCoverStratification (proof).
- WeilConjectures.AlgebraicGeometry.EtaleSeparatedStratifiedFinite (proof).
- WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluing (proof).
- Mathlib.AlgebraicGeometry.Cover.Open (proof).
- WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly (proof).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting (proof).
 The five
consumer imports of the Sheaf provider are replaced by the upstream provider.
Also removed the two unused imports of the policy-dropped
Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType identified above.
Its planned mathematical result is not withdrawn by this delivery; the consumers
retain their original statements and DAG plans for their subsequent proof work. No
mathematical dependency node becomes unnecessary: affine-cover separation, separated
finite-etale stratification, partition assembly, affine-local gluing and pullback
pasting remain exactly as in the node's proof. No upstream declaration or proof is
removed, and no unit statement or step is bypassed.

The twelve actual DAG parents, the unit record and five quarantined direct consumers
were checked. The five archives (TopologicalStratifiedLisseLattices,
ContinuousLissePullbackSystem, ContinuousLisseStratifiedLattices,
LisseEConstructibleIntegralLattice, StratifiedLattice) remain untouched, with all
attachments and dependencies preserved. Their restoration must redirect the old
private import to the now-canonical upstream provider; they are not treated as
withdrawn or unused. The mathematical replacement argument is the same full existing
proof, with identical hypotheses and conclusion, and the node attachment is updated
in this delivery.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module containing a hole, but this assignment
is listed as retire and currently has zero holes. The historical DIFFERENT label
predates the current synchronization: the entire declaration section now agrees
byte for byte with its adopted twin. The theorem was already proved by U2; no new
proof credit is claimed. The library search found that exact adopted replacement;
LeanFinder and Loogle found no shorter Mathlib stratification theorem. The node's
mathematics and fixed unit route require no correction.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
