## What changed

Proved two of the three existing theorem holes in
`Sheaf.AlgebraicGeometry.ConductorNormalizedResolutionExtension` using the declared
proof dependencies, without changing any public signature or definition.

`AlgebraicGeometry.rationalConductor_geometry` obtains coherence, nowhere density,
and the normality criterion from `conductor_smooth_base_change`. It converts the
closed nowhere dense support into a dense complement and applies
`Scheme.IdealSheafData.normalizedBlowup_calculus` for normality, reducedness and
finite type of the actual preparation.

`AlgebraicGeometry.rationalConductor_smoothBaseChange` proves quasi-compactness of
its source map using Noetherianity of the rational source. It applies conductor
base change, then the unique normalized-blowup comparison and its cartesian and
smooth properties. The commutativity equation of any competing cartesian square
proves uniqueness. This uses the hypotheses exactly as stated: no compatibility
of the chosen rational structure maps is assumed or added.

Two proved private helpers establish Noetherianity of a rational input and finite
generation of affine ideals. These implement steps 1--2 of the existing node.
The public proofs implement steps 1--2 and 4 of that plan, so no DAG route changes
are needed. All constructions still use the actual normalized conductor blowup.

Searched with the required msearch leanfinder, loogle and grep queries, and searched
the source and statement libraries. LeanFinder returned relative normalization
maps; Loogle and Mathlib grep found no conductor-resolution result. The sibling
quasi-excellent extension has different rule hypotheses and its corresponding
assembly theorem is also unfinished. No shorter applicable theorem was found.

Validation: the first version compiled in 7.5 seconds; the final version is checked
again after removing its unused private import. No new statement, case restriction,
choice of unproved data, or shared-module change is introduced. Empty and
disconnected inputs, and smooth maps without an explicit structure-map equation,
remain covered by the same universal proofs.

## Proved and sorry left

Closed two existing holes:

- `AlgebraicGeometry.rationalConductor_geometry`.
- `AlgebraicGeometry.rationalConductor_smoothBaseChange`.

One original hole remains unchanged:

- `AlgebraicGeometry.conductor_normalizedResolution_extension`, node
  `lem-trf-conductor-extension-of-normalized-resolution`. Its sourced eight-step
  proof remains in its docstring and node. The conductor-prepending tower and its
  coherent ordered comparison laws still require formal assembly.

No holes added or split off. This is a partial delivery: 2 of 3 original holes
closed, 1 remaining. The two new private helpers are completely proved. The proof
dependencies retain their own existing proof status.

## No longer needed

Removed the unused private import `Mathlib.AlgebraicGeometry.PullbackCarrier`.
The implemented proofs use only categorical pullback commutativity, already
available through the statement imports, rather than scheme pullback carrier
surjectivity. No mathematical node or module is declared globally unnecessary:
the existing surjective-base-change dependency is still part of step 8 of the
unchanged remaining assembly proof. All other imports are used by the public
statements or the two completed proofs; no public import is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The existing dependency declarations fit
the two proofs. The Noetherian-source quasi-compactness instance directly supplies
the affine-open compactness argument already planned by the node. The unfinished
final assembly is explicitly reported rather than counted as a proof.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
