## What changed

Repair of the import-prune return: removed the private duplicate declarations
`transport_left_naturality` and `descent_orbit_saturated`, and imported their existing
modules as proof imports. All calls now use the existing public theorems. The DAG
records both existing theorem nodes as proof dependencies. Both sandbox modules
compile cleanly through lcompile.py. No existing public signature or visibility changes.

Replaced the original sorry in
`CategoryTheory.Over.DescentDatum.exists_descent_norm_affine_shrinking` by the empty-set
case, transport naturality, groupoid composition and inversion, invariant closed-image
interior, and upstream finite prime avoidance. Its signature and docstring are unchanged.

The second reader repaired the false new affineness statement: containment in a basic
open alone does not imply affineness. The remaining norm argument now lives in the new
module `Sheaf.AlgebraicGeometry.DescentNormLocusAffine`, imported only for the proof.
It requires the exact norm-locus equality, a domain W where the pullback of f is
well-defined, D(f) contained in W, and the locus contained in D(f). The original proof
supplies these hypotheses, including exchanging source and target images by inversion.

## Proved and sorry left

Hole closed: `CategoryTheory.Over.DescentDatum.exists_descent_norm_affine_shrinking`.
Hole added: `CategoryTheory.Over.DescentDatum.isAffineOpen_descent_norm_locus`, node
`lem-pd-descent-norm-locus-affine`, in `Sheaf.AlgebraicGeometry.DescentNormLocusAffine`.
This is a decomposition (one hole closed, one added; net zero), not a sorry-free proof
of the original theorem. The original module has no remaining sorry.

The private helper `descent_inversion` is proved without sorry. Naturality and orbit
saturation use the existing public theorems `transport_left_naturality` and
`descent_orbit_saturated`, which are already proved in the library. The two duplicate
private proofs have been removed. The upstream prime-avoidance theorem is also proved.
The original theorem and the new norm-locus theorem additionally use sorryAx, from
the explicitly reported remaining theorem. There are no definitions or data selected
from an unproved existence theorem in this delivery.

## No longer needed

Removed proof import `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
no fibre degree or bound is used. No old proof_deps node is dropped: the groupoid,
fibre product and finite locally free definitions are used, the finite closed-map
node is realized by Mathlib's finite/proper instance and closed-map theorem, and
prime avoidance by upstream `IsAffineOpen.exists_basicOpen_le_of_finite`.
No claim is made that FiberDegree is unreachable from all other targets.
Removed the direct proof import `Mathlib.AlgebraicGeometry.PullbackCarrier`: its only
direct use was in the duplicate orbit-saturation proof, now removed. No further nodes
or modules are pruned; the two existing theorem modules are needed and reused.

Added proof imports: `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Sheaf.AlgebraicGeometry.DescentNormLocusAffine`,
`Sheaf.AlgebraicGeometry.DescentOrbitSaturated`, and
`Sheaf.AlgebraicGeometry.TransportLeftNaturality`. Each supplies a used theorem or instance.
All existing public imports are required by the original signature and retained.
The field-extension norm specialization in `WeilConjectures.AlgebraicGeometry.BaseChangeNorm`
cannot handle arbitrary finite locally free morphisms and a nonaffine W.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two theorems already stated and proved in the library.
The repair reuses those declarations rather than repeating their proofs, as requested.

The first worker's `isAffineOpen_descent_norm_locus` asserted that any open U contained
in D(f) was affine. With identity descent, A the affine plane over a field, f = 1,
and U the complement of the origin, its hypotheses hold but U is not affine.
The docstring's identification with a norm locus was absent from the Lean hypotheses.
That undelivered statement has been replaced, not assumed. The corrected intermediate
is precisely the determinant-norm subclaim of Stacks Tag 03JE. No existing statement
or definition changed, and no change record is needed for this new undelivered theorem.

## New nodes

`lem-pd-descent-norm-locus-affine`: affineness of the explicitly identified norm locus
for a finite, flat, locally finitely presented source map. It asserts neither finite-set
prime avoidance nor invariant neighbourhood existence, so it is strictly part of the
original argument. Its node contains the verbatim signature, source, complete determinant
argument, and the three kinds of searches, including this reader's new queries.
No change records.

## Earlier second reading (a previous round; superseded)

1. Compared the sandbox module with the repository version. The original theorem's
   signature and docstring are byte-for-byte unchanged. No existing definition changed.
   The new undelivered theorem was false and has been repaired as explained above;
   it has also been moved to its own module as the brief requires.
2. Compiled both modules through lcompile.py in import order, without errors or warnings.
   Inspected all declarations: the only sorry is the named norm-locus theorem, with source,
   complete proof docstring and matching node. No axiom, unsafe, opaque, extern,
   implemented_by, hidden sorry, or hollow definition. Printed axioms in a scratch copy:
   all private helpers and upstream prime avoidance use only the three allowed axioms;
   the two public theorems additionally use sorryAx, as expected for this decomposition.
3. Read Stacks Tag 03JE against the repaired statement. Finite/flat/local finite
   presentation gives a determinant norm on W; hWA makes t* f defined there; hUset
   supplies exactly its nonvanishing set; hfW allows restriction to affine D(f), and
   hU keeps the same locus. Checked identity maps (the equality forces U = D(f)),
   f = 0 (empty locus), f a unit, empty W/R, and rank-zero components. Thus the
   punctured-affine-plane counterexample is excluded. Searched leanfinder, loogle,
   grep, lean/Sheaf, and the upstream BaseChangeNorm module using different wording.
   Found the basic-open and prime-avoidance results already used, but no general norm
   gluing theorem that closes the remaining hole. The intermediate is strictly smaller
   than the original statement and does not restate it.
4. Read downward through the proof: actual transport laws establish composition,
   inversion, identity and saturated orbits; finite closed images give invariant
   interiors; upstream prime avoidance gives D(f); the remaining norm theorem supplies
   affineness alone. The finite-field-extension norm route is too specialized.
   Checked every import against its use and recorded the removed FiberDegree import.
   Every old proof_deps node remains used. Read sk-prop-jacobian-descent.json: its
   realized arrays are empty; this delivery alters none of its steps or route, and
   retains effective descent's norm-shrinking step.
5. Updated the existing node's proof and proof_deps to include the actual set-theoretic
   reduction and the norm-locus node. Updated the new node's statement, dependencies,
   proof, source, searches, module/file, and verbatim Lean signature to match the repair.
   No signature is silently changed and the original statement still matches its Lean.

Changes by this reader: removed the false unrestricted affineness lemma; stated its
correct norm-locus replacement in a separate module; proved the source/target image
exchange and all replacement hypotheses in the original reduction; repaired DAG and
report, including the net-zero decomposition and the actual pruned import.

## Second reading by X3

1. PASS. Diffed the item against the read-only repository. The existing public
   theorem's signature is byte-for-byte identical (also checked by script), as is
   its docstring. The only existing interface is unchanged; added imports are proof
   imports. The new norm-locus module does not exist in the repository. No existing
   definition or statement changed and no change record is required.
2. PASS as a decomposition. Compiled both delivered modules in import order using
   lcompile.py. The sole sorry is isAffineOpen_descent_norm_locus, a named public
   theorem with its source, complete determinant proof docstring and node. Scanned
   for prohibited declarations and hidden holes: none. A fresh scratch copy prints
   axioms for descent_inversion, the two reused transport/orbit theorems, prime
   avoidance and both public theorems. Only the two public theorems use sorryAx;
   all others use only propext, Classical.choice and Quot.sound. No definition or
   arbitrary data witness from an unproved existence statement is introduced.
3. PASS. Independently read https://stacks.math.columbia.edu/tag/03JE, especially
   its final norm argument. The new statement supplies exactly the domain for t*f,
   the norm nonvanishing set, D(f) contained in W and U contained in D(f). These
   identify U with a basic open in the affine D(f); containment alone would not.
   For s=t=id, U is D(f); for f=0, U is empty; for unit f, U is a basic norm locus
   inside affine A. Empty W, empty source and rank-zero fibres satisfy the same
   determinant criterion (norm 1), with hU imposing the required containment.
   Nonclosed and inseparable fibre points cause no change: a finite-dimensional
   fibre algebra element is a unit exactly when it avoids every prime ideal.
   Ran independent leanfinder, loogle and grep searches with different wording,
   and read the upstream BaseChangeNorm signatures. No exact general result was
   found; its fibre criterion assumes a finite field-extension base change.
   Recorded these new searches in the new node. This lemma asserts affineness
   alone, not finite-set prime avoidance or existence/invariance of a shrinking,
   and is a strictly smaller part of the argument.
4. PASS. Read the reduction top down: inversion and identity come from actual
   transport laws; existing proved orbit saturation supplies orbit equality;
   finite closed images construct invariant open interiors; proved upstream
   prime avoidance chooses f; inversion exchanges the two closed images; the
   final application supplies every hypothesis of the norm-locus lemma. No
   shorter available route was found. All imports supply signature data or a
   used theorem/instance. The removed FiberDegree import is recorded; every old
   proof_deps node is retained and used. No additional module is claimed pruned.
   Read sk-prop-jacobian-descent.json: its realized arrays are empty and its
   effective-descent route is unchanged; the norm-shrinking step remains.
5. PASS. Read both DAG nodes alongside their Lean. Checked verbatim lean.statement
   fields and equality between proof_deps and the union of proof-step uses by
   script. The existing node follows the actual groupoid/interior/prime-avoidance
   reduction and names both reused theorem nodes and the new norm lemma. The new
   node has its source, proof, origin, three search kinds, created record,
   blueprint ancestry, chapter/unit and correct module/file/declaration.

Changes in this reading: added independent search records to the new node and
this review section; refreshed the scratch axiom probe against the current proof.
No delivered Lean repair was necessary. One original hole is closed syntactically
and one strictly smaller hole is added: net zero, a decomposition, not a complete
sorry-free proof. No further holes closed and no additional imports pruned.
