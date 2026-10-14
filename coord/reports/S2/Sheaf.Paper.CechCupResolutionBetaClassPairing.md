## What changed

Replaced the `sorry` in
`AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing` with a proof from
`cupCech_signed_axis_pairing`, preserving the reviewed signature and public imports.
The current fetched branch lacks
this module, so this repair restores its reviewed interface and supplies the proof.
Added the proof-only import `Sheaf.Paper.CechCupSignedAxisPairing` and updated the item's DAG
proof and proof dependencies to match the argument.

The main proof lifts the two beta homology classes through alpha, proves that the global
resolution product is a cycle using `D.leibniz`, identifies the lifted input classes with
`A.alpha_class` and `B.alpha_class`, and evaluates the same total pairing along both axes.
Applying the inverse target comparison and `C.alpha_class` identifies the target classes;
`hcup` completes the product calculation. Three proved private helpers establish cycle-class
surjectivity, alpha-class surjectivity, and existence of the paired global cycle.

The new theorem constructs a total homology pairing from six chain maps and their explicit
axis component equations. It does not assume any comparison isomorphism, alpha quasi-isomorphism,
class identification, or characterized sheaf cup product. It isolates the original plan's
signed cochain construction and axis calculations; the original plan's surjectivity and
characterization step is proved in the item. The existence theorem is eliminated only in a
proof; no definition chooses arbitrary data from an unproved existence statement.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing`
(node `lem-sc-cech-cup-resolution-beta-class-pairing`). There is no `sorry` in the item's module.

Added: `AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing`
(node `lem-sc-cech-cup-signed-axis-pairing`), in
`Sheaf.Paper.CechCupSignedAxisPairing`. This is the only new hole, and its proof is exactly
`by sorry`, with the source and full component/quotient argument in its docstring and node.

Relative to the assigned historical module this is a decomposition: one upper hole closed
and one lower hole added. The current source base lacks the upper module entirely, so the
restoration adds the lower hole to that base; no net ledger improvement is claimed.
The signed total construction remains open; all lifting, cycle construction, characterization,
and inverse-isomorphism glue in the item is proved. After the restoration repairs,
`lcompile.py --all` compiled both modules without warnings (7.3 and 10.6 seconds).
The total construction uses finite sums in each first-quadrant total degree. Empty index sets,
zero coefficients or cycles, and degree zero satisfy the same axis formulas; it needs neither
a cover nor quasicoherence. Its maps are only chain maps with specified components, so no
comparison isomorphism is silently assumed in that remaining obligation.

## No longer needed

None. Both original public imports are required for the unchanged statement; the new proof
import is used. The original definition dependencies remain needed in the new construction
and the main proof. No node or module is claimed pruned, and no unit route is bypassed.
The unit record `sk-prop-av-cube` has no realized statement or step bound to this comparison.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing conflict returned at head `3be04b59c`: the dry-run tool refreshed
the clone to `24e53817915f203a97884f8c6ec998f44e30ae4c`. At that current base neither
`lean/Sheaf/Paper/CechCupResolutionBetaClassPairing.lean` nor its node exists. A read-only
check on the live server likewise found the module absent. Consequently there is no current
file to copy or competing proof to preserve. Restore the reviewed declaration unchanged,
with the proved reduction, and explicitly record this interface restoration. The restored
node is now attributed to S2 and this item; stale landing-review metadata is removed. The
previous second readings are removed so the new independent reader reviews the current repair.
This is a source restoration, not an unchanged re-push over a concurrent version.


The previously reviewed `cupCechResolution_total_pairing` had a specialized version of the
two axis formulas, but its module imported this item and proved its beta formula from this item.
That module is also absent at the current base.
Importing it here would create a cycle. The new construction therefore takes the chain maps
and component equations directly, without the stronger comparison data, and has no dependency
on either this item or `CechCupResolutionTotalPairing`.

The source Tag 0FKV states its derived comparison diagram for a cover. The component construction
used here is the signed map of Tag 07MB and the two axis calculations; those are valid for any
family. The main proof obtains alpha invertibility from the explicit comparison data instead
of from a cover or flasque-resolution theorem. This preserves the original unrestricted family
hypothesis.

The earlier delivery recorded the following searches: Lean Finder found only Dold-Kan and alternating-face-map infrastructure. Loogle found generic
homology-map declarations. Upstream grep found no matching Cech pairing. LeanSearch returned an
internal-server error, recorded as unavailable. Blueprint searches for `Cech cup` and
`Alexander` found no matching blueprint node.

## New nodes

`lem-sc-cech-cup-signed-axis-pairing`, in `dag/nodes/sec-abelian-varieties/`, records the signed
total homology pairing and its two axis formulas for chain maps satisfying the component
equations. Its module is `Sheaf.Paper.CechCupSignedAxisPairing`. It keeps the item's chapter,
unit, and blueprint ancestor; its dependencies are the existing resolution, Cech comparison,
and Cech cup data. No existing definition or statement changes and no forced adaptation occurs.

`lem-sc-cech-cup-resolution-beta-class-pairing` is restored because the current base
lacks both it and its module. Its reviewed statement and Lean signature are unchanged.
The restoration is recorded in
`coord/changes/cech-cup-resolution-beta-class-pairing-restoration.md`.

## Second reading by S2

1. Interface: attempted `diff` against both repository modules; both are absent, as
   the restoration record states. The main signature matches that record byte for byte,
   and both node signatures match the delivered Lean modulo whitespace. No repository
   declaration or definition is modified. Verdict: documented restoration, not an
   independently verifiable comparison with an available historical source.
2. Proof: independently compiled both modules with `lcompile.py --all`, cleanly (7.1 and
   9.8 seconds). Scratch copies with `#print axioms` show only `propext`,
   `Classical.choice`, and `Quot.sound` for all three private helpers; the main theorem
   and the signed-axis theorem additionally use `sorryAx`. The only literal hole is
   `cupCech_signed_axis_pairing`, a named public theorem with its source, proof docstring,
   and node. No forbidden declaration or holed definition occurs. Verdict: sound
   conditional reduction, one upper hole closed and one lower hole added, not a complete
   proof or a net hole reduction.
3. Split: read the full signed-axis statement and component proof, and the definitions
   of the double complex, pairing, comparison maps, and coefficient cup. With resolution
   degree first, the differential is resolution differential plus `(-1)^r` times Cech
   differential; the interchange factor `(-1)^(i*s)` gives total Leibniz sign
   `(-1)^(r+i)`. Both axes have factor one. Checked degree zero, zero inputs, empty
   families (all Cech objects vanish), and a singleton family (degree-zero formula is
   section multiplication). No cover or invertible comparison is needed for this
   construction. Tags 07MB and 0FKV support the signed construction and axis diagram;
   the unrestricted-family extension uses the explicit component calculation, not the
   cover-dependent quasi-isomorphism assertion of 0FKV. Fresh Lean Finder search for a
   bilinear multiplication on total double complexes returned total-complex and tensor
   infrastructure only; Loogle on `HomologicalComplex.homologyMap` returned generic
   homology functor facts; Mathlib grep for `Alexander|Whitney|pairing` in Algebra/Homology
   found no hit. Local and upstream searches found no usable theorem with these six
   maps and both axis equations. The local cosimplicial AW theorem has different
   objects and only a degree-zero component formula. Verdict: true construction-only
   subproblem, strictly a part of the original comparison argument, not a restatement.
4. Route and pruning: checked the actual reduction from top to bottom: lift beta classes
   using alpha quasi-isomorphisms, construct the global paired cycle via Leibniz, apply
   both axis formulas to the same pairing, cancel the target iso, and apply `hcup`.
   An arbitrary existence witness is eliminated within a proposition only. Both public
   imports are needed by the signatures; the signed-axis import is correctly proof-only.
   No original dependency is dropped. `dag/units/sk-prop-av-cube.json` has empty realized
   statement and step lists; this construction bypasses no realized unit step. Verdict:
   no omitted pruning and no shorter existing route found.
5. DAG: checked both complete records, their source and blueprint provenance, created
   fields, module/declaration/signature records, and dependency unions. The main proof
   steps agree with the Lean lifting and cancellation argument; the lower node describes
   the remaining signed cochain and quotient construction. Verdict: consistent.

Changes by this second reader: appended this independent review and fresh search evidence
in the sandbox search log. No Lean proof, signature, import, node, or change record needed
repair. The split construction is substantial and could not be closed in a few minutes.
