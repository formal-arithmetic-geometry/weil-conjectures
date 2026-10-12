## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_of_lt` in
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre`, with its signature unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.AlternatingCechComputes`.
Two private, fully proved helpers construct the finite-infimum chosen-intersection
Čech complex and identify it with the existing explicit Čech complex. The proof
uses the existing affine comparison and alternating comparison, then proves the
cardinality obstruction and transports zero homology through the comparisons.
Updated the cohomology-bound node's proof to record these encoding identifications.

## Proved and sorry left

The sole original sorry, `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_of_lt`
(node `lem-pc-projective-space-cohomology-bound`), is proved from the existing named
declarations. No sorry remains in the delivered module and no new sorry is added.
The imported `AlgebraicGeometry.Scheme.alternatingCechComputes` remains an existing
sorry in its own module (node `lem-pc-alternating-cech-computes`); it is the next
proof obligation on this route, not a new statement in this delivery.

The argument covers d = 0, arbitrary commutative A including the zero ring, and
all q > d. Its cardinality contradiction uses only the strict inequality and
Nat.card n = d + 1. No field or noetherian assumption was introduced.

## No longer needed

None. No original import was removed, and no node of the planned route was bypassed.
The one newly added import is used by the proof. No new module is needed to bridge
the two Čech encodings: both helpers are fully proved in Serre.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical argument is correct. Its Lean declarations use two distinct
Čech encodings: the affine comparison uses Mathlib's module-valued complex, while
the alternating theorem uses SiteCechComplex with explicit abelian cochains. The
proof supplies the missing encoding identifications using an existing module-to-
abelian Čech homology isomorphism and the private finite-infimum complex isomorphism.
The unit's standard-cover/Čech route is preserved. No statement or definition used
by a target was changed.

## Second reading by Q2

1. PASS: compared the whole delivered module with the repository using `diff` and
   the declaration-table comparison. All existing signatures and definitions are
   byte-for-byte unchanged. Only one proof, two private helpers, and one plain
   proof import were added; there is no statement change or change record.
2. PASS: compiled the complete module locally without errors or warnings. Scanned
   for forbidden constructs and local sorry: none. A scratch copy printed axioms
   for all 16 declarations, including the private helpers: only propext,
   Classical.choice, Quot.sound, and permitted transitive sorryAx occur. Both new
   helpers are free of sorryAx. The newly reduced theorem is not yet a closed
   comparator proof: the existing alternating comparison remains open.
3. PASS (no split-off statements): no new theorem with sorry, no new module, and
   no new node. Checked the finite-infimum universal property and the identity
   component maps against both differential definitions. For d = 0 and q = 1,
   two strictly increasing indices cannot fit in one coordinate; for all q > d
   the same injection/cardinality contradiction applies. The zero ring and any
   finite coordinate type need no additional hypothesis. Empty coordinate types
   cannot satisfy Nat.card n = d + 1.
4. PASS: read the affine and alternating comparison statements, the explicit
   module/abelian homology comparison, and the upstream version (still sorry).
   An independent Mathlib grep search via msearch and source rg found no shorter
   general bound; monomial results concern twists over fields and cannot replace
   the arbitrary quasi-coherent-module argument. The new import is plain and
   used. All four old proof_deps remain used, so No longer needed is complete.
   Read dag/units/sk-thm-picard-pn.json: the standard-affine-cover/Cech computation
   route is preserved. Its realized.statement and realized.steps are already
   empty in the repository; this delivery neither fills nor bypasses them.
5. PASS after metadata repair: proof steps follow the actual finite-infimum
   identification, alternating comparison, cardinality obstruction, and affine
   comparison. proof_deps is precisely the union of the steps' uses, with the
   SiteCechComplex definition added to the four original dependencies. Only
   proof, proof_deps, proof_origin, and lean metadata differ from the old node.

Changes by the second reader: corrected the existing node's lean.sorry_free,
branch, line, and note to describe the delivered local proof and its remaining
transitive obligation. No Lean proof needed repair. Added this audit, including
explicit axiom results and the pre-existing empty unit realization table.
