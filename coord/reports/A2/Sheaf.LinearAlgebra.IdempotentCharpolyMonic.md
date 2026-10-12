## What changed

Replaced the sorry in Matrix.idempotentCharpoly_monic_of_map_monic by a complete Lean
argument from the new leading-coefficient lemma. The target signature is unchanged.
Added Sheaf.LinearAlgebra.IdempotentCharpolyLeadingCoeff with one strictly smaller
statement: the leading coefficient is idempotent, without any quotient, Jacobson,
or monic-reduction hypotheses. The proof-only import replaces the unused standard
free-cover import. Updated the original node's proof route and dependencies.

The Lean argument proves directly that idempotents killed by reduction modulo a
Jacobson ideal vanish. It then proves the leading coefficient survives reduction,
uses the mapped leading-coefficient formula, and kills its complementary idempotent.
The zero-ring case is handled separately; the nonzero quotient instance follows
from properness of the Jacobson radical. Both modules compile cleanly.

## Proved and sorry left

Closed: Matrix.idempotentCharpoly_monic_of_map_monic
(lem-weil-pbc-idempotent-charpoly-monic).
Added and left: Matrix.isIdempotentElem_idempotentCharpoly_leadingCoeff
(lem-weil-pbc-idempotent-charpoly-leading-coeff), in the new module.
This is a decomposition: one hole closed, one strictly smaller hole added; net zero
holes. No other holes were added and none remain in the item's module. Its final
proof still depends on the new theorem's sorry.

## No longer needed

Removed direct import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover.
The original theorem no longer directly uses
lem-weil-pbc-finite-projective-standard-free-cover,
lem-weil-pbc-charpoly-free-module-properties,
lem-weil-pbc-finite-projective-rank-locally-constant, or
lem-weil-pbc-localized-span-eq-zero. The definition
def-weil-pbc-idempotent-charpoly is no longer a direct proof-step dependency, but
remains a statement dependency and its module stays publicly imported.
The first, second and fourth remain in the
natural-language plan for the new leading-coefficient node; they are not globally
pruned. The locally constant rank node and the maximal-ideal rank-locus argument
are unnecessary for this route. The second reading removed the redundant public import Mathlib.Algebra.Ring.Idempotent
from the new module; no public import of the existing module changed.
The idempotent determinant definition remains needed by both statements.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement is unchanged and no false statement was found.
The DAG's local-freeness and rank lemmas do not directly expose the needed determinant
coefficient calculation. The new node records precisely that calculation instead
of restating monicity under a new name. The original rank-locus argument is valid
but unnecessary once leading-coefficient idempotence is known.

Checked edge cases: zero ring, empty matrix index set (determinant 1), P=0
(determinant 1), P=1 (ordinary monic characteristic polynomial), and rings that are
products with different ranks (the leading coefficient can be a nontrivial
idempotent, so unconditional monicity would be false). The intermediate statement
allows all these cases. Mathlib searches were actually run: LeanSearch returned
an unavailable service, Loogle and source grep returned no match. LeanFinder also
returned only related matrix determinant declarations. The whole blueprint search
for idempotent characteristic polynomials and leading coefficients found no exact
statement. Tag 09XI's characteristic-polynomial paragraph was read online; the
local .tex source is absent on this machine.

## New nodes

lem-weil-pbc-idempotent-charpoly-leading-coeff, at
dag/nodes/sec-proper-base-change/lem-weil-pbc-idempotent-charpoly-leading-coeff.json,
with theorem Matrix.isIdempotentElem_idempotentCharpoly_leadingCoeff in
Sheaf.LinearAlgebra.IdempotentCharpolyLeadingCoeff. It isolates the local
finite-projective determinant computation and standard-cover descent, and removes
the entire Jacobson and monic-reduction portion from the remaining task. Its proof
plan retains the existing image/base-change, free-cover, characteristic-polynomial,
and standard-cover injectivity nodes. No change records are needed.

## Second reading by A2

1. Compared the delivered monicity module with the repository using diff. Its
   sole existing declaration's signature is byte-for-byte unchanged; only its
   proof and one plain proof import changed. No definitions or target statements
   changed. The new module has one new theorem, with the verbatim signature in
   its node. No change record is required. Verdict: pass.
2. Compiled both modules in import order using lcompile.py. Both compile without
   errors or warnings. The only sorry is the reported named theorem
   Matrix.isIdempotentElem_idempotentCharpoly_leadingCoeff, whose proof is exactly
   `by sorry`; neither module defines data or adds forbidden declarations.
   Scratch-copy #print axioms checks and delivery probes check both declarations.
   The monicity proof remains conditional on the new theorem (sorryAx); this is
   one decomposition, zero net holes closed. Verdict: pass as a decomposition.
3. Independently checked the new statement: on a simultaneous finite free cover
   of the image and complement, the determinant is a monic characteristic
   polynomial, so its coefficient at the global natural degree is 0 or 1.
   Localization injectivity then proves idempotence. Checked zero rings, empty
   index sets, P=0, P=1, and varying-rank product rings (for one coordinate and
   P=(1,0), T=0 the polynomial is (X,1), with leading coefficient (1,0)).
   This statement removes all ideal and reduction assumptions and isolates only
   the local determinant calculation; it does not restate monicity. Its docstring
   supplies a complete proof and its node supplies source and dependencies.
   Read Stacks Tag 09XI's characteristic-polynomial paragraph independently.
   Searched with fresh projector/top-coefficient phrasing via LeanFinder, Loogle,
   msearch grep, and rg in the library and Mathlib. No exact existing result was
   found. The local Jacobson argument is short and sound; the library's proved
   idempotent-congruence theorem is a possible alternative but requires another
   import and gives no smaller remaining hole. Verdict: pass.
4. Read the old proof dependencies and their Lean/Mathlib records. The leading
   coefficient lemma captures precisely the remaining adapted-basis calculation;
   formalizing it is not a few-minute corollary of the currently exposed API.
   Kept the sound reduction. Removed the new module's redundant public import
   Mathlib.Algebra.Ring.Idempotent and recompiled to verify it is unnecessary.
   The pruning list accounts for every old proof dependency, including the
   determinant definition still needed by the signatures. Read
   dag/units/sk-thm-p1.json: neither this item nor the pruned rank lemma realizes
   its statement or steps; the unit's realized route is preserved. Verdict: pass.
5. Compared the nodes with the statements and the proof as written. The old
   node's new proof_deps contains the leading-coefficient node; the new node has
   its exact Lean signature, creation/provenance, searches, chapter/unit, and
   local-cover proof plan. Corrected the first old-node step's elementary flag
   to false because it uses a non-elementary named lemma. Verdict: pass.

Second reading changed only the redundant import, that elementary flag, and
this report's review/pruning details. The existing proof remains intact.
