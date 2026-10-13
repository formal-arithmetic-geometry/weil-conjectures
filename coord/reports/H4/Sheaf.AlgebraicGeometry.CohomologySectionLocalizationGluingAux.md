## What changed

Proved `AlgebraicGeometry.Scheme.Modules.localized_middle_comparison_bijective` in
`Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux`, preserving its complete
signature and visibility. Added proof-only imports of `Sheaf.Paper.CohomologySectionDivision`
and `Mathlib.Algebra.FiveLemma`. Updated the existing node's proof, proof_deps and
proof_origin to match the Lean argument.

The proof cancels multiplication by s^n using `exists_cohomologySection_division`,
then proves uniqueness of comparisons by quotient surjectivity and direct-sum generator
extensionality. It identifies the diagram comparison and the three local equivalences
with the given c. Private proved helpers reindex the lower row using the intersection
and union equalities; deriving identity restriction gives identity on cohomology.
The degree-zero left-exact lemma and the successor-degree additive five lemma complete
the argument. No data is chosen from a mere existence theorem to define a public object.

Validation: the single module compiles through lcompile.py with no errors or warnings.
The required deliver3.py --no-push dry run is the final validation. Read the source
Mayer--Vietoris paragraph at https://stacks.math.columbia.edu/tag/09MR; its five-term
argument is exactly the route used. The unit's realized statement and steps are preserved:
this auxiliary node realizes no unit-level statement or step.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.localized_middle_comparison_bijective`
(node `lem-sc-invert-s-cohomology-gluing-aux`).

No sorry remains in the delivered module. No holes were added and no statements were
split off. All private helpers are proved. This proof uses existing stated dependencies;
in particular `AlgebraicGeometry.exists_cohomologySection_division` remains a separate
existing task, and its hole is not added or changed by this delivery.

## No longer needed

None. Both original public imports are required by the statement. The original proof-only
Mayer--Vietoris import remains used. The five-lemma node remains a proof dependency,
implemented through Mathlib's additive-group variants rather than bundled composable
arrows. The division node is a needed additional existing dependency. No planned node,
module or import is pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires cancellation by the cohomology multiplication map,
but did not list the existing individual-twist division node supplying that bijectivity.
Added `lem-sc-cohomology-section-division` to proof_deps. No mathematical correction or
interface change was needed. The repaired hc and intersection fraction formula suffice.
The local literature checkout is absent on this machine; the source paragraph was read
from the Stacks website. No new lemma or source claim was invented.

## Second reading by H4

1. PASS: Compared the complete module with the repository version. The sole existing
   declaration's signature is byte-for-byte identical, including hc and all three
   local fraction formulas; its visibility and the public imports are unchanged.
   The existing interface change record is landed and this delivery does not modify
   it. Added helpers are private and do not occur in a public signature or definition.
2. PASS: Independently compiled the module with lcompile.py, without errors or
   warnings. Searched for forbidden declarations and proof escapes: none occur, and
   there is no sorry in this module. Compiled a scratch copy with #print axioms for
   all eight declarations: the seven private helpers use only propext,
   Classical.choice and Quot.sound; localized_middle_comparison_bijective additionally
   uses sorryAx through existing open dependencies. The private data definitions are
   explicit composites of restriction maps, not choices of unproved witnesses.
3. PASS: No statements were split off and no holes were added. Checked the new
   private helpers directly: fraction extensionality follows from direct-sum
   generators and quotient surjectivity; the row transports reduce by substituting
   the equal opens and identity restrictions. These arguments cover empty opens,
   zero groups, and degree zero. Searched the library for alternative fraction
   extensionality and gluing declarations, and Mathlib via msearch.py grep with
   QuotientAddGroup.*ext|DirectSum.addHom_ext. The analogous upstream helper is
   private; Mathlib quotient extensionality is another implementation of the same
   already-correct short argument. No usable theorem directly closes the item.
4. PASS: Read the proof downward and checked both additive five-lemma variants in
   Mathlib.Algebra.FiveLemma. Cancellation is used only for comparison uniqueness;
   local equivalences then give exactly the four outer comparisons. Degree zero
   uses initial injections, and successor degrees use the three interior exactness
   assertions. All three proof-only imports are used, and the original proof_deps
   are both retained; thus No longer needed is complete. Read Stacks Tag 09MR's
   Mayer--Vietoris paragraph and dag/units/sk-thm-curveestimate.json: the unit's
   realized statement is thm-sc-proper-cohomology with no realized steps, so this
   auxiliary proof bypasses no unit-level realization and changes none.
5. PASS: Compared the node JSON against the repository: only proof, proof_deps and
   proof_origin changed. The node's stored Lean signature exactly matches the
   delivered signature. The proof steps and dependency union agree with division,
   the localized Mayer--Vietoris diagram and Mathlib's five lemma as used in Lean.
   There are no new nodes or change records to validate.

Changes by the second reader: appended this independent review and recorded its
compilation, signature, search and axiom checks. No Lean or DAG repair was needed.
The result closes one original hole, adds zero holes, and prunes no module; it
remains conditional on the existing open dependencies rather than an axiom-free
proof of the complete target closure.
