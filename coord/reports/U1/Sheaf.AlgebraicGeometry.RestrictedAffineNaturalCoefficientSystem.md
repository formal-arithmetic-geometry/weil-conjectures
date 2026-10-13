## What changed

H9 repair (reviewer X-cf892): removed the three unused proof-only imports
`RestrictedAffineSingleTransitionLaws`, `RestrictedAffineSingleConeNaturality` and
`RestrictedAffineSingleConeLeg`. Removed `restrictedAffineSingleConeIso` from the local
irreducibility attribute. Removed the corresponding three proof dependencies and step uses
from the main node, and clarified that its unresolved construction plan does not apply them.
No declaration signature, proof body or docstring changed in this repair.

The first repair was still false: `rCanonical` was another unconstrained input, so setting
`rCanonical := r` satisfied the new hypothesis for every old counterexample. Arbitrary
complex transitions `psi` also had no relation to `phi`.

Corrected `AlgebraicGeometry.Etale.restricted_affine_stage_naturality` to the advertised
concrete construction: `restrictedAffineDiagram`, `restrictedAffineK` and
`restrictedAffineSingleTransition`. Its cohomology comparisons are identities. The proof
unfolds the transition and canonical restricted-cohomology map and uses reflexivity.
No data or new definitions are chosen from an existence theorem.

Reopened `AlgebraicGeometry.Etale.exists_restricted_affine_natural_coefficient_system`
as its sole named `sorry`, preserving its signature and full source/proof docstring
byte for byte. Its previous body obtained arbitrary witnesses from the coefficient-system
theorem and applied the false stage helper. The corrected concrete helper cannot be applied
to those witnesses, whose transitions and comparisons are not identified with the actual
constructions. Keeping that inference would retain the error. A direct concrete reconstruction
was attempted but could not pass the existing 60-second per-file compile limit; it is not
part of this delivery. The theorem's existing docstring gives the complete construction route.

The change record is `coord/changes/restricted-affine-stage-naturality-repair.md`.
Only the stage helper's exported statement changes. No target statement, definition or
other module changes. `RestrictedAffineSingleMaps` is public because the corrected signature
uses its definitions; raw cohomology remains public through its construction import.
The reopened construction plan does not justify retaining unused proof imports.
The transition-law, cone-naturality and cone-leg modules are removed in the H9 repair. Local transparency controls only
prevent gratuitous elaborator unfolding and do not alter any definitions.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.restricted_affine_stage_naturality` in its documented,
corrected concrete form. This is not a proof of the old false universally quantified statement.

Hole removed in that corrected declaration: `restricted_affine_stage_naturality`
(node `lem-sbc-restricted-affine-natural-coefficient-system-stage`).
Hole added by reopening the invalid dependent proof:
`AlgebraicGeometry.Etale.exists_restricted_affine_natural_coefficient_system`
(node `lem-sbc-restricted-affine-natural-coefficient-system`). This is the only `sorry` left.
Its statement, source and complete natural-language proof docstring are unchanged.

No new split-off declarations or nodes. One of the two declarations now has a complete
kernel-checked proof. Zero net holes closed minus added; this delivery is a statement/soundness
repair, not progress measured by the ledger and not a completion of the existential theorem.

## No longer needed

H9 additional removed imports and corresponding main-node proof dependencies/uses:

- `Sheaf.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws`:
  `lem-sbc-restricted-affine-single-transition-laws`.
- `Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeNaturality`:
  `lem-sbc-restricted-affine-single-cone-naturality`.
- `Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeLeg`:
  `lem-sbc-restricted-affine-single-cone-leg`.

These modules are unused by the delivered proof. No claim is made about their reachability
from other target imports. The unused local irreducibility entry
`restrictedAffineSingleConeIso` is also removed.

Removed imports: `Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientSystem` and the redundant
direct `Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology` import. The coefficient-system
existence theorem does not identify the witnesses needed by the concrete stage equation.
Raw cohomology remains available through the public single-maps/construction imports.
This is import pruning, not a claim that these modules leave the whole target closure:
`RestrictedAffineComplexSystem` still imports the coefficient-system module.

The main node's old direct dependencies now supplied through the concrete construction plan:
`def-pc-fibre-product`, `lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-qcqs-morphism-permanence`, `def-weil-pbc-inverse-image`,
`lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-left-adjoint-preserves-colimits`.
They no longer appear as direct proof_deps of this node; the concrete construction and
coherence nodes supply these steps. `def-sbc-raw-affine-restricted-cohomology` remains.
The stage node's old raw-cohomology dependency remains and the concrete definitions are added.
The former route through `lem-sbc-restricted-affine-coefficient-system` and
`lem-sbc-restricted-affine-single-coherence` is insufficient for stage compatibility and
is not used by the corrected concrete plan.

## Where the brief, the DAG or earlier work was wrong

H9 identified imports retained only for an unimplemented construction plan. The previous
second-reading notes below describe the earlier version; their claims about retaining
transition laws, cone naturality and cone-leg dependencies are superseded by this repair.

Reviewer X-dba85's two-stage constant-system counterexample remains valid for the first
repair, by choosing `rCanonical := r`. Independently, identity comparisons cannot make an
unrelated `psi` into the transition of `phi`. The old Lean helper therefore failed to express
its node's concrete-witness qualification. The corrected helper fixes every relevant datum
by an actual definition and is true by definitional equality.

The old main body applied the false helper to arbitrary witnesses. The DAG's old proof_deps
were a plan rather than that reduction. The delivered records now give the verified concrete
stage proof and the concrete construction plan for the reopened main theorem. No target was
weakened and no invalid witness choice was retained.

Source checked: [Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1) restricts the coefficient
system to U times_S X_i before continuity; [Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
requires coherent inverse-image complex transitions with a common lower bound. The preserved
main construction route uses precisely these stages, transitions and bound zero.

## New nodes

None. Updated two existing node records. The stage node has a statement_change and its exact
corrected Lean signature; the main node's statement and signature remain unchanged.

## Statement corrected

The old stage helper quantified over unrelated schemes, complexes, transitions and comparisons.
Its correction uses the actual existing definitions and identity comparisons. For two identical
stages with coefficient group integers squared, comparison identity at one index and coordinate
swap at the other contradict the old equation; the first repair admits the same example.
The base DAG has no node citing the stage node in stmt_deps or proof_deps. The main node's
actual Lean use of the faulty helper is removed and the concrete stage lemma is recorded in its
future construction plan. No unit realizes this auxiliary stage statement.
The associated unit `sk-lem-failure-field` has empty realized.statement and realized.steps[0];
these fields remain unchanged. The affine restriction/single-complex/colimit route is preserved.

## Forced adaptations

None. `tools/downstream.py` found 167 downstream modules and only the held module uses the
changed helper. The main existential signature is byte-for-byte unchanged, and the existing
public raw-cohomology definitions remain available transitively. The change record lists every
downstream module and its current holder. No downstream statement or definition needs an edit.

## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered module with the repository using diff and the declaration parser.
   The main signature and docstring are byte-for-byte identical. Rejected the vacuous repair,
   corrected only the false helper's signature with a full change record, and reopened the
   invalid main body. No definition or target statement changes. Verdict: partial soundness
   repair, with the one documented interface correction.
2. The final module compiled in 37.1 seconds, with no error or warning. No axiom, unsafe, opaque,
   implemented_by, extern or definition hole occurs. The only sorry is the complete proof of the
   existing named main theorem, whose node and source/proof docstring are present. The scratch
   axiom audit is recorded below when completed. Verdict: stage equation is an actual proof;
   the dependent construction is openly unresolved rather than justified by the false helper.
3. No new split-off statements. The corrected stage equation is definitional for all arrows
   and all degrees, including identity arrows, degree zero, positive degree and zero sheaves;
   neither directedness nor affineness is needed. LeanFinder (single-functor pullback comparison
   naturality), Loogle (fully qualified mapCochainComplexSingleFunctor) and grep searches found
   the generic single-functor comparison. The repository's explicit maps make this particular
   equality reflexive. Verdict: no duplicate holed helper or arbitrary existential data.
4. Took the shortest route for the concrete stage equation: expand the existing definitions.
   The main construction route still uses the actual geometric witnesses, transition laws,
   cone naturality and cone-leg equality as its docstring describes. The unused existential
   construction import is removed; every old direct dependency removed is listed above.
   Inspected the unit's realized fields: unchanged, with no unit step bypassed. Verdict: pruned
   the invalid reduction, preserved the paper's construction route, and claimed no ledger gain.
5. Updated both node proof records, proof_deps and proof_origin. Dependencies are exactly the
   union of each step's uses. The stage node's statement, stmt_deps, lean.statement and
   statement_change record the concrete correction. The main record explicitly describes a
   plan for its reopened proof, and its signature is unchanged. Verdict: no missing node or
   undeclared hole; node records distinguish the verified lemma from the open construction.

Changes by this reader: removed rCanonical/hr; replaced the false general stage statement
with a proved concrete equation; reopened its invalid dependent proof without changing its
statement; pruned imports; updated two nodes and the full change record. Net holes: zero.

Validation: scratch copy compiled in 41.9 seconds with both `#print axioms` commands.
`restricted_affine_stage_naturality` uses only `propext`, `Classical.choice`, `Quot.sound`.
`exists_restricted_affine_natural_coefficient_system` uses those plus `sorryAx`, exactly
for its reopened named proof. No additional axiom occurs.


## Second reading by U1

1. Compared the delivered module with the repository using `diff -u` and the declaration
   parser. The existential signature is byte-for-byte identical, as is its proof docstring.
   Only the stage helper signature and docstring change, explicitly recorded in
   `coord/changes/restricted-affine-stage-naturality-repair.md` and the stage node's
   `statement_change`. There are no definitions or target statements in this delivery.
   A repository-wide use search finds the helper only in the held module; no forced
   adaptation is required. Verdict: documented correction of a false auxiliary statement,
   with no accidental interface change.
2. Compiled the sole delivered file through lcompile.py: 38.0 seconds, no errors or warnings.
   Inspected the entire file: its only sorry is the existing named existential theorem,
   with the original source and full construction proof docstring and matching node.
   There is no definition hole, axiom, unsafe, opaque, implemented_by, extern or kernel-check
   bypass. A fresh scratch copy with both #print axioms commands compiled in 37.8 seconds:
   the concrete stage lemma uses only propext, Classical.choice and Quot.sound; the open
   existential uses exactly those plus sorryAx. Verdict: a checked stage proof and one
   openly unresolved construction, not a completed existential proof.
3. No statements or nodes are split off. Read RestrictedAffineSingleMaps,
   RestrictedAffineCoefficientConstruction and RawAffineRestrictedCohomology: the diagram's
   maps are rawAffineRestrictedMap, K is the restricted degree-zero single complex, and the
   transition's two factors are exactly those inside rawAffineRestrictedCohomologyMap.
   This verifies the concrete equation for every arrow, including identities, for degree
   zero or positive degree, zero coefficients and non-affine U. The removed geometric and
   coherence assumptions are unnecessary for this definitional equation. A fresh grep
   service search for restrictedAffine naturality/rawAffineRestrictedCohomologyMap returned
   no hits; the local search finds the defining factors rather than an alternative theorem.
   Verdict: no relabelling split and no arbitrary data from an unproved existence theorem.
4. The stage proof takes the shortest route: unfold the two map definitions and reflexivity.
   The sole public import is required by the corrected signature, and supplies raw
   cohomology transitively. Checked every old proof_deps entry removed from the two base
   nodes against No longer needed; all are listed. The report also lists the three imports
   pruned in the latest H9 repair. Read dag/units/sk-lem-failure-field.json: its realized
   statement and step lists are empty and unchanged. Read
   [Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
   [Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM): affine restriction followed by
   coherent bounded-below coefficient complexes remains the construction route.
   Verdict: pruning is accurately reported; no unit route is bypassed, no net progress claimed.
5. Inspected both delivered nodes and compared their fields with the repository. Only the
   permitted proof/Lean fields change in the main node; the stage additionally has its
   documented statement correction and stmt_deps. Each proof_deps equals the union of its
   steps' uses. The stage dependencies name precisely the definitions expanded by the proof;
   the main proof and proof_origin explicitly describe its unresolved construction plan.
   Confirmed no base node cites the stage helper, matching its empty correction citers list.
   Verdict: nodes and Lean distinguish the proved concrete equation from the open main theorem.

Changes by this second reader: corrected the stale change-record paragraph claiming that
transition-law, cone-naturality and cone-leg imports were retained; they are removed in the
actual module. Added this independent review and a fresh scratch axiom audit. No Lean proof,
statement, definition or node needed further changes. One of two declarations is proved in
its documented corrected form; zero new split-off declarations; zero net holes closed.
