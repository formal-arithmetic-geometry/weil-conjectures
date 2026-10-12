## What changed

Completed `Ring.serreCriterionNormal` without changing its statement. The forward direction
uses the proved source-library regularity theorem in dimensions zero and one, constructs
one-term regular sequences in dimension one, and uses one new depth-two statement in
higher dimension. The reverse direction lowers R1/S2 to R0/S1, applies the existing
reducedness criterion, and proves integral closedness of total fractions using membership
at primes of height at most one. This follows the S2-only argument of Stacks Tag 031T
rather than the conductor induction of 031S. This node is not a unit realization, and the
unit's realized statement and steps are unchanged.

Added four modules. Three now have complete proofs: local denominator clearing, the
associated-prime height bound for regular quotients of S2 rings, and total-fraction
membership detected in codimension at most one. The latter two use the existing named
depth lemmas; the local denominator proof uses Mathlib alone. Updated the original node
and added matching nodes for the four modules. All five modules compile without warnings
through lcompile.py. The depth-two module retains proof-only imports of Kollár and the
nonzerodivisor theorem so its unfinished plan stays in the dependency closure. Existing theorem and public imports are unchanged.

## Proved and sorry left

- Proved `Ring.serreCriterionNormal`: the item's one original sorry is removed.
- Proved `IsIntegral.exists_local_denominator_of_normal`
  (`lem-weil-pbc-integral-total-fraction-local-denominator`) using Mathlib localization
  lifting, integral closedness, denominator clearing, and unit cancellation.
- Proved `Ideal.height_le_one_of_mem_associatedPrimes_regular_quotient`
  (`lem-weil-pbc-serre-s2-regular-quotient-associated-height`) from the existing
  `IsLocalRing.depth_quotSMulTop_of_isSMulRegular` and
  `IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`, and Mathlib's
  associated-prime localization theorem.
- Proved `Ring.exists_algebraMap_eq_of_serreS_two`
  (`lem-weil-pbc-serre-s2-total-fraction-membership`) from that height bound and Mathlib
  associated-prime existence. This statement does not assume integrality or R1.
- The sole sorry added or left in the delivery is
  `IsLocalRing.depth_two_of_normal` (`lem-weil-pbc-normal-local-depth-two`). It is a
  strictly smaller local depth assertion, with no R1 condition and no reverse implication.
  Its module gives the full Kollár/finite-extension argument in words.

This is a decomposition: one original hole closed and one strictly smaller hole added,
with net zero holes closed by this replacement. The three other new statements are proved.

The criterion still depends on previously stated sorries in the reducedness and
reduced-normal/total-fractions criteria, and the two depth lemmas above. They are used
as intended by stage 3; their modules are not edited or duplicated.

## No longer needed

Removed direct proof imports:
`Sheaf.RingTheory.Depth` (already public through SerreConditions),
`Sheaf.RingTheory.KollarLocalDichotomy`,
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`,
`Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated`, and
`Sheaf.RingTheory.RegularLocalDimOneIffNormal`.

The original node's direct proof-plan dependencies bypassed by the changed route are:
- `lem-weil-pbc-fg-ideal-radical-power`.
- `lem-weil-pbc-finite-of-integral-generators`.
- `lem-weil-pbc-localization-prime-residue-field-iso`.
- `lem-weil-pbc-noetherian-local-system-of-parameters`.
- `lem-weil-pbc-regular-local-dim-one-iff-normal`.
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`.

The following cease to be direct dependencies of the criterion but are retained in
`lem-weil-pbc-normal-local-depth-two`'s planned proof, so they are not globally pruned:
- `lem-weil-pbc-artinian-local-unique-prime`.
- `lem-weil-pbc-finite-algebra-is-integral`.
- `lem-weil-pbc-kollar-local-dichotomy`.
- `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`.

The corresponding removed modules not needed by this delivery's proof are
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and
`Sheaf.RingTheory.RegularLocalDimOneIffNormal`; Kollár and the nonzerodivisor lemma will
still be needed when the local depth-two item is proved. Other targets may independently
reach the pruned nodes. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

No statement error or target change was found. The second reader updated the criterion's
docstring, which still described the bypassed conductor induction. The DAG's long conductor induction is a
valid plan, but below this node it can be replaced by the associated-prime argument
already used in Stacks Tag 031T: only S2 is used after that proof obtains it from normality.
The generalization to reduced rings uses a nonzerodivisor denominator in place of a
nonzero denominator. The quotient-height lemma itself does not require reducedness.

The literature checkout is absent on this machine, so Tags 031S and 031T were read on the
Stacks website. LeanSearch returned HTTP 500 for both queries; this is recorded as
unavailable, not as a negative search. Loogle, LeanFinder and Mathlib/source grep were run.
Blueprint searches for normal depth, intersection localizations, associated principal
quotients and Serre S2 found no exact duplicate of the new auxiliary statements; the
clearing-denominators search returned unrelated scheme and Frobenius-model nodes.

Edge cases checked: the zero ring has no primes and every total fraction comes from it;
fields have dimension zero and are excluded in the depth-two lemma; in dimension one the
maximal ideal is nonzero; a unit denominator yields the zero quotient with no associated
primes; product rings use total fractions and regular denominators, never an assumed
embedding of the whole ring into a local fraction field. Local denominator clearing
allows the map from total fractions to the local fraction field to have a kernel.

## New nodes

`lem-weil-pbc-normal-local-depth-two`: Noetherian normal local domains of dimension at
least two have depth at least two; the sole new sorry, exactly the forward depth step.

`lem-weil-pbc-integral-total-fraction-local-denominator`: an integral total fraction admits
a denominator outside any prime whose localization is a normal domain; completely proved.

`lem-weil-pbc-serre-s2-regular-quotient-associated-height`: associated primes of a quotient
by a nonzerodivisor in an S2 Noetherian ring have height at most one; proved from the
existing depth statements and Mathlib. Normality is not assumed.

`lem-weil-pbc-serre-s2-total-fraction-membership`: local denominator witnesses at primes of
height at most one detect membership in a reduced S2 ring; completely proved from the
height lemma and associated-prime existence. Neither R1 nor integrality is assumed.

No change records are needed: existing definitions, statements and public imports are
unchanged. The new modules have no existing users to adapt.

## Second reading by P1

1. **Interfaces: PASS.** Diffed the sole existing module against the repository and
   compared declarations with the stage-3 reader: `Ring.serreCriterionNormal` retains
   its exact signature, including all universes, instances and both implications.
   Its two public imports are unchanged. The other four modules are new; no definition
   is changed or added, and no change record is required. The existing node changes only
   `proof`, `proof_deps` and `proof_origin`.
2. **Proofs and axioms: PASS with reported holes.** Compiled all five modules in import
   order using lcompile.py, without errors or warnings. Scanned the complete Lean text:
   the sole direct sorry is the whole proof of `IsLocalRing.depth_two_of_normal`.
   There are no forbidden declarations or attributes and no holed definitions.
   Scratch-copy `#print axioms` checks on all five declarations show exactly the three
   permitted axioms for `IsIntegral.exists_local_denominator_of_normal`; the other
   four declarations additionally use `sorryAx`, accounted for by the new depth lemma
   and the pre-existing depth and normality/reducedness dependencies.
3. **Auxiliary statements: PASS.** Read Stacks Tags 031S and 031T and each Lean proof.
   The denominator proof permits a kernel in the map from total fractions to the local
   fraction field and clears equality before cancelling the regular denominator.
   The quotient-height proof uses only S2, regularity, associated-prime localization
   and the two existing depth lemmas. Membership uses an associated prime containing
   the annihilator of the numerator class, so the local multiplier gives the required
   contradiction. The sole split-off hole is only the high-dimensional forward depth
   step, not a restatement of the criterion. Its docstring gives the finite-extension
   embedding and integrality argument from 031S. Checked fields (excluded by dimension),
   dimension-one domains, unit denominators (zero quotient), the zero ring (no primes),
   and products of domains (no global domain assumption in the total-fraction lemmas).
   New searches with “integrally closed local domain admits regular sequence length
   two”, “associated prime of the quotient by a regular element in an S2 ring”,
   Loogle `IsIntegrallyClosed, IsRegular` and `IsIntegral, IsIntegrallyClosed,
   IsLocalization`, and grep for associated-prime height and intersection/localization
   found no exact replacement. Grep hits concern all prime/maximal localizations or
   Dedekind domains, which do not discharge these statements. Also searched both Lean
   roots for normality/depth and regular-sequence variants. The remaining depth proof
   requires the finite-extension construction; it is not a few-minute closure.
4. **Route and pruning: PASS after repair.** The criterion opens its original hole
   directly, uses the proved source regular-local theorems in small dimension and the
   existing reducedness and total-fraction criteria, then the genuinely smaller new
   statements. Checked all ten removed old direct proof dependencies against the
   report: six bypassed, four retained in the depth-two proof plan. Restored proof-only
   imports of Kollár and the nonzerodivisor theorem in that module, keeping the plan's
   existing unfinished work in the import closure. No proof-only import is public.
   Read `dag/units/sk-thm-p1.json`: neither this item nor its auxiliaries realizes a
   unit statement or step; all `realized` entries and the unit route remain intact.
5. **Nodes: PASS after repair.** Read all five node files against their declarations
   and proofs. All new nodes have source, searches, creation, blueprint ancestry,
   chapter/unit and Lean records; each proof dependency set equals the union of step
   uses. Removed `lem-weil-pbc-localization-dimension-chains-below-prime` from the new
   quotient-height node, since the Lean proof does not use dimension equals height.
   The original criterion's node records the new associated-prime route and retains
   its statement unchanged.

Second-reading changes: updated the criterion's stale conductor-induction docstring to
match its actual proof; restored the depth lemma's planned proof imports; removed the
unused quotient-height DAG dependency; explicitly recorded one original hole closed,
one new hole added, and net zero for this decomposition. No theorem signature or proof
body needed repair. The only independent new sorry-free result is the denominator lemma;
the two proved S2 proof bodies still depend on the pre-existing depth holes.
