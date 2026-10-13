## What changed

Proved `Algebra.nonempty_popescuCorrectionQuotient_reduction_equiv` directly in
`Sheaf.RingTheory.PopescuCorrectionReduction`, following the existing node's three-step
plan. Constructed the reverse map by descending the reduced coefficient map and the
old-variable evaluation through their ideals; constructed the forward map by killing
the corrected relations and then the image of I. Checked both inverse identities on
coefficients and variables, and checked R/I scalar compatibility on representatives
from R. All existing declaration signatures, definitions and docstrings are unchanged.

Removed the provisional `Algebra.exists_popescuCorrection_reduction_algHom_pair` and
its unlanded node `lem-weil-pbc-popescu-correction-reduction-alghom-pair`: that statement
was equivalent to the goal and did not constitute a genuine reduction. No new
declarations or nodes remain. Restored the existing node's original proof plan and
empty `proof_deps`, which agree with the direct proof.

Replaced the unused public import `Mathlib.RingTheory.Smooth.StandardSmooth` with
`Mathlib.Algebra.MvPolynomial.Rename`. The latter is public because the existing
relation definition uses `MvPolynomial.rename`. `Mathlib.RingTheory.Ideal.Over` is
needed for the quotient scalar algebra structures appearing in the statement.

## Proved and sorry left

Hole closed: `Algebra.nonempty_popescuCorrectionQuotient_reduction_equiv`
(node `lem-weil-pbc-popescu-correction-reduction-equiv`).

Holes added: none. Holes left in delivered modules: none. Original holes proved:
1 of 1; split off: 0. This is a full proof, not a decomposition. The local hole delta
is closed 1, added 0; the maintainer's pinned-baseline ledger determines project-wide
closure and pruning figures.

Local compilation through `lcompile.py` succeeds without warnings. A scratch copy
with `#print axioms` verifies that the proved theorem, `Algebra.popescuCorrectionRelation`
and `Algebra.popescuCorrectionIdeal` use only `propext`, `Classical.choice`, `Quot.sound`.
No forbidden declarations, hidden holes, or data chosen from an unproved theorem occur.

## No longer needed

Removed import: `Mathlib.RingTheory.Smooth.StandardSmooth`.
The original node's `proof_deps` was empty, so there are no old DAG dependencies to
prune. No project module is claimed pruned. The unlanded homomorphism-pair node was
deleted from the sandbox, and the existing node no longer refers to it.

## Where the brief, the DAG or earlier work was wrong

The first worker's claim that mutually inverse algebra homomorphisms were strictly
weaker than an algebra equivalence was incorrect: the two formulations are equivalent.
The proposed split merely moved the entire mathematical argument to a new hole and
was rejected during this reading. The original node's proof plan already gave the
needed construction; no additional quotient-calculation theorem was necessary.

Independent searches (recorded in `searches.jsonl`) used a polynomial-extension
quotient formulation in Lean Finder, a Loogle query for evaluation and renaming, and
Mathlib grep. Lean Finder located the coefficient-quotient equivalence, which is only
an ingredient and does not itself handle the corrected relations. Loogle located
`MvPolynomial.eval₂Hom_rename`. Searches of lean/Sheaf, lean/WeilConjectures and the
upstream source found no existing complete proof of this reduction. The direct
universal-property construction avoids additional quotient-transport infrastructure.

Checked the cited equality in [Stacks Project, Tag 07CK](https://stacks.math.columbia.edu/tag/07CK).
The quotient computation itself needs neither the ambient lifting lemma's square-zero
hypothesis nor its smoothness assumptions. The existing Lean statement reflects this.

## Second reading by X3

1. **Interface preservation — pass.** Read the full repository and delivered module
   and compared them with `diff -u`. All five existing declarations have byte-for-byte
   identical signatures; all four existing definitions/abbreviations have identical
   bodies. The only retained changes are the proof and the explicitly reported import
   replacement. There are no statement changes. The public-import change is documented in
   `coord/changes/PopescuCorrectionReductionImports.md`.
2. **Proof and trust — pass after repair.** Replaced the provisional hole by concrete
   quotient lifts and polynomial evaluation homomorphisms. Compiled the delivered
   file without errors or warnings, and checked axioms in a scratch copy. There are
   no sorries, axioms, unsafe/opaque declarations, foreign implementations, or hollow
   definitions. Every quotient lift has a proved kernel-inclusion argument.
3. **Split statements — repaired; none remain.** Rejected and removed the equivalent
   homomorphism-pair restatement and its node. No new statement needs a docstring or
   node. Checked empty old-variable and relation lists, empty correction lists, I=0,
   I=top, and zero rings mathematically: all constructions and extensionality arguments
   remain valid, and no nontriviality hypothesis is used.
4. **Route and pruning — pass.** The proof follows the original node's forward map,
   reverse map and inverse/scalar checks. Independent searches found no complete
   existing theorem that bypasses this calculation. Removed the smoothness import;
   the two remaining imports support the public definitions and statement. Read
   `dag/units/sk-thm-p1.json`; its `realized` route is retained, with no unit or chapter
   step bypassed. The old dependency list is empty and fully accounted for above.
5. **DAG agreement — pass after repair.** Restored the existing node's original three
   proof steps, empty `proof_deps`, and documentary `proof_origin`; these now match
   the implemented proof. The node's statement, source, unit, chapter and Lean
   attachment are unchanged. No new nodes or forced adaptations remain.

Changes made by this reading: removed the equivalent split-off theorem and node;
proved the entire original statement; restored its docstring and original DAG plan;
pruned the unused smoothness import; corrected the report's progress accounting.

## Change records

`coord/changes/PopescuCorrectionReductionImports.md` documents the public-import
replacement. The first dry run required this record; the downstream scan lists
200 modules, all reached through the sole direct importer, which already publicly
imports StandardSmooth. No declaration changes meaning and no adaptation is needed.

Compiled the unchanged direct importer
`Sheaf.RingTheory.PopescuStandardReductionFactor` against the modified module through
lcompile's sandbox overlay; it also compiles without warnings. This checks the public
import pruning without delivering an unnecessary adaptation.
