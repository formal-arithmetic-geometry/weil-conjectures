## What changed

Proved AlgebraicGeometry.nonempty_affineOpen_higherDirectImage_sections_iso by
restricting to the inverse-image open, applying the existing Leray edge, and
composing the source-cohomology, direct-image restriction and section comparisons.
Its signature and public imports are unchanged.

Added two modules, both with complete Lean proofs:
Sheaf.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing and
Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction. The first applies the
existing qcqs quasi-coherence theorem, affine vanishing and the module/source
comparison. The second applies the existing source-library ordinary restriction theorem to
the cartesian open restriction square and converts its pullback input to
restriction using Mathlib restrictFunctorIsoPullback. All added imports in the item are proof-only.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.nonempty_affineOpen_higherDirectImage_sections_iso
(lem-pc-affine-open-higher-direct-image-sections-iso).

Also proved AlgebraicGeometry.isZero_affine_higherDirectImage_moduleCohomology
(lem-pc-affine-higher-direct-image-cohomology-vanishing) and
AlgebraicGeometry.nonempty_higherDirectImage_openRestriction_iso
(lem-pc-higher-direct-image-open-restriction). No holes added; no sorry remains in any delivered module. Imported declarations
may still depend on sorry, as intended by stage 3; this is a proof from existing
statements, not an assertion that the full target import closure is axiom-free.

Positive vanishing requires p > 0 and includes q = 0. The restriction theorem
has no affine, quasi-coherence or finiteness assumptions and includes degree zero
and empty opens. The original theorem's qcqs and quasi-coherence hypotheses are
retained. No arbitrary existence witness is installed in a definition.

## No longer needed

Removed direct proof import Sheaf.Paper.HigherDirectImagePresheaf and the direct
dependency lem-weil-pbc-higher-direct-image-presheaf from the item: ordinary
restriction is proved on complexes, without the sheafification description.
Other importers may still use that module.

Removed direct proof import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
from the item; it remains used by the proved vanishing helper, so is not globally
pruned. Removed direct proof import Sheaf.Topology.RestrictInjectiveResolution
from the item; it remains used by the existing open cohomology comparison. The restriction
helper uses the source-library restriction theorem instead. The uniform-bound clauses of lem-pc-finite-support-hi are
not needed; only ordinary higher-image quasi-coherence is used in the helper.
No global reachability claim is made for other targets or importers.

The complete old proof_deps minus new proof_deps is:
lem-pc-affine-vanishing (now used by the vanishing helper),
lem-pc-finite-support-hi (only its quasi-coherence clause is needed, through the
existing ordinary source theorem),
lem-sc-ringed-space-restrict-injective-resolution (still used by the imported
open cohomology comparison), and
lem-weil-pbc-higher-direct-image-presheaf (replaced by ordinary restriction).
These are removed direct dependencies; none is asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox left the vanishing helper sorry because it reported an
import cycle through DirectImage.Sections. Rechecking the current source graph
returns yes: DirectImage.Sections no longer reaches this item. Its existing
isQuasicoherent_higherDirectImage applies under QuasiSeparated, so closes the
helper without a new hole. Its section comparison still requires IsSeparated
and is not used. OrdinaryHigherImageQuasiCoherent is another acyclic interface,
but its compiled module was absent from the published snapshot during this work.
The DAG helper uses the existing ordinary quasi-coherence node as its mathematical
dependency; its Lean proof uses the source declaration of the same statement.

The earlier source citation of Tag 01E4 for open restriction should be 01E5;
01E4 is the cohomology-presheaf description. Checked the primary Stacks pages
https://stacks.math.columbia.edu/tag/01XJ (clause 1),
https://stacks.math.columbia.edu/tag/01XK and
https://stacks.math.columbia.edu/tag/01E5. The unit's realized statement and
steps are unchanged. Local Stacks source files are absent: WANTED coherent.tex,
cohomology.tex and sites-cohomology.tex. The new proof origins remain agent.

The first concurrent compile checks timed out on the restriction module;
compiling it alone initially succeeded in 29 seconds, but subsequent runs also
timed out. Rechecking the now acyclic source-library restriction theorem gave
a shorter route, so the explicit resolution construction was replaced by its
application and a pullback/restriction conversion. Validation is through lcompile.py
and the final deliver3.py --no-push dry run. The first worker performed no push; delivery follows the independent second reading.

## New nodes

lem-pc-affine-higher-direct-image-cohomology-vanishing records positive Leray
column vanishing for a qcqs morphism over an affine base. It is fully proved
from the existing quasi-coherence, affine-vanishing and source-comparison
statements. Its module is AffineHigherDirectImageCohomologyVanishing.

lem-pc-higher-direct-image-open-restriction records the fully proved ordinary
higher-direct-image restriction comparison in HigherDirectImageOpenRestriction.
Both nodes are in dag/nodes/sec-picard-framework/. No change record is needed:
existing signatures, visibility and public imports are unchanged.

## Second reading by H1

1. Compared every delivered module with the read-only repository. Only the item
already exists there; its entire theorem signature, existing docstrings and
public imports are byte for byte unchanged. The two helper modules are new.
The existing node changes only proof, proof_deps and proof_origin. No definition,
target statement or other module interface is changed. Verdict: pass.

2. Compiled all three modules in import order using lcompile.py: no errors or
warnings (5.8, 6.6 and 11.2 seconds). Inspected every proof and scanned the delivered
Lean for forbidden declarations and sorry: none occurs. Scratch copies with
#print axioms for all three theorems report exactly propext, Classical.choice,
Quot.sound and sorryAx. The last comes from still-open imported statements,
including the upstream quasi-coherence and ordinary open-restriction theorems;
these helpers are proved reductions from those statements, not proofs that those
imported holes have been closed. There are no new definitions or permanent
choices of data from mere existence. Verdict: pass within the stage-3 contract.

3. There are no new sorry statements. Read both new theorem signatures and their
proofs, together with DirectImage.Sections, ModuleCohomologySourceComparison,
OpenModuleCohomologyComparison and LerayDegenerateSections. Checked the primary
Stacks statements [01XJ](https://stacks.math.columbia.edu/tag/01XJ),
[01XB](https://stacks.math.columbia.edu/tag/01XB),
[01XK](https://stacks.math.columbia.edu/tag/01XK) and
[01E5](https://stacks.math.columbia.edu/tag/01E5).
The vanishing helper needs qcqs and quasi-coherence but no separatedness; it
allows q=0 and correctly excludes cohomology degree p=0. A nonzero module on a
point demonstrates why that exclusion is essential. Zero modules and empty
affine bases give zero cohomology. The restriction helper has no qcqs or
quasi-coherence condition; at p=0 it is ordinary restriction of pushforward,
for U=top it is the identity comparison, and for U=empty both sheaves vanish.
The helpers isolate two strictly smaller parts of the Leray argument.
Searched Mathlib through msearch grep, Loogle and LeanFinder with different
queries, and searched both local Lean roots and DAG records with rg. Found the
existing source restriction theorem and used it, with the nontrivial
restrictFunctorIsoPullback conversion already written by the first worker;
found no exact signature duplicate or shorter direct proof of the item under
QuasiSeparated. The derived-category open restriction node is a different
statement about unbounded complexes. Verdict: pass.

4. The item's proof first obtains the Leray edge on the restricted morphism,
uses affine positive-column vanishing, and composes explicit source and target
comparisons. Checked all isomorphism directions, restriction of quasi-coherence,
and preservation of qcqs under the open base change. The source section theorem
requires IsSeparated and cannot replace this proof. All newly added item imports
are proof-only; Modules.Tilde supplies isQuasicoherent_restrictFunctor. The new
modules' public imports supply signature notions and the Grothendieck enough-
injectives instance needed to elaborate rightDerived without adding hypotheses.
Proof comparison imports are plain imports. Completed the exact old-minus-new
proof_deps list under No longer needed. No global pruning is claimed. Inspected
sk-thm-picard-duality.json: realized is unchanged and none of these nodes replaces
a realized unit statement or step. Verdict: pass.

5. Matched each DAG step to the Lean proof: the item uses the two helpers, Leray,
the two cohomology comparisons and open sections; the vanishing helper uses
ordinary quasi-coherence, affine vanishing and the source comparison; restriction
specializes the existing source theorem to isPullback_morphismRestrict and maps
the restriction/pullback iso. Both also explicitly use the named enough-injectives
theorem. New nodes have source, blueprint ancestry, searches, creation metadata,
chapter/unit and Lean records. Corrected the new lean.statement fields to the
verbatim multiline signatures, stale grep verdicts and the omitted enough-
injectives proof dependencies. Verdict: pass after these repairs.

Changes by this second reading: corrected the new vanishing docstring's informal
induction explanation to refer to the qcqs-open induction principle (08DR), rather
than suggest induction on an arbitrary intersection's affine-cover size; wrapped
its line to 100 columns; repaired node metadata and completed pruning reporting.
No Lean proof term or existing signature changed. One original hole closed, zero
holes added; both new helper theorems have complete Lean proofs.
