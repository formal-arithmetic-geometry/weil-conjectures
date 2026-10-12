## What changed

Replaced the sole sorry in CategoryTheory.brownCohomologicalRepresentability by a
complete Lean assembly of two strictly separate parts of the Stacks Tag 0A8F proof.
The signature and existing docstring are unchanged. The proof extracts the compact
family, constructs a Yoneda map on its shifts, extends component invertibility by
generation, and uses NatIso.isIso_of_isIso_app and the inverse of asIso.
Two new modules state the construction and detection parts. Their proof-only imports
retain CompactHomHocolim and CompactGeneratorsBuildObjects, respectively. Updated the existing
node's proof and dependencies to agree with this assembly.

## Proved and sorry left

Closed: CategoryTheory.brownCohomologicalRepresentability (one original hole).
This is a decomposition, not an axiom-free proof of Brown representability.
Added two holes, both whole proofs of named public theorems in separate modules:

- CategoryTheory.brownRepresentabilityConstruction, node
  lem-pc-brown-generator-construction: constructs a map invertible only on shifted
  compact objects, without any generation hypothesis.
- CategoryTheory.cohomologicalGeneratorDetection, node
  lem-pc-cohomological-generator-detection: starts with an arbitrary given object
  and map, extending the assumed generator invertibility to all objects.

No sorry remains in the original module. Net holes closed minus added is -1.
The three files compile in import order. The assembly uses no data definition
chosen from an unproved existence statement: both witnesses are eliminated only
inside the proof of the existential theorem.

Edge cases checked in words: an empty compact family imposes no restriction in
the construction and the zero object gives a map; an empty generating family
forces every object to be zero, so detection holds. The construction requires all
integer shifts, and all index sets (pairs of generator, shift, and H-element) fit
Type v. Detection includes compactness and generation; neither assumption was
silently dropped. Source checked directly at https://stacks.math.columbia.edu/tag/0A8F.

## No longer needed

Removed direct proof imports Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
and Sheaf.CategoryTheory.CompactHomHocolim from the original module. It now uses
only BrownRepresentabilityConstruction and CohomologicalGeneratorDetection.
Their old mathematical dependencies were relocated to the two new nodes' proof
plans, not discarded: compact_hom_hocolim is needed for construction, and
compactGenerators_buildObjects is needed for detection. Thus no mathematical
node is claimed pruned. The old Yoneda, Hom exactness, homological functor,
triangulated category and five-lemma dependencies likewise remain in those plans.
Neither new statement is the original theorem renamed or repackaged: the first
has no generation hypothesis and only concludes invertibility on a specified
small collection; the second constructs no representing object or map.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies do not themselves construct the Brown map or prove the
cohomological closure of its isomorphism locus. The original DAG groups these
arguments into long steps; the two new statements expose that missing glue.
The construction and detection follow the original route and do not bypass a
blueprint unit. The unit's realized field does not assign this node a unit step.
The local literature/stacks-project/derived.tex is absent; the cited source was
read at its official Stacks page. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and source searches were available and found no replacement.

## New nodes

lem-pc-brown-generator-construction is in
lean/Sheaf/CategoryTheory/BrownRepresentabilityConstruction.lean. Its docstring
and node give the coproduct, kernel-killing, telescope and compact-Hom argument.

lem-pc-cohomological-generator-detection is in
lean/Sheaf/CategoryTheory/CohomologicalGeneratorDetection.lean. Its docstring
and node give the five-lemma closure, coproduct closure and generator-building
argument. Both inherit the original chapter and unit and its blueprint ancestor.
No definition or existing statement changed; no change record is required.


## Second reading by T3

1. **Visible declarations: pass.** Diffed the existing module against the read-only
repository. Its only changes are two plain proof imports and the theorem body.
Checked the theorem signature byte for byte, including every universe, implicit
instance and hypothesis; the existing docstring and both public imports are also
unchanged. The other two modules are new; no existing definition or target changed,
so no change record is required.

2. **Kernel and holes: pass as a decomposition.** Compiled all three files in import
order using lcompile.py after the repair (2.1, 2.1 and 2.0 seconds, no warnings or
errors). Appended #print axioms to temporary copies using lcompile's probe facility
for each of the three declarations: each lists only propext, Classical.choice,
Quot.sound and sorryAx. Scanned all delivered Lean for forbidden declarations and
holes: exactly the two reported named public theorems have whole-proof sorry;
there are no definitions, arbitrary witness definitions, hidden holes or forbidden
axioms. The top theorem eliminates witnesses inside its existential proof and
correctly reverses the Yoneda-to-H isomorphism. This closes one original hole and
adds two lower holes (net -1); it is not an axiom-free proof of representability.

3. **Split statements: pass.** Read both statements, complete docstring proofs and
nodes against the construction and final detection arguments of the official
Stacks Tag 0A8F page, https://stacks.math.columbia.edu/tag/0A8F. Construction uses no
generation and promises invertibility only on the prescribed compact shifts;
detection starts from a given map and object and constructs neither. They are
strict subarguments, not a renaming of Brown representability. The kernel-killing
indices are Type v because generator indices, integers, H-values and morphisms
are small in v. Shift equivalences preserve compactness and coproducts. Checked
the empty-family case: construction can use zero; detection's generation forces
all objects to be zero, and additive functors send zero to zero. A family consisting
of zero objects gives the same checks. No additional assumption or conclusion is
needed by the assembly. Independent searches used LeanFinder for transformations
of homological functors detected by generating sets, Loogle for preadditiveYoneda,
and grep for localizing/telescope/component isomorphisms. Read Mathlib's
Triangulated.Generators and LocalizingSubcategory: their classical/strong generator
and Verdier localization notions do not supply these statements. Source searches
in lean/Sheaf and lean/WeilConjectures found no replacement. Neither split lemma
has a short available proof to close in this reading.

4. **Route and pruning: pass after import repair.** The assembly takes the direct
construction/detection route of the source. Public imports provide the existing
signature; the two new theorem imports are plain imports. The new modules' public
imports supply only their signatures; restored the planned compact telescope and
object-building dependencies as plain imports. The old direct proof dependencies
are now accounted for explicitly: lem-pc-compact-hom-hocolim occurs in construction;
lem-pc-compact-generators-build-objects, lem-weil-pbc-hom-out-of-triangle-exact and
lem-weil-pbc-five-lemma occur in detection; lem-galois-yoneda-hom-bijection occurs
in construction; the triangulated, abelian and homological definitions are provided
by signature imports and the two plans. lem-weil-pbc-hom-into-triangle-exact is no
longer a direct step of Brown's proof: it is used below in CompactHomHocolim and
CompactGeneratorsBuildObjects. Thus every old direct dependency is relocated or
accounted for; no mathematical node or module is claimed pruned. Read
sk-thm-picard-duality.json: its realized fields are empty and this item realizes
no separately assigned unit step; no unit record or route is altered.

5. **DAG: pass.** Compared the existing node with its new assembly; proof and
proof_deps cite exactly the two applied intermediate nodes, with document origin.
Read each new node in full: statement matches its Lean declaration; source,
complete stepwise proof, union of step dependencies, proof_origin, search records,
status, created, blueprint ancestry, chapter/unit and Lean record are present.
The new construction and detection dependency plans agree with their docstrings
and with the restored proof-only imports. Existing statements and stmt_deps stay
unchanged.

**Changes made by this reading:** restored import
Sheaf.CategoryTheory.CompactHomHocolim in BrownRepresentabilityConstruction and
import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects in
CohomologicalGeneratorDetection. This prevents the unproved planned dependencies
from being accidentally pruned out of the import closure. Added this independent
review and the explicit old-dependency accounting. No proof or signature rewrite
was needed; closed/added holes remain one/two, respectively, with no modules pruned.
