## What changed

Replaced the hole in
AlgebraicGeometry.openSections_cohomology_unit_comparison with a proof from two
independent computational statements. The first supplies a natural isomorphism
normalized on every ordinary complex class. The second identifies the restricted
structure class before comparing it with ambient derived sections. The proof takes
the component equivalences, evaluates naturality, and composes the structure-class
identity with the ordinary-unit square. The existing structure restriction
isomorphism and all existing declaration signatures are unchanged.

Added OpenSectionsCohomologyModel with explicit, hole-free ordinary section,
complex, homology and ordinary-to-derived comparison constructions, and
OpenSectionsStructureClass with the explicit extended-structure complex isomorphism.
All data are constructed directly; no definition chooses an unspecified witness
from an unproved existence theorem.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.openSections_cohomology_unit_comparison
(lem-sc-open-sections-cohomology-unit-comparison).

Added two holes, each in its own public named theorem:
AlgebraicGeometry.exists_openComparison_cohomology_model_iso
(lem-sc-open-sections-cohomology-model-comparison), and
AlgebraicGeometry.openComparison_structure_class
(lem-sc-open-sections-structure-class).

This is a decomposition, not a sorry-free proof of the whole argument: one upper
hole closed and two strictly smaller computational holes added. The original
module has no remaining sorry. All new definitions and all final combination
steps are proved. The new statements were checked on empty U and the zero ring:
all the ordinary sections and canonical classes are zero, and the same maps apply.
They impose no quasi-coherence, boundedness, affine-open, or nonemptiness hypothesis.

## No longer needed

Removed the original direct proof import
Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact. Its theorem remains a planned
dependency of the normalized model-comparison node; this is not a claim that the
whole module is globally pruned.

The original node now depends directly on the two new computations and on
def-sc-koszul-open-system for its already constructed restriction isomorphism.
def-sc-principal-open-alternating-total and
lem-sc-derived-structure-evaluation-one-bijective remain needed for the definitions
appearing in the statements. The evaluation-one bijectivity theorem itself is not
used: only its independent, explicitly constructed derivedStructureGlobalOne is
needed. No unit statement or unit proof step is bypassed; the unit record has no
realized node at this position. No existing library module is claimed globally
unreachable. The complete list removed from the original direct proof_deps is
lem-sc-derived-open-restriction-adjunction-exact,
def-sc-principal-open-alternating-total, and
lem-sc-derived-structure-evaluation-one-bijective. The latter two remain statement
dependencies and their modules remain public imports of the original item.

Second reading removed the unused public import
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp from
OpenSectionsCohomologyModel. Its generic composition criterion remains a possible
proof tool for the open normalized-comparison hole, not a used declaration.
The exact-adjunction planned proof import is retained privately in the model module.
OpenSectionsCohomologyModel now imports DerivedCategory and
RingedSpaceModuleCohomology directly instead of
DerivedStructureEvaluationOne; the latter is imported by OpenSectionsStructureClass,
whose statement actually uses derivedStructureGlobalOne.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old plan gave the correct mathematical
computations but no declarations for the normalized comparison square or the
ordinary structure-class equality. These are now separate compilable statements,
with explicit maps and independent proof plans.

LeanSearch was unavailable (Internal Server Error); semantic search, Loogle,
and source searches were used and recorded. The cited Stacks pages (08BS, 079V,
06Z0) were read online because the local literature tree does not contain the
cited TeX files. WANTED: the local Stacks cohomology and derived-schemes TeX sources
for these tags. The computational glue and new proof plans are marked agent-written.

## New nodes

lem-sc-open-sections-cohomology-model-comparison states the comparison on arbitrary
ordinary complexes and its ordinary-unit square; it makes no assertion about the
structure class. Its explicit ordinary constructions are in
lean/Sheaf/AlgebraicGeometry/OpenSectionsCohomologyModel.lean.

lem-sc-open-sections-structure-class states the ordinary-to-derived restricted
structure-class equation, without an unknown comparison equivalence or ambient
derived sections. Its actual extension/single-complex isomorphism is in
lean/Sheaf/AlgebraicGeometry/OpenSectionsStructureClass.lean.

Both inherit sec-picard-framework and sk-thm-picard-duality, with the original
finite-duality blueprint ancestry. No interface change or forced adaptation was made.

## Second reading by H1

1. Compared the original module with its repository version using diff. Both existing
signatures are byte for byte unchanged; openStructureRestrictionIso and its docstring
and body are unchanged. Only proof imports, declaration-local elaboration options,
and the target proof changed. No existing definition or target meaning changed.
There are no change records or forced adaptations.

2. All three submitted modules compiled locally through lcompile.py. The only textual
sorry occurrences are the two public named split-off theorems listed above. All data
are explicit constructions: no witness of the model existence theorem is chosen in
any definition. The target locally obtains its isomorphism within its proof. No axiom,
unsafe, opaque, extern, implemented_by or kernel-check bypass occurs. Explicit #print axioms checks in scratchpad/lean/SecondReadingAxioms.lean compiled
successfully for every delivered declaration: every construction, including the
existing restriction isomorphism, uses only propext, Classical.choice and Quot.sound.
Exactly the two split theorems and the final combination additionally use sorryAx.
The delivery probe also checks all declaration axioms.

3. Read both split statements and their full docstring arguments, their nodes, the
restriction exact-adjunction theorem and the construction of derivedStructureGlobalOne.
Verdict: the normalized comparison is the general K-injective computation, independent
of any structure generator; the second is a calculation of that generator before
comparing with ambient derived sections. Neither restates the conjunction of the
original item. The ordinary-to-derived arrows and exact-restriction factorization
have the correct direction. For U empty or A the zero ring the classes and groups
are zero; for U top the ordinary comparison is the ordinary global-section identity.
Neither statement requires boundedness, quasi-coherence or nonemptiness. Read Stacks
[08BS](https://stacks.math.columbia.edu/tag/08BS),
[079V](https://stacks.math.columbia.edu/tag/079V), and
[06Z0](https://stacks.math.columbia.edu/tag/06Z0). New independent semantic, Loogle and
source searches are recorded in searches.jsonl and the new nodes. Also searched the
project with restriction/cohomology/sections terminology. The existing
nonempty_openRestriction_moduleCohomology_iso concerns right derived functors on
ordinary sheaves, not arbitrary unbounded derived objects or this normalized square.
The affineOpenSectionsDerivedUnit in KoszulOpenSectionsUnit is a specialization of
the generic constructed unit; importing it here would form a cycle because that
module imports the present item. No available result closes either hole in a few
minutes; both are retained as explicit computations, not reported as net progress.

4. Verified the final combination by naturality and equality transport, and checked
all old proof_deps against the report's pruning list. No unit is bypassed:
sk-thm-picard-duality has empty realized statement and step lists at this position,
and neither it nor its route changes. No global module pruning is claimed.

5. Compared node proof steps and dependency unions with the Lean reduction. Existing
node changes are only proof, proof_deps and proof_origin. Both new nodes have sources,
full plans, search records, split status, creation metadata, inherited chapter/unit
and blueprint ancestry, and Lean statement records matching the declarations.
Dependencies on the model and evaluation nodes in the structure-class node refer to
their constructed maps/class, not to an application of their holed theorems.

Changes made: removed the unused public composition import; replaced the model's
structure-evaluation import by direct DerivedCategory and RingedSpaceModuleCohomology
imports, retained the model's planned exact-adjunction proof import, and moved the
structure-evaluation import to OpenSectionsStructureClass; completed the explicit
old-dependency pruning list; recorded independent searches and this reading.
No additional proof holes were closed or added during the second reading.
