## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.SerreCriterionAffineness` with a complete Lean reduction.
For each first cohomology class, the proof obtains a finite-type subideal representative,
uses `ModuleCat.subsingleton_of_isZero` and the supplied vanishing hypothesis to make
that representative zero, and uses `map_zero` to show the original class is zero.
It then applies `AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero`.
The existing signature, universes, public imports and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.FiniteTypeIdealH1Representatives`, containing the
strictly smaller class-lifting step. Its theorem has no vanishing hypothesis and no
conclusion of affineness. Its morphism is required to commute with the two ideal
inclusions into the structure sheaf, and its ideal is required to lie below I.
Updated the parent DAG proof and dependencies to match this reduction.

Both modules compile cleanly together through lcompile.py --all. The unit record
sk-prop-av-pqf-finite has no realized nodes in its statement or step; this delivery
keeps the original Tag 01PG / 01FF / 01XF argument rather than changing its route.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.isAffine_of_finiteType_ideal_h1_zero`
(node `pqf-lem-serre-criterion`). No direct sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.ideal_h1_finiteType_representative`
(node `lem-pqf-finite-type-ideal-h1-representatives`). This theorem's proof is exactly
`by sorry`; its complete proof in words and source are in its docstring and node.

This is a decomposition: one hole closed and one added, net zero holes. It does not
claim an axiom-free proof of Serre's criterion. The imported existing theorem
`AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero` is also still sorry in the
baseline; it is used as the stage-3 brief intends and is not changed here.

Edge cases: the zero ideal is a finite-type stage and makes the index nonempty;
for an empty scheme all cohomology groups are zero. Neither edge case is excluded
by the new statement. No objects are defined by choosing arbitrary witnesses of
unproved existence theorems; all witnesses are eliminated inside theorem proofs.

## No longer needed

Removed the item's direct proof imports:
`Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit` and
`WeilConjectures.Compactification.FiniteTypeDirected`.
These are relocated to the new class-lifting module as its planned proof dependencies.
Their nodes `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` and
`lemma-nagata-ideal-directed-union-finite-type` are consequently no longer direct
proof dependencies of the parent, but remain required for its new child.
No entire node or module is pruned from the transitive argument. All existing public
imports remain, preserving the importers' interface.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's first step needs bridges not supplied by the
recorded declarations: `sSup_ofFiniteType_le_eq` is an equality in the ideal-data
lattice, not an IsColimit of module sheaves; its finite-type predicate is `ofFiniteType`,
whereas the item's hypothesis uses `toModules.IsFiniteType`; and the directed-colimit
cohomology theorem is group-valued open cohomology, whereas the item is module-valued
global cohomology. The new representative step records all three bridges without
changing an existing interface or duplicating the recorded results.

Mathlib searches: LeanFinder found local section and local generator lemmas but no
Serre criterion or ideal H1 representative. Loogle IsAffine returned unknown identifier;
a rightDerived query found the general definition and degree-zero/injective results.
Mathlib grep found only local cohomology supported in ring ideals, which has a different
statement. LeanSearch returned Internal Server Error, recorded as unavailable rather
than as a negative mathematical result. Local rg searches of both library roots found
no existing representative theorem. The Stacks source files named by the DAG are not
installed in this checkout; Tags 01XG, 01PG and 01FF were read on the official Stacks
website. Tag 01XG explicitly follows the same directed-colimit and vanishing route.

## New nodes

`lem-pqf-finite-type-ideal-h1-representatives`, in
`dag/nodes/sec-abelian-varieties/lem-pqf-finite-type-ideal-h1-representatives.json`,
states only finite-stage lifting of an arbitrary first cohomology class, with finite
type and inclusion compatibility. It realizes the first part of step 1 of
`pqf-lem-serre-criterion`. The vanishing implication and final affineness argument
are proved in the parent. No statement or definition changed, so no change record
or forced adaptation is required.

## Second reading by J1

1. Compared the existing module with the repository using diff. The sole existing
   declaration's signature and docstring are byte-for-byte unchanged; only its proof
   and two plain proof imports change. No definitions or target interfaces change.
   Compared the existing node as well: only proof, proof_deps and proof_origin change.
   Verdict: pass; no change record or forced adaptation is needed.
2. Compiled both modules in dependency order with lcompile.py --all, including after
   the import repair. Inspected all delivered Lean for forbidden declarations and holes:
   the only direct sorry is the named representative theorem; there are no definitions
   added at all. The parent eliminates witnesses inside a proposition proof and uses
   zero preservation of the induced linear map. Scratch-copy #print axioms checks show
   only propext, Classical.choice, Quot.sound and sorryAx (the explicitly open inputs).
   Verdict: valid reduction, not an axiom-free proof of the criterion.
3. Read the new theorem, its entire node and the recorded input declarations. Checked
   Stacks https://stacks.math.columbia.edu/tag/01XG, /tag/01PG and /tag/01FF directly.
   Directed finite-type subideals and the surjective colimit cohomology map prove its
   statement; comparison with module-valued cohomology is natural via the same
   injective resolution and exact forgetting. Inclusion compatibility rules out an
   arbitrary unrelated map. For x=0 the zero ideal and class work, including I=0 and
   the empty scheme; affine X also has only the zero H1 class. The statement has no
   vanishing premise and proves no affineness, so is strictly part of the argument.
   Independent LeanFinder search for cohomology of filtered unions found sheaf colimit
   existence and presentation lemmas, not class lifting. Loogle IsFiniteType with
   IsQuasicoherent found no result; Mathlib grep for rightDerived/colimit and filtered
   cohomology found only pointwise right-derived existence infrastructure. Local rg
   found no ideal H1 representative or finite-type bridge that closes this theorem.
   OpenModuleCohomologyComparison has a related comparison, but not the natural
   finite-stage lifting assertion and not the ideal diagram construction. Its proof
   confirms the resolution comparison route. Verdict: true, sourced, nonduplicate
   decomposition; closing the remaining diagram and comparison work is beyond a
   brief repair.
4. Read the two old dependency modules, QuasiCompactH1Zero and the unit record
   sk-prop-av-pqf-finite.json. No shorter existing criterion or class-lifting theorem
   was found. The unit's realized statement and step lists are empty; the Tag 01PG,
   01FF, 01XF route is retained. No longer needed lists both removed direct imports
   and their nodes; they remain transitive planned inputs of the new child, so no
   entire module is pruned. Existing public imports preserve the public interface.
   In the new module replaced public import Sheaf.Paper.PQFCohomology with the
   narrower public import Sheaf.Topology.RingedSpaceModuleCohomology: the signature
   needs the cohomology definition, not the Paper theorem. The child's two plain
   proof imports remain its stated proof plan. Verdict: pass after this import repair.
5. Checked new-node fields, source, searches, verbatim Lean statement, parent reduction,
   dependency unions and proof origins against both modules. The parent uses exactly
   the representative theorem and quasi-compact vanishing criterion; the child records
   finite-type directed union, open cohomology colimits and the cohomology definition.
   All existing-node edits are in stage-3-owned fields. Verdict: pass.

Second reading changed only the new module's cohomology import and this report.
The delivery closes isAffine_of_finiteType_ideal_h1_zero and adds
ideal_h1_finiteType_representative: one-for-one decomposition, net zero holes.
