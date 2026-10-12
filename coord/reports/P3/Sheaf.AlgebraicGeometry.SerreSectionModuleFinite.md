## What changed

Replaced the sorry in AlgebraicGeometry.serreSectionModuleFinite with a complete Lean
combination of three independent steps in new modules:
Sheaf.AlgebraicGeometry.SerreSectionModuleConstruction,
Sheaf.AlgebraicGeometry.SerreSectionModuleTailFinite, and
Sheaf.AlgebraicGeometry.SerreSectionModuleComponentFinite.
The original theorem signature, including universes, coherence hypothesis, grading,
negative-degree vanishing, and homogeneous multiplication compatibility, is unchanged.
The construction does not assume coherence and asserts no finite generation. The tail
statement asserts finiteness of only an eventually high span. The component statement
asserts finiteness degree by degree, with no uniform generating bound.

The proved argument forms the finite supremum of the spans of the degrees in Fin N,
adds the finite high tail, and proves that this sum is top by induction on the internal
decomposition. Negative homogeneous elements are zero; degrees below N are in the
finite supremum; degrees at least N are in the tail. Mathlib's FG.sup then proves
Module.Finite. In particular N=0 is handled by the empty Fin 0 supremum.

Updated the original node's proof, proof_deps and proof_origin to this decomposition.
New node docstrings and JSON records explain the remaining geometric and module-action
steps, with the original source and exact homogeneous action. No definitions, existing
statement signatures, or target statements were changed. The unit's realized lists are
empty, and the original twist-quotient/Serre-vanishing route is retained in the tail node.

Validation: all four sandbox modules compile in import order using lcompile.py.
The source's online Stacks 01YS and 0AG6 pages were read because the local coherent.tex
checkout is absent. LeanFinder and source searches found no shorter existing result;
LeanSearch returned HTTP 500, recorded without a mathematical verdict.

## Proved and sorry left

Closed the one original hole, AlgebraicGeometry.serreSectionModuleFinite
(node lem-sc-p1-serre-section-module-finite). Its body has no sorry.
This is a decomposition, not a proof free of sorry dependencies: one upper hole closed
and three lower holes added. The three new remaining public theorem holes are:

- AlgebraicGeometry.serreSectionModuleConstruction
  (lem-sc-p1-section-module-construction).
- AlgebraicGeometry.serreSectionModuleTailFinite
  (lem-sc-p1-section-module-tail-finite).
- AlgebraicGeometry.serreSectionModuleComponentFinite
  (lem-sc-p1-section-module-component-finite).

Each is in its own new module, with a complete natural-language proof and blueprint tag.
No hole remains inside the combination argument, a definition, or a private declaration.
Edge checks: the construction works without coherence; G=0 gives zero pieces and empty
bases. For G=O and G=O(-1) it gives S and the nonnegative truncation of S(-1). The component
statement is compatible with infinite generation across infinitely many degrees, so it
cannot itself replace the target. The tail statement does not assert finiteness of low
degrees. No internal-grading assumption is needed in either finiteness step: surjective
maps into the spans suffice, while the combination uses the internal grading to exhaust M.

## No longer needed

Removed these direct proof imports from SerreSectionModuleFinite:

- Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
- Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
- Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
- Sheaf.Paper.PQFCohomology
- Sheaf.RingTheory.GradedSubmoduleFinite
- WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
- WeilConjectures.AlgebraicGeometry.Cohomology.Serre
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

The original public imports remain because they belong to the original interface.
The geometric dependency nodes are now needed by the tail/component nodes, not by the
combining proof directly. They are not claimed globally pruned:
lem-pc-projective-space-twist-quotient, lem-sc-p1-twist-exists,
lem-sc-ext-tensor-exact, pqf-def-cohomology,
lem-pc-projective-space-serre-vanishing, lem-pc-projective-space-twist-cohomology,
lem-sc-p1-coherent-finite, lem-sc-p1-proj-shifted-free-twist, and lem-pc-twist-tensor.
The definition nodes def-sc-p1-standard, pqf-def-coherent,
def-weil-pbc-proj-twisting-sheaf and def-pc-projective-space-twist still describe the objects
used by those geometric steps or by the original statement.

The tail proof needs only ordinary finite generation of a submodule of a finite module
over the noetherian polynomial ring, not homogeneous generators. Consequently
lem-sc-p1-graded-submodule-finite / Sheaf.RingTheory.GradedSubmoduleFinite is not needed by
this route. Its work and its specialized homogeneous-generator argument are pruned here;
other targets may still use it.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric statements do not directly construct the canonical S-module on the
sum of twisted global sections. This requires the construction node: multiplication of
local fractions proves the action laws, and summand images supply the internal grading.
The stated section equivalences are additive, so the component finiteness proof must
explicitly use hphi for constant polynomials to recover k-linearity; an arbitrary additive
equivalence by itself would not transfer a k-basis. The tail proof must also transport
RingedSpace.IsCoherent to the quasi-coherent/finite-presentation hypotheses in the existing
Serre statements on the noetherian projective line. These steps are stated in full in the
new nodes rather than silently treated as immediate applications of the existing lemmas.

No statement was found false. The search service failure was not treated as evidence
that a theorem is absent.

## New nodes

lem-sc-p1-section-module-construction, in
lean/Sheaf/AlgebraicGeometry/SerreSectionModuleConstruction.lean: canonical nonnegative
section module and action, for any G, with no coherence or finite-generation assertion.

lem-sc-p1-section-module-tail-finite, in
lean/Sheaf/AlgebraicGeometry/SerreSectionModuleTailFinite.lean: the high-degree span is
finite after a cutoff, from the twist quotient, exact twisting, Serre vanishing, twist
cohomology, and ordinary noetherian submodule finiteness.

lem-sc-p1-section-module-component-finite, in
lean/Sheaf/AlgebraicGeometry/SerreSectionModuleComponentFinite.lean: each degree has a
finite S-span, from coherent cohomology finiteness and constant-scalar compatibility.

All inherit sec-picard-framework / sk-thm-picard-duality and the blueprint ancestor
lem-sc-p1-graded-resolution through lem-sc-p1-serre-section-module-finite.
No change record is needed: no existing public interface was changed.

## Second reading by P3

1. Compared the original module with the repository by diff and compared the entire
   theorem signature byte for byte. Verdict: unchanged; no existing definition,
   declaration signature, target or unit was changed. The delivery adds three public
   intermediate theorems, each in its own module, rather than a renamed target.
2. Compiled all four modules locally in import order, both before and after the repairs.
   Verdict: clean. The only explicit holes are the three named theorems listed above,
   each with a source, full proof docstring and node. A scratch copy printed the axioms
   of all four declarations: only propext, Classical.choice, Quot.sound and sorryAx.
   There are no forbidden declarations or hollow definitions. The parent is a proved
   reduction, not an axiom-free completion: one hole closed, three holes added (net -2).
3. Read every split statement and proof docstring, and checked Stacks 01YS and 0AG6
   online. Verdict: true and strictly partial. Construction assumes no coherence and
   concludes no finiteness; component finiteness gives no uniform cutoff; tail finiteness
   does not cover low degrees. Without internality in the latter two statements, the
   map from the external sum into M still has the stated span as image, so their
   proofs do not require independence of the subgroups. Checked G=0, G=O and G=O(-1),
   constants (e=0), negative components, and N=0. No lower statement can be closed in
   a few minutes: the action construction and the geometric transports remain work.
   Repeated LeanFinder searches using polynomial action on tensor powers, coherent
   tensor-twist sections, and surjections from shifted polynomial modules; searched
   Loogle for FG/span and rg for sectionModule, sectionsModule, twist finiteness and
   IsInternal/sections in Mathlib, the upstream library and Sheaf. No exact replacement
   appeared. Loogle found FG.span, which may shorten the future component proof once
   its k-module structure and finite-dimensionality are established; it does not close
   the current statement by itself.
4. Read the reduction from the top down. Verdict: the finite-supremum argument is
   correct and uses Mathlib's fg_iSup, FG.sup and decomposition induction. Every old
   proof dependency is accounted for under No longer needed; the geometric dependencies
   remain in the new tail/component route. Only GradedSubmoduleFinite is pruned from
   this route. The unit realized fields are statement=[] and steps=[[]]; no realized
   unit step is bypassed, and the geometric twist quotient / Serre route remains.
   Found and repaired missing proof-dependency imports in the new geometric modules.
5. Checked all four node records, union of proof-step uses against proof_deps, the
   new-node required fields, and verbatim Lean signatures (normalizing whitespace).
   Verdict: consistent. Existing-node edits are restricted to stage-3-owned fields;
   new nodes inherit the original chapter/unit and blueprint ancestor.

Changes made by the second reader: added plain proof imports to the tail module for
FiniteLocallyFreeTensorExact, ProjShiftedFreeTwist, ProjectiveLineTwistExists,
PQFCohomology, Cohomology.Serre and ProjectiveSpace.Twist; to the component module for
ProjShiftedFreeTwist, ProjectiveLineTwistExists and Cohomology.ProjectiveLine. These are
needed by the pending proofs recorded in their nodes, so those modules stay reachable.
In both new geometric modules, replaced public Finiteness.Basic by Finiteness.Defs
(the signature only uses FG) and removed the unused public DirectSum.Module import.
No theorem statement, proof body, node route or hole count changed in this reading.
