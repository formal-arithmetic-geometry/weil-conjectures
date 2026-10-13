## What changed

Replaced the sorry in `AlgebraicGeometry.relativeMV_ses_presentation` by a complete
Lean proof using two steps. The geometric step produces a strict square of first
restriction maps and identifies its functorial cones with the specified overlap
objects. The general algebraic step turns any strict square of cochain maps into
a morphism of short exact mapping-cylinder rows. The original proof composes all
six vertex isomorphisms and derives all four differential equations and both
endpoint equations by postcomposition and associativity. Its signature and
public imports are unchanged. During the second reading, the two new modules
were reduced to the public DerivedCategory.Basic API, and the geometric module
received the private proof-plan imports recorded by its node.

Added `Sheaf.AlgebraicGeometry.RelativeMVConePresentation` and
`Sheaf.CategoryTheory.DerivedCategory.ConeDiagramSESPresentation`. The latter is
proved entirely from Mathlib: its objects, arrows, splittings, and comparison
morphism are constructed explicitly, without choosing data from an unproved
existence assertion. In Mathlib's cone order, the row is
A → B ⊞ Cone(id A) → Cone(t), with first map (t,0,id) and quotient
(b,a⁺,a) ↦ (-a⁺,b-t(a)). A contracting homotopy for Cone(id A) proves that the
middle projection becomes invertible after localization. The morphism of rows
uses β on B and the functorial cone map of α on Cone(id A).

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.relativeMV_ses_presentation`
(lem-pc-relative-mv-ses-presentation), by reduction to the geometric cone
construction followed by a proved algebraic construction.

Proved the new theorem `cone_diagram_ses_presentation`
(lem-pc-cone-diagram-ses-presentation), including degreewise short exactness,
localization comparisons, and functoriality. It and all its private helpers have
no sorry.

Added exactly one remaining hole:
`AlgebraicGeometry.relativeMV_cone_presentation`
(lem-pc-relative-mv-cone-presentation). Its proof is exactly `by sorry`, in its
own module, with a source and proof in words. It supplies the geometric enhanced
diagram, without constructing short exact replacement complexes on S'.

This is a decomposition with one upper hole closed and one lower hole added,
not a sorry-free proof of the geometry. The cylinder part is now proved. There
are no sorries in the delivered original module and no hollow definitions.

Edge cases checked: t=0 and zero complexes in the cylinder formula give the usual
split row; t=id has contractible cone and the same formula works; no invertibility
of α or β is assumed. For the geometric statement, empty opens give zero
restriction complexes and repeated opens give the split restriction row. No
nonempty-open hypothesis was introduced.

## No longer needed

Removed the following direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`
- `Sheaf.AlgebraicGeometry.DerivedPullback`
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`

These direct imports are replaced by the two new proof modules. Several notions
remain publicly reachable through RelativeMVMaps. The geometric cone node still
needs the pinned pullback and base-change constructions, the K-injective
presentation, and affine permanence. These were moved below the geometric step;
they are not claimed as wholly pruned from the target closure.

The updated route does not need the triangle-level theorems
lem-pc-derived-mayer-vietoris-triangle (DerivedMayerVietorisTriangle) or
lem-pc-derived-mayer-vietoris-functorial (DerivedMayerVietorisFunctorial): the
remaining statement is explicitly at the enhanced complex/cone level. It also
does not need lem-pc-derived-direct-image-preserves-qcoh
(DerivedDirectImagePreservesQCoh): the desired output has no QCoh assertion about
the resulting base objects. The independent unpinned existence lemma
lem-pc-ringed-spaces-derived-adjoint (DerivedAdjoint) is not needed because the
maps already use pinned adjunctions. No claim is made that these modules are
unreachable from every other target branch.

For completeness, all thirteen old direct proof dependencies are accounted for:
`def-pc-relative-mv-maps` is still needed by the statement. The base-change map,
derived pullback, pullback-composition comparison, right-derived triangulated
functor, affine morphism between affine schemes, and affine permanence nodes
are moved into the geometric cone node's plan. The open-restriction maps node
remains reachable through the public relative-map definitions and the
K-injective presentation. The four theorem nodes no longer used as proof steps
are `lem-pc-derived-mayer-vietoris-triangle`,
`lem-pc-derived-mayer-vietoris-functorial`,
`lem-pc-derived-direct-image-preserves-qcoh`, and
`lem-pc-ringed-spaces-derived-adjoint`. The fifth is
`lem-weil-pbc-qcqs-over-affine`: the K-injective restriction presentation works
for any scheme and cover, so the new enhanced construction does not need this
additional compactness reduction. These are removals from this proof route,
not assertions of global unreachability. In particular DerivedAdjoint is still
publicly imported transitively by SchemeDerivedBaseChangeMap.

The public ShortExact import in each new module was replaced by Basic; no
short-exact-sequence triangle API is needed by either new statement or proof.
The geometric module imports KInjectiveMayerVietorisPresentation,
DerivedDirectImageSplitTriangle, RightDerivedFunctor.Triangulated and Affine
privately, as required by its remaining proof plan.

## Where the brief, the DAG or earlier work was wrong

The original node cited geometric triangle/functoriality declarations, but their
interfaces do not expose the simultaneous relative strict diagram with the
specified global and overlap components. They do not directly prove the node's
mapping-cylinder step. The new split makes that missing enhanced geometric step
explicit and proves the generic cylinder step.

Mathlib has a cylinder object and functorial cones, but the searches found no
single theorem returning this simultaneous short exact presentation. LeanSearch
was unavailable (Internal Server Error), recorded by msearch.py; LeanFinder and
source grep were run. Blueprint searches for mapping cylinder and relative
Mayer returned no matching imported blueprint nodes. No unit or chapter route
was changed; the unit's realized lists are empty and were left unchanged.

The cited Stacks sources were not present under literature/stacks-project on
this machine. Read-only source copies were fetched into this item's scratchpad
for inspection; these are not part of the delivery. Tags 08BV and 08HZ describe
the K-injective restriction rows; 08HY describes the adjunction mate. The new
geometric proof is explicitly a synthesis of these source constructions, not a
claim that Stacks states this exact Lean interface verbatim.

## New nodes

`lem-pc-relative-mv-cone-presentation`:
`lean/Sheaf/AlgebraicGeometry/RelativeMVConePresentation.lean`, theorem
`AlgebraicGeometry.relativeMV_cone_presentation`. This isolates the enhanced
geometric square, six vertex comparisons, and prescribed component identities,
prior to short exact mapping-cylinder replacement.

`lem-pc-cone-diagram-ses-presentation`:
`lean/Sheaf/CategoryTheory/DerivedCategory/ConeDiagramSESPresentation.lean`,
theorem `cone_diagram_ses_presentation`. This is the proved generic cylinder
construction for an arbitrary abelian category, with no scheme assumptions.

Both nodes are under dag/nodes/sec-picard-framework and inherit the original
unit and blueprint ancestry. Updated the original node's proof, proof_deps,
and proof_origin to reflect the actual composition proof. No statement or
interface change record is needed.

## Second reading by G1

1. Compared the delivered original module against the repository with diff and
checked the theorem signature byte for byte. The existing docstring and public
imports are unchanged; only its proof and private proof imports differ. Both
new theorem signatures match their DAG lean.statement fields exactly. No
existing statement, definition, hypothesis or visibility was changed, and no
change record is required. Verdict: pass.

2. Read every private helper in the cylinder construction and the complete
composition proof. The cylinder uses actual biproduct and mapping-cone
constructions, explicit degreewise splittings, the contracting homotopy of the
identity cone, and the functorial cone map. There is no choice of a witness from
an unproved existence theorem. Scanned all delivered Lean files for forbidden
constructs and holes: exactly one sorry remains, in the reported public
relativeMV_cone_presentation theorem, whose proof is exactly by sorry. All three
modules compile cleanly through lcompile.py. A separate scratch module prints
the axioms of all three public theorems; the cylinder theorem uses only the
standard axioms, and the two geometric theorems additionally use sorryAx.
Verdict: pass as a one-for-one decomposition, not a completed geometric proof.

3. Checked the new cone statement against the K-injective presentation and the
Stacks restriction rows and base-change mate construction (08BV, 08HZ, 08HY).
It isolates the strict enhanced geometric diagram before cylinder replacement;
it does not restate the short exact replacement conclusion. The already-proved
algebraic theorem is a genuine additional step. At t=0, its quotient is
A[1] plus B; at t=id, the quotient is contractible; for zero complexes the
formulas reduce to zero maps. The degreewise retraction and section identities
hold in all these cases without requiring alpha or beta invertible. Empty
opens contribute zero and repeated opens give the split restriction row; no
extra geometric hypotheses are hidden in the statement. Independent LeanFinder
queries for degreewise split cone diagrams and enhanced open-cover base change,
Loogle for mappingCone.map, msearch grep, and local rg found only constituent
cone lemmas, a single-map cylinder factorization, and the one-cover K-injective
presentation, not a duplicate of either new result. The remaining geometric
hole is substantial and is not plausibly closable in a few minutes. Verdict:
pass; no further hole closed.

4. Checked the top-down composition and the cylinder's elementary direct route.
The existing single-map cylinder theorem is itself sorry and lacks the
simultaneous row morphism and specified quotient component, so it is inferior
to the complete Mathlib construction here. No shorter complete relative
geometric theorem was found. Completed the report's accounting of every old
proof dependency, including qcqs-over-affine and the distinction between a
removed proof step and a transitively reachable module. The unit
sk-thm-picard-semicon has empty realized statement and step lists; neither its
route nor any unit/chapter record changed. Verdict: pass.

5. Compared all three node records with the declarations and actual proof:
the original composes the geometric cone theorem and the proved cylinder
theorem; the generic cylinder has no project proof dependencies; the remaining
geometric node records its source-based plan and dependencies. New nodes have
the required source, proof steps, dependency unions, ancestry, searches and
verbatim Lean statement records. Added the missing private imports of the
geometric plan rather than leaving those dependencies invisible to the Lean
import closure. Verdict: pass.

Changes made by this reader: reduced the two new public imports from
DerivedCategory.ShortExact to DerivedCategory.Basic; added the four missing
private imports carrying the geometric node's planned proof dependencies;
completed pruning accounting and clarified transitively retained imports in
this report. No proof body, declaration signature or DAG route was rewritten.
