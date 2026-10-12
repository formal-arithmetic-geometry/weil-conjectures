## What changed

Completed the earlier sandbox reduction in
`Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite`. The signature and existing
docstrings are unchanged. The proof defines the multiplication maps using homogeneous Rees
monomials, proves their section formula and degree-zero scalar action, applies
`AlgebraicGeometry.gradedFinitenessCohomology`, and distributes the action across the two
finite support decompositions to obtain the exact convolution formula.

Added `Sheaf.AlgebraicGeometry.IdealPowersReesGradedData` for the sheaf-level input to that
application, and `Sheaf.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism` for the scalar
compatibility of derived module cohomology. The latter is proved using a scalar chain map on
an injective resolution, resolution naturality and `ShortComplex.homologyMap_smul`.
The scalar endomorphisms are explicit linear maps, not data chosen from an unproved theorem.
All proof-only imports in the item remain nonpublic. No existing interface or other holder's
module is changed. No change record or forced adaptation is needed.

All three modules compiled together via `lcompile.py --all`, without errors or non-sorry
warnings. The literature was read in the locally available Stacks snapshot at
`/home/ubuntu/c1-stacks-review/coherent.tex` (5330--5400) and `cohomology.tex` (the
ringed-space module paragraph of section-cohomology-sheaves). The canonical source paths
remain those already used by the project. LeanSearch returned HTTP 500 and is recorded as
unavailable; LeanFinder and source grep found related algebraic and homology lemmas, but no
existing statement supplying the full graded sheaf data.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.cohomology_powers_ideal_rees_finite`
(node `lem-weil-pbc-cohomology-powers-ideal-rees-finite`). Its proof contains no sorry.

Also proved the new theorem
`AlgebraicGeometry.moduleCohomology_scalar_endomorphism`
(node `lem-weil-pbc-module-cohomology-scalar-endomorphism`), including both private helpers.

Added one hole, exactly the whole public theorem proof:
`AlgebraicGeometry.idealPowersReesGradedData`
(node `lem-weil-pbc-ideal-powers-rees-graded-data`). It supplies only the sheaf-level
action, quasi-coherence and local generators; it has no cohomology or finite Rees-module
conclusion. Its maps are uniquely determined by the displayed section formula under the
monomorphic inclusions into F. The main theorem genuinely combines this input with the
existing graded finiteness theorem and the proved scalar helper.

This is a decomposition: one old hole closed and one new hole added, net zero before
closure pruning. The existing imported theorem `gradedFinitenessCohomology` remains open
in the library and is used as the stage-3 brief intends. No hollow definition was added.
Edge cases checked for the new statements: empty scheme, zero module, zero and unit ideals,
zeroth powers and q = 0. For I = 0, only the positive powers vanish; G_0 still needs F's
local generators. The scalar theorem needs no coherence or properness hypotheses.

## No longer needed

Removed six direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.Coherent` (node `pqf-def-coherent`): its definition is already
  available through the public statement imports; finite local generators are part of the
  new graded-data subproblem.
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
  (node `pqf-lem-coherent-ft-locnoeth`): moved to the new graded-data node's proof plan.
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`
  (node `lem-weil-pbc-module-pullback-ideal-quotient`): moved to that sheaf-level proof plan.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
  (node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`): moved to that proof plan.
- `Sheaf.Paper.PQFCohomology` (node `pqf-def-cohomology`): available through
  `GradedFinitenessCohomology`; the item uses the explicit module-cohomology interface.
- `WeilConjectures.Blowup.Affine.Proper`: blow-up properness
  (`lemma-nagata-affine-blowup-proper`) and finite type over the Rees degree-zero component
  are unnecessary here. Mathlib's Rees-algebra finite-type instance over A suffices.

The first four nodes are still needed below the new graded-data node, so this report does
not claim they have been eliminated from the full mathematical argument. In the item's
updated proof_deps, the old local-Noetherian, finite-type-over-Noetherian, affine-section,
ideal-product, coherence, and affine-basis setup is encapsulated in that node. The
base-ring, properness, ideal-product and cohomology definitions remain statement dependencies.
No unit statement or realized unit proof step has been bypassed. Whether a removed direct
import becomes unreachable from all targets is for the maintainer's closure computation.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had not compiled its scalar helper and had no new-node records or
report. The helper's section formulas mixed ring-valued module scalars with the scheme's
commutative-ring presheaf. Keeping the scalar construction in `moduleRings` and unfolding
`SheafedSpace.sheaf` at the comparison closes this issue. The main reduction then compiled
unchanged. The earlier new docstring incorrectly grouped the zero ideal with cases needing
no generators; its zeroth degree remains F, and the corrected docstring says so.

The original node's last step treated scalar compatibility as a convention. The actual
moduleCohomology is a derived functor, so the supplied helper proves that compatibility.
There is no disputed statement, signature correction or change to a target. The updated
node records the exact proof route rather than claiming that the affine setup was already
formalized in the item's proof.

## New nodes

`lem-weil-pbc-ideal-powers-rees-graded-data`, in
`dag/nodes/sec-proper-base-change/`, records steps 1 and 3 of the original plan as the
strictly smaller sheaf-level input in `IdealPowersReesGradedData.lean`. Its statement is
self-contained, its proof follows Stacks 02O8 and cites the existing affine-section and
coherence nodes, and the Lean docstring carries the complete construction and edge cases.

`lem-weil-pbc-module-cohomology-scalar-endomorphism`, in the same chapter, records the
proved injective-resolution argument in `ModuleCohomologyScalarEndomorphism.lean`, using
Stacks 01DZ. Both nodes have their exact Lean signatures and three actual kinds of search,
with the unavailable LeanSearch service recorded honestly. Neither depends on the item.


## Second reading by J3

1. Compared the delivered item module with the repository version. The theorem signature and existing
   declarations are byte-for-byte unchanged; only proof text and proof-only imports changed. The two
   added modules and node records are new delivery-owned declarations.

2. Compiled all three modules together with `lcompile.py --all`; compilation succeeded without errors
   or warnings. The scalar endomorphism theorem has only `propext`, `Classical.choice`, and
   `Quot.sound` in its axiom report. The remaining `sorryAx` occurs only through the explicitly split
   graded-data theorem and the existing graded finiteness theorem it invokes; no definition contains
   `sorry`, and no forbidden declaration was added.

3. Checked the two new statements against their docstrings, source citations, and edge cases. The
   graded-data theorem is strictly smaller than the item: it supplies sheaf maps, quasi-coherence,
   compatibility, and local generators, while leaving cohomological finiteness to the existing node.
   The scalar theorem is a genuine derived-functor compatibility result, not a restatement of the
   item. Searches found no existing declaration with either statement.

4. The proof follows the shortest available route below the unit: the item invokes the graded-data
   reduction, the scalar derived-functor lemma, and `gradedFinitenessCohomology`, then expands finite
   support sums. The removed direct imports are not used by the item proof. The old proof-dependency
   nodes no longer used directly are `pqf-def-locnoeth`,
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`, `def-weil-proper-morphism`,
   `lem-weil-pbc-finite-type-over-noetherian`, `pqf-lem-coherent-ft-locnoeth`,
   `lem-weil-pbc-spec-module-tilde-sections`, `lem-weil-pbc-module-pullback-ideal-quotient`,
   `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, `def-weil-pbc-coherent-formal-module`,
   `def-pc-scheme`, `def-nagata-rees-algebra`, `def-weil-pbc-noetherian-ring`,
   `def-weil-pbc-finite-type-algebra`, `pqf-def-coherent`, and `pqf-def-cohomology`.
   Their mathematical work is encapsulated in the split graded-data node or remains a statement
   dependency. The unit's realized route is unchanged.

5. The delivered DAG proof steps and `proof_deps` agree with the Lean proof: the item node uses the
   two new nodes, the Rees grading/finiteness nodes, and the graded cohomology node; each new node's
   dependency set is exactly the union of its proof-step uses. No target statement or unit record was
   changed.

I changed only this second-reading report section and removed temporary axiom-probe files; no Lean
proof or node statement required repair.
