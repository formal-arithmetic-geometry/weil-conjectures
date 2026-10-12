## What changed

Replaced the sorry in `AlgebraicGeometry.gradedCohomologyModuleFinite_generators`
with a complete cohomology argument from geometric realization and existing library
statements. Existing public signatures and visibility are unchanged, including the
already proved `gradedCohomologyModuleFinite` wrapper.

The new module `Sheaf.Paper.GradedModuleRelativeSpecRealization` states only the
geometric step: a quasi-coherent finitely presented module F on the explicit
base change Y, coproduct inclusions into pi_*F, and their homogeneous action
squares. It has no cohomology degree, supplied cohomology action, finite
cohomology assertion, or finite spanning-set assertion. Its one theorem is
strictly part of the original relative-spectrum argument.

A proved private helper `finite_moduleCohomology` transfers proper coherent
higher-direct-image finiteness to module right-derived cohomology. It uses the
existing natural source comparison and scalar endomorphism theorem; it introduces
no new cohomology definition. The main proof composes the direct-sum comparison
with the affine edge map, proves homogeneous compatibility using source and target
naturality and the geometric square, and performs two direct-sum inductions to
prove B-linearity for exactly the supplied `mod`. A linear equivalence transports
finiteness and gives the requested FG top submodule.

All new imports needed only by proofs are non-public. No definitions, intermediate
signatures, target signatures, or other modules are adapted. The realization's
existential witness is eliminated inside a proposition proof; no definition chooses
arbitrary data from an unproved existence statement.

Read the pinned Stacks `coherent.tex`, label `lemma-graded-finiteness`, Tag 0897,
lines 5247--5300 (downloaded into the sandbox scratchpad because literature is not
checked out on this machine), and checked its published Tag 0897 page. The new
geometric statement is the construction paragraph before the cohomology comparison.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.gradedCohomologyModuleFinite_generators`
(node `lem-weil-pbc-graded-cohomology-module-finite-generators`).
The item's module now has zero sorries. The previously proved
`AlgebraicGeometry.gradedCohomologyModuleFinite` is retained.

Added one named hole:
`AlgebraicGeometry.gradedModule_relativeSpec_realization`
(node `lem-weil-pbc-graded-module-relative-spec-realization`), in its new module,
with proof exactly `:= by sorry` and a complete natural-language construction.
This is a decomposition: one hole closed and one geometric hole added, net zero.
The new hole concerns sheaf realization only; the full cohomology combination is
proved in Lean. Existing imported theorems may still depend on their own sorries;
those are unchanged.

Both modules compile through lcompile.py. The original module's proof also compiled
individually against the sandbox overlay without warnings. The dry run performs the
final set compilation, axiom probe and preflight.

## No longer needed

Removed these direct proof imports from the item and placed them in the realization
module because they belong to its geometric proof:
`Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`,
`Sheaf.AlgebraicGeometry.AffineModuleFiniteType`,
`Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, and
`Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`.
Their nodes remain needed by the new geometric item; none is claimed pruned.

Removed the direct import `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` in favor of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`. Its definitions remain
needed and imported transitively. No dependency module or node is eliminated from
the targets' closure. Pruned modules: none.

Removed DAG dependencies, accounted for explicitly: the generator node no longer
uses `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-relative-spec-base-change`,
`lem-weil-pbc-affine-morphism-relative-spec`,
`lem-weil-pbc-affine-module-correspondence`,
`lem-weil-pbc-affine-module-finite-type`, or `pqf-lem-coherent-ft-locnoeth`
directly; each is retained in the realization node's proof dependencies.
The wrapper node now uses only the generator node. Its former direct dependencies
are all retained below the generator/realization or as statement dependencies:
`lem-weil-pbc-proper-fp-permanence`,
`lem-weil-pbc-finite-type-algebra-noetherian`, `def-weil-proper-morphism`,
`lem-weil-pbc-finite-type-over-noetherian`, `pqf-def-coherent`,
`def-weil-pbc-finite-type-algebra`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-relative-spec-base-change`,
`lem-weil-pbc-affine-morphism-relative-spec`,
`lem-weil-pbc-affine-module-correspondence`,
`lem-weil-pbc-affine-module-finite-type`, `pqf-lem-coherent-ft-locnoeth`,
`lem-pc-coherent-hi`, `lem-weil-pbc-affine-morphism-cohomology-edge`,
`def-weil-pbc-module-cohomology-fmap`,
`lem-weil-pbc-qcqs-cohomology-direct-sum`, `pqf-def-cohomology`,
and `def-weil-finitely-generated-module`. No removed direct edge is claimed as
closure pruning.

## Where the brief, the DAG or earlier work was wrong

The previous generator node compressed the entire construction and cohomology
comparison into one proof step. The existing affine correspondence takes an
already constructed module over the pushed-forward algebra sheaf; it does not
construct that module from the homogeneous mu maps and hfinite condition. The new
realization theorem exposes precisely this remaining construction and gives the
multiplication squares needed downstream.

The proper coherent finiteness declaration uses higher direct image sections and
the source library's ordinary H, whereas the item's statement uses module-valued
right-derived sections. A direct application does not typecheck. The private
helper resolves this using existing source-comparison and scalar-endomorphism
statements. Edge-map B-linearity is proved rather than asserted or split off.

The new statement was checked on the empty scheme, zero modules, zero coefficient
ring, degree-zero actions, and empty local generator families. Empty families force
local homogeneous sections to vanish. Scalar a = 1 supplies the unit law despite
the degree-zero target being presented as G(m+0). Finite type over the Noetherian
base makes B Noetherian, and proper base change makes Y locally Noetherian, so
finite presentation is valid. No cohomology finiteness is assumed in this step.
The unit sk-thm-p1 realized nodes are untouched.

Searches: LeanFinder found presentation infrastructure only; Loogle found
`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`; grep found no relative
spectrum module realization. LeanSearch returned HTTP Internal Server Error and
is recorded as unavailable, not as a negative search result. The blueprint search
found no matching realization statement; existing affine correspondence, affine
finite-type and relative-spectrum nodes are cited rather than restated.

## New nodes

`lem-weil-pbc-graded-module-relative-spec-realization`:
`lean/Sheaf/Paper/GradedModuleRelativeSpecRealization.lean`, declaration
`AlgebraicGeometry.gradedModule_relativeSpec_realization`. It states the geometric
construction, finite presentation, coproduct universal property and homogeneous
multiplication squares, with no cohomology conclusion. The node carries the source,
three kinds of recorded search (plus the failed LeanSearch), and the local algebra,
relative spectrum, affine correspondence and finite-presentation proof steps.
The existing generator node is updated to match the complete Lean cohomology proof;
the wrapper node now records its actual FG-top-to-Module.Finite argument.
No change record is needed because no existing interface changed.

## Second reading by R1

1. Unchanged interfaces: PASS. Diffed both delivered modules against the repository
   (the realization module is new). Extracted the two existing theorem signatures
   through `:= by` and checked byte-for-byte equality. The wrapper's proof is
   unchanged. Existing nodes change only proof, proof_deps and proof_origin. No
   definition, target, existing signature, visibility or other module is changed.
2. Proof and axioms: PASS. Compiled both files in import order with lcompile.py,
   without errors or warnings (4.1 and 14.2 seconds). Independently compiled scratch
   copies with `#print axioms` for the realization, private finiteness helper,
   generator theorem and wrapper. Each uses only propext, Classical.choice,
   Quot.sound and sorryAx from the declared open dependencies. Scanned for forbidden
   declarations and mechanisms: none. The sole new sorry is the public realization
   theorem with proof exactly `:= by sorry`; there are no definitions or hidden
   holes. The existential realization is eliminated inside a proposition proof,
   not used to define arbitrarily chosen data.
3. Split statement: PASS. Matched the new node's Lean signature verbatim, read its
   construction docstring and the pinned coherent.tex paragraph. The statement
   omits cohomology, cohomology actions and cohomology finiteness, and is strictly the
   geometric part of the original argument. Additivity implies the zero action;
   the scalar condition at a=1 supplies the unit; multiplicativity and O_X-linearity
   give the tensor-algebra action. Local generation is sufficient on stalks, and
   finite type over the Noetherian base makes finite presentation valid. Checked
   empty X, zero G, zero B, concentrated degree-zero grading, and r=0: none requires
   a nonzero object or nonempty generating family. Independent LeanFinder search
   for a quasi-coherent module over a graded algebra realized on a base change
   found tilde/presentation infrastructure only. Loogle query
   `SheafOfModules.IsQuasicoherent, CategoryTheory.Limits.IsColimit` found no match;
   an earlier unqualified IsColimit query was invalid and not counted as evidence.
   msearch grep for tensor/sheaf and affine equivalence/module found infrastructure
   only. Repository rg additionally found Proj-specific graded sheaf constructions,
   not this affine realization. Closing the geometric construction is substantial
   new work, not a few-minute application of an existing result.
4. Route, imports and pruning: PASS. Read the affine correspondence, finite-type,
   affine edge, source comparison, scalar endomorphism and direct-sum declarations.
   The private helper resolves the different cohomology models; an existing private
   analogue in FormalFunctionsCompleteBase is inaccessible and takes a different
   coherent-module input. The main proof applies the actual geometric and
   cohomological comparison declarations, proves edge naturality for homogeneous
   multiplication, and extends compatibility to the given mod by two direct-sum
   inductions. This is a real reduction, not a renamed finite-generation assertion.
   Public imports of the new module supply its signature, including smulHom from
   Cohomology.Defs and moduleRings from DerivedHomMayerVietoris; its plain imports
   retain the open geometric proof plan. No unit-level route is bypassed: checked
   sk-thm-p1.realized, whose statement and all four step lists are untouched. The
   report now explicitly accounts for every removed old proof dependency. None is
   claimed pruned from the closure. This remains one hole closed and one added,
   net zero, and is reported as a decomposition.
5. DAG agreement: PASS. Checked all three nodes, their proof-step uses unions equal
   proof_deps, every dependency has a Lean declaration or Mathlib match, the new
   node's source/creation/blueprint/chapter/unit/Lean/search records, and the exact
   new signature. The generator node follows the Lean realization, finiteness
   comparison, naturality and linear-equivalence transport; the wrapper node
   follows its FG-top surjection proof. Removed pqf-def-cohomology and
   def-weil-finitely-generated-module from the new node's stmt_deps because its
   geometric statement mentions neither cohomology nor finite cohomology modules.

Second-reading changes: no Lean edits; removed two unrelated new-node statement
edges, completed the No longer needed dependency accounting, and added this review.
