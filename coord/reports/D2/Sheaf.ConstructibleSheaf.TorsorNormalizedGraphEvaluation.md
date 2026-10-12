## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.ordinaryGraphEvaluation_bijective` with its
signature unchanged. Added a proved private `constantCoordinates_localRestriction` helper
in the same module. It combines the existing inverse-image/localization comparison with
the source library's constant abelian sheaf/continuous-function comparison, after forgetting
module scalars. Connectedness identifies the coefficients with F(c.P); open fibres provide
the local restriction formula. The main proof uses two explicit pullback graph identities,
naturality, and diagonal normalization to identify graph evaluation with the coordinate
equivalence. Empty W and zero coefficients are covered by the same proof.

Added only proof imports:
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`

Removed the redundant plain import `Sheaf.ConstructibleSheaf.TorsorAssociatedModule`;
`TorsorSectionRepresentation` already publicly imports it.
The public imports and all existing signatures and visibility are unchanged. The node's
proof now records the implemented steps and the inverse-image/restriction comparison.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.GaloisCover.ordinaryGraphEvaluation_bijective`.
Added 0 holes; no `sorry` remains in this module and no new module is delivered.
The private coordinate lemma is fully proved. This is a proof, not a decomposition.

The module compiles cleanly with `lcompile.py`; the delivery dry run checks it with the
project's axiom probe. Existing imported obligations remain in the library unchanged.

## No longer needed

Removed the redundant direct proof import `Sheaf.ConstructibleSheaf.TorsorAssociatedModule`.
Its module remains transitively imported, and its section-space and restriction definitions
are used, so its node remains a proof dependency. No nodes or modules were pruned. The proof
uses no equivariance or torsor graph-splitting lemmas, and does not import
`Sheaf.ConstructibleSheaf.TorsorGraphEvaluation`,
`Sheaf.ConstructibleSheaf.TorsorDiagonalEvaluationBijective`, or the separate module-valued
comparison `Sheaf.ConstructibleSheaf.ConstantModuleLocallyConstant`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan is implemented. The constant-sheaf coordinate
step can be discharged with the existing abelian continuous-function comparison after
forgetting scalars; no new module-valued comparison or geometric obligation is needed.
Mathlib searches found connected locally constant functions are constant; the relevant
scheme-specific comparison is already proved in the source library. The proof takes the
same restriction/forgetting comparison used in `TorsorOrdinaryEvaluation`.

## Second reading by D2

1. PASS: compared the complete delivered Lean module and node with the repository.
   The existing public theorem signature is byte-for-byte identical; its docstring,
   visibility, file options, and public imports are unchanged. No definition or target
   statement changed. Only the proof, a proved private helper, proof imports, and the
   permitted node proof fields changed.
2. PASS: compiled the module with `lcompile.py` without errors or warnings. A scratch
   copy with `#print axioms` for both the public theorem and the private helper reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There are no sorries, forbidden declarations, or hollow definitions. The selected
   trivialization is an input hypothesis used inside a proof, not arbitrary data
   chosen by a definition from an unproved existence theorem.
3. PASS: no statement was split off and no new public statement was added. Read the
   private coordinate helper in full: localization and the discrete continuous-function
   comparison give the equivalence; naturality on an open fibre proves the restriction
   identity. Empty W makes the pointwise clause vacuous, zero coefficients give unique
   sections, and the identity torsor uses the same graph identities. Searched the
   library for graph evaluation, constant coordinates, and local restrictions, and
   independently queried Loogle with `LocallyConstant, ConnectedSpace` (zero hits).
   The upstream constant-sheaf comparison is already used; ordinary evaluation's
   existence theorem does not supply the bijectivity or local-restriction statement.
4. PASS: read the proof from graph evaluation down to constant coordinates. It uses
   the already proved upstream comparison and connectedness lemma, adds no holes, and
   invokes no equivariant extension or graph splitting. Both new plain imports are
   needed by the comparison. The removed direct associated-module import is redundant
   via the public section-representation import. Every old proof dependency remains
   used; none is pruned. Read `dag/units/sk-thm-p1.json`, including `realized`: this
   local torsor tool changes no realized unit statement or step and keeps the planned
   two-step constant-coordinate/diagonal-normalization route.
5. PASS: the node's proof describes the actual coordinate helper and pullback graph
   identities. Its proof dependencies are exactly the union of the steps' uses,
   including the inverse-image/localization comparison. Its Lean declaration and
   recorded signature agree with the module; proof origin records the implemented
   route. No new nodes are required for an entirely proved private proof helper.

Second reading changed only this report: recorded the redundant removed proof import
in What changed and No longer needed, and appended the independent checks above.
The Lean proof and node metadata needed no repair. Closed one existing hole, added
zero holes, split off zero statements, and pruned no modules.
