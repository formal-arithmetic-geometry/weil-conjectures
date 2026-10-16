## What changed

`Sheaf.Paper.IntegralResidueComparisons` now proves its original theorem from one
structural projection-normalization theorem. The proof uses the already proved
`Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable` with `hPerfect`,
constructs the target isomorphism using the proved comparison of composite right adjoints,
cancels the normalization isomorphisms, then reflects componentwise isomorphisms through
exact restriction by the derived homology comparison and the conservative module forgetful
functor. Finally it applies `NatIso.isIso_of_isIso_app`.

The actual typed functors, comparison structure, mate definition, and existing counit
proof moved verbatim to `Sheaf.Paper.IntegralResidueComparisonInterface`; the original
module publicly imports it. This makes the new proof dependency acyclic without changing
any existing signature, definition body, visibility, attribute, or target meaning.
`residueExchangeCoefficient` abbreviates the already constructed restricted regular residue
module in degree zero. The new `residueExchangeReductionAdjunction` exposes the actual
proved scalar adjunction. `IntegralResiduePullComparisons.restrictPushIso` is constructed
by transporting composite adjunctions along `c.pull` and applying `rightAdjointUniq`.
The normalization module publicly imports only the generic projection-map definition API,
which its statement mentions. The main module privately imports normalization and
`ProjectionMapDualizable`, used only by its proof. The original rigid-object public import
is attached to the main theorem, whose signature mentions `IsDualizable`, rather than to
the extracted interface. The derived-category braiding API is already available through the
existing public imports; its redundant direct proof import was removed after compilation.

Validation: the interface, normalization statement, main proof, and the unchanged sole
direct importer `Sheaf.Paper.BoundedExchangeAmbient` compile together without warnings.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_comparisons`,
with its statement unchanged. Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_projection_normalization`
(node `new-integral-residue-projection-normalization`). The existing
`IntegralResiduePullComparisons.push_counit` remains proved and unchanged.

This is a decomposition, not a net reduction of holes: one original hole closed and one
structural hole added. The dualizable projection argument, comparison of composite right adjoints, and
conservative-restriction argument are fully proved in Lean. The remaining theorem
assumes only `hTensor`, has no
perfectness hypothesis and no invertibility conclusion. It still needs the coherent
K-flat scalar-pull comparison, strong monoidality of actual derived module pullback,
the source and input-side tensor identifications, and the counit calculation identifying
the specified mate with the projection map. These tasks and the complete proof in words
are recorded in its docstring and node. The scratch file
`scratchpad/IntegralResidueRestrictedTensor.lean` contains a checked natural tensor
identification from the supplied universal property (its printed axioms are only
`propext`, `Classical.choice`, and `Quot.sound`). It is not part of the delivery: the
remaining mate identity needs the comparison compatible with the canonical coefficient
maps. This scratch calculation does not close the full structural normalization theorem.

## No longer needed

No DAG node or module is pruned. The original three public imports remain publicly
available through the main module:
`ContinuousIntegralCoefficients` and `Adjunction.Mates` through the extracted interface,
and `Monoidal.Rigid.Basic` directly at the main theorem. None of the
planned coefficient, coherence, or mate steps is bypassed. The redundant direct import of
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` was removed; this
does not prune that module from the import closure, since the existing interface
dependencies already expose it.
Second reading replaced the normalization module's public import of
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable` by the smaller
`ProjectionMap` module; `ProjectionMapDualizable` is a private proof import of the main
module. It remains in the import closure and is not a pruned module. The rigid-object
public import moved from the interface to the main module without changing old exports.
The flat-change `derivedPullIso` API is not imported as a separate proof dependency and is
not used; its exactness hypothesis is unavailable for quotient extension of scalars.

## Where the brief, the DAG or earlier work was wrong

The plan's perfect-projection invertibility step already exists as a proved generic library
theorem; it no longer needs to remain part of the open coefficient-comparison obligation.
The exact faithful restriction step also follows from existing homology comparisons and
module forgetful functors. The available flat-change comparison API cannot construct the
non-flat residue comparison directly. No statement was weakened or disputed, and the
blueprint unit's route is preserved. The
[paper](https://arxiv.org/html/1309.1198v2) references motivate the construction,
but do not literally state the specialized ambient normalization theorem: Lemma
6.5.9(3) gives the perfect-coefficient projection formula, Proposition 6.8.11(3) concerns
constructibility for finite extensions, and Remark 6.8.15 describes the ambient pullback.
The remaining structural theorem uses the explicit relative-tensor and adjunction
argument given in its docstring; it does not infer arbitrary-scheme or arbitrary-E
claims merely from the more restricted paper statements.

## New nodes

`new-integral-residue-projection-normalization` isolates the structural map identification
from the invertibility argument. Its source is Bhatt--Scholze Lemma 6.5.9(3), Proposition
6.8.11(3), Remark 6.8.15, and the canonical relative tensor and adjunction constructions.
The statement includes explicit source and input-side tensor isomorphisms, uses the
proved restriction/direct-image isomorphism, and states the component map equality.
The original proof node now follows the completed Lean proof. The existing
interface and counit nodes point to the extracted module.

Change record: `coord/changes/integral-residue-comparison-interface-extraction.md`.

## Second reading by B4

1. **Existing statements and data: PASS.** Read all three delivered modules and diffed the
   original module against the shared repository. A byte comparison confirms that the
   entire moved interface declaration block (including the existing counit proof), and
   the signature of `integralResidue_comparisons`, are unchanged. The extraction has its
   change record. Old global names, visibility, attributes, and definition bodies remain
   available through the main module. The new coefficient abbreviation is the explicit
   degree-zero restricted regular module; the two adjunction constructions use actual
   library adjunctions and `rightAdjointUniq`. No arbitrary witness is taken from an
   unproved existence theorem. The sole direct importer, `BoundedExchangeAmbient`, was
   compiled unchanged against the final delivered set.

2. **Proof and axioms: PASS as a decomposition.** Compiled the final three modules through
   `lcompile.py --all`; all pass without source warnings (19.0, 27.3, and 41.9 seconds).
   Inspected the projection-map theorem and the restriction/homology argument: perfectness
   is applied to the coefficient on Y, the normalization equality gives an invertible
   restricted composite, its target isomorphism is cancelled, and the exact homology
   comparison plus conservative module forgetful functor reflects invertibility before
   applying `NatIso.isIso_of_isIso_app`. Scratch copies with 13 explicit `#print axioms`
   commands show only `propext`, `Classical.choice`, and `Quot.sound` for the 11 interface
   declarations, and those three plus `sorryAx` for normalization and the parent theorem.
   One appended scratch command alone triggered a line-length warning; no delivered
   source did. The only delivered `sorry` is the named normalization theorem. There is
   no forbidden declaration or `sorry` in a definition. The report correctly counts one
   closed original hole and one new hole, net zero, rather than claiming a completed
   axiom-free theorem.

3. **Split statement: PASS.** Read the normalization docstring and its matching node.
   It asks for coherent pull comparisons and a structural projection-map identity,
   without perfectness or an invertibility conclusion. It is a strict structural part
   of the original argument; the parent supplies the dualizable projection and
   conservativity argument in Lean. Checked identity morphisms (the identity pull
   comparison and unit tensor comparison give the identity projection), zero complexes,
   and empty schemes; no excluded case or missing geometric hypothesis is needed for
   these tensor/adjunction comparisons. The degree-zero coefficient is actual data.
   The docstring explains the balanced-tensor construction, K-flat derivation,
   composition coherence, tensor identifications, and counit transposition. Read the
   paper's Lemma 6.5.9(3), Proposition 6.8.11(3), and Remark 6.8.15 and clarified their
   precise scope above: the specialized statement uses the recorded formal argument,
   rather than treating the paper as literally stating it. Ran fresh Loogle, Lean Finder,
   and grep searches with different queries; recorded them in the new node. Read
   `ModuleObject.ChangeOfCoefficients`, `MonoidalProjectionConjugate`, and
   `RingedExchangeTensorCoherence`: none supplies this exact normalization. In particular,
   the available derived scalar-pull comparison assumes exact extension of scalars.
   The whole normalization cannot be closed by a short application of those APIs.

4. **Route and pruning: PASS after import repair.** The main proof takes the existing
   generic dualizable projection theorem and exact homology comparison. The normalization
   preserves the remaining scalar-pull coherence and specified-mate identification.
   Read `dag/units/sk-thm-properbasechange.json`: its statement and all three realized
   steps are unchanged and none is bypassed. Both old proof dependencies remain used;
   `## No longer needed` therefore correctly lists no pruned node or module. Replaced
   normalization's public `ProjectionMapDualizable` import with the smaller public
   `ProjectionMap` definition API; added `ProjectionMapDualizable` as a private proof
   import of the main module. Moved the original public rigid-object import to the main
   theorem, whose signature needs it, preserving the original exports.

5. **Nodes: PASS.** All four delivered node files were read with their Lean declarations.
   Every `proof_deps` list equals the union of the proof steps' `uses`; every dependency
   exists. The parent node describes precisely the implemented projection cancellation
   and homology reflection. The interface node records the concrete composite-adjunction
   construction, and the counit node now points to its extracted module. The new node has
   the required source, complete proof steps, search records, creation and blueprint
   metadata, chapter/unit, and an exact byte match to the Lean theorem signature.
   Existing node edits are confined to `lean`, `proof`, `proof_deps`, and `proof_origin`.

Second reading changed the import layout described in point 4, updated its change record
and report, clarified the source claims and honest decomposition count, and recorded
independent searches. No existing signature, definition body, or proof argument was changed.
