## What changed

Proved the assembly of pbcDescentOperations from finite-stage operations. Constructed
the actual direct-image family through ambient restriction and rational localization,
including its coefficient coherence and BetaSpec. Proved normalized exactness at
every direct-image stage and packaged the family exact structures. Constructed
the localized natural exchange and reduced its compatibility to the scalar square.
The item applies each family result twice, applies the already proved
pbcDescentFunctors four times, constructs the exchange by descNatTrans conjugated
by functorCompIso, and proves its displayed component formula because both
composition isomorphisms have identity components.

Moved five existing interface declarations verbatim to PbcDescentInterfaces and
publicly re-exported them from the original module. This avoids an import cycle;
it changes neither a definition's value nor any existing theorem statement.
The change record is coord/changes/pbc-descent-finite-stage-inputs.md.

## Proved and sorry left

The existing general theorem AlgebraicGeometry.Scheme.pbcDescentFunctors remains
proved. All nine sandbox modules compile together through lcompile.py --all (exit 0).
The original hole AlgebraicGeometry.Scheme.pbcDescentOperations is closed
by a complete Lean assembly proof. The direct-image and exchange constructions
are also proved from the narrower statements below: pbcDirectImageCoherentFamily,
pbcDirectImageFamilyShiftCompatible, pbcDirectImageFamilyExact and
pbcExchangeCompatibleFamily have complete proofs. The unique normalized stage
shift and its exactness are proved in pbcDirectImageStageShift_exists.
This is a decomposition, not a complete proof of the operation application:
one upper hole closed and two lower holes added, net minus one hole.

The remaining newly added sorry declarations are:

- AlgebraicGeometry.Scheme.pbcPullbackCoherentFamily, node
  lem-weil-pbc-pullback-coherent-family.
- AlgebraicGeometry.Scheme.pbcExchangeStageSquare, node
  lem-weil-pbc-exchange-stage-square.

Each is exactly a public named theorem with a whole-proof sorry and a source and
complete proof in words. There is no sorry in a definition. The completed
direct-image scalar-shift proof uses the fixed normalized stage shifts. The remaining
pullback statement has one map and makes no common-stage or Cartesian-square
assertion. The exchange square assumes four families and the actual natural stage
transformations; it asserts only their scalar compatibility. They are strictly distinct
parts of the source argument, rather than a renamed copy of the original theorem.

## No longer needed

Removed the redundant direct proof imports PbcRationalTransport,
FiniteStagePairCategory, CommonStageCalculus, PbcCommonStageCones and
PbcVerdierAxioms: their required public declarations are already exposed through
the retained public PbcQbarCategory/PbcScalarExtension imports. Removed the direct
IntrinsicQbarCategory import: the proof uses the recorded existing pair category
and requires no extra scalar-action interface from that module. These are direct
import removals, not claims that no other target consumer needs those modules.

The retained general Lean proof uses the already proved native StageSystem.Morphism
API directly. It does not need lem-sbc-coherent-pair-functor-descent or its separate
Sheaf.CategoryTheory.StageSystemFunctorDescent interface. Its explicit private shift
construction does not need lem-weil-pbc-pair-functor-shift-coherence or
Sheaf.Paper.PbcPairFunctorShiftCoherence. Its single-triangle stage argument uses the
Verdier characterization, and does not need lem-weil-pbc-distinguished-diagram-lifting
or Sheaf.Paper.PbcDistinguishedDiagramLifting, which concern arbitrary finite diagrams.
These three parent proof edges and the tool-use approval
lem-sbc-coherent-pair-functor-descent are removed.
The general Mathlib triangulated-category notions need no extra proof edges to the
unattached def-weil-triangulated-category and def-weil-pbc-triangles-with-shift nodes.
Other consumers may still need any of these nodes; no source declaration is removed.

Rational transport, scalar extension, the common-stage calculus, common-stage cones,
the Qbar category and the Verdier axioms remain needed, directly or in the new inputs.
The unit's own statement and steps stay. The five moved interface declarations are
not pruned or replaced. The direct-image proof needs its private conjugation,
full-subcategory, localization and tower-coherence helpers.

## Where the brief, the DAG or earlier work was wrong

The supplied file's general exact descent was already proved. Its remaining hole
also required constructing the normalized concrete families and proving exchange
compatibility; the generic theorem alone could not supply those inputs. The DAG's
final proof step grouped those separate finite-stage arguments with their descent.
The new nodes make the missing inputs explicit without changing the unit route.

The small-field inclusion composition is not reflexivity: one must cancel the
intermediate Shrink equivalence. Rewriting a coefficient map under a dependent
associator also requires transporting its composition proof, rather than an ordinary
rewrite with an ill-typed motive. These are normalization tasks in the finite-stage
inputs, not failures of the source statements. The localization comparison and the
completed direct-image family use irreducible private definitions with component
lemmas, preventing expensive unfolding during later normalization checks.
The assembly's BetaSpec hypotheses
need explicit type annotations to preserve their implicit field quantification.

## New nodes

lem-weil-pbc-direct-image-coherent-family constructs the actual single-map rational
direct-image family with coherent scalar comparisons and BetaSpec, and applies the
separate exact-family packaging theorem. Its construction is proved.

lem-weil-pbc-direct-image-stage-exact proves existence and uniqueness of the exact
shift normalized by the actual integral localization square. Its definitions choose
only the uniquely determined shift, using a proved existence-and-uniqueness theorem.

lem-weil-pbc-direct-image-family-shift-compatible proves that the normalized scalar beta maps commute with these fixed stage shifts.
It identifies both ambient shift conventions by adjunction-unit uniqueness,
reflects through full subcategories, and reflects through rational localization. Its
endpoint-identification definition is an explicit equality transport.

lem-weil-pbc-direct-image-family-exact packages the normalized stage shifts,
triangulatedness, additivity and the separate comparison equation on a given base
family; its Lean proof is complete.

lem-weil-pbc-pullback-coherent-family isolates the actual completed pullback family,
preserving the inverse orientation in the scalar normalization.

lem-weil-pbc-exchange-compatible-family constructs the localized actual natural
exchange for given families and uses the separate stage scalar square to package
its compatibility. Its construction is proved.

lem-weil-pbc-exchange-stage-square isolates the scalar equation for given canonical
localized stage transformations. It constructs no transformation or exact family.

def-weil-pbc-descent-interfaces attaches the three moved coherent-family and
pullback interface definitions. The existing direct-image definition node retains
its two attachments at their new location. No duplicate operation is defined.

Change record: coord/changes/pbc-descent-finite-stage-inputs.md.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
