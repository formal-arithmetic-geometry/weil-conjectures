## What changed

Fill two existing proof holes in `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
All existing public declaration signatures and definition bodies are preserved.
The scalar-stage portion is moved verbatim, except for the two completed proofs and
private proof helpers, into `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`.
The item public-imports that supporting module, preserving every original public name.
Its proof-only `SfIntegralConstructibleTriangulated` import moves with the stage proofs.

`transitionCommShift_existsUnique` transports the retained finite-field normalization
and uniqueness theorem. A private, concrete datum has base field `ZMod p`, where
`p > l` is prime. Parameter independence identifies the integral and rational functors;
integral normalization uniqueness identifies their shift comparisons. These equalities
identify the two predicates at shift one, so equality transport gives existence and
uniqueness of the required coherent integer-shift datum. This adds no condition on `Y`.

`transitionExact` transports the retained finite-field exactness theorem along the
rational functor equality and the equality of its prescribed CommShift structures.
The existing `specialization_transition` and `specialization_transitionShift` lemmas
are moved earlier, with their signatures and proofs preserved, to support this argument.
All new helpers are private and proved. Their concrete finite-field datum is a real
construction. Local unfolding of the small category record and local opacity of scalar
composition keep the supporting comparison proofs within the existing cache interface.
The owning DAG node records these arguments. The existing specialization additivity
proof is factored through a proved private lemma for equivalences of preadditive
categories; preservation of zero morphisms is supplied explicitly. No existing instance
attribute or public declaration interface changes. The equivalence definition is locally opaque
while its final instances are registered, to avoid expanding equality transport.

## Proved and sorry left

Closed 2 of the original 9 holes (namespace
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients`):

- `transitionCommShift_existsUnique`.
- `transitionExact`.

Added holes: none. Split-off holes: none. The following seven existing named theorem
holes remain unchanged. The cocycle is relocated with the scalar stages and attached
to `lem-general-algebraically-closed-coefficient-stages`; the six other obligations
remain in the item and its original node:

- `associator_cocycle`.
- `shift_existsUnique`.
- `transitionIso_commShift`.
- `specialization_comparisons`.
- `specialization_homCoordinates`.
- `specialization_commShift_existsUnique`.
- `specialization_distinguished`.

The two transition proofs use the already stated finite-field theorems, whose existing
holes remain in `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`; no new obligation is
introduced or hidden inside a definition. The auxiliary datum is constructed from
`ZMod p` and its algebraic closure, rather than selected from an unproved existence
statement. Its use in the proof of the uniquely specified shift adds no arbitrary
choice to the public normalization.

## No longer needed

No mathematical nodes, modules, public declarations or unit steps are pruned.
The proof-only `SfIntegralConstructibleTriangulated` import is removed from the item
and retained in the supporting scalar-stage module, where its proof is used.
Direct scalar-stage dependencies move to the subordinate node and remain required.
The direct rational shift-construction argument is not needed again for the general
interface: the retained finite-field normalization theorem supplies it. That theorem
and its dependencies remain needed. The other declared dependencies still serve the
retained constructions and seven remaining obligations.

## Where the brief, the DAG or earlier work was wrong

The item was absent initially because of the quarantine recorded in `coord/rework.tsv`.
Its archive was read and preserved; the shared source subsequently reappeared unchanged.
The delivery updates that source and does not withdraw the module.

No statement defect or mathematical counterexample was found. The existing
finite-field interface applies to the same intrinsic stages for arbitrary `Y`, with
the characteristic parameter used only in preservation proofs. This gives the shorter
route to the normalized transition shift and its exactness. An existential exact shift
alone would not establish these normalized statements.

The current blueprint snapshot does not contain the old item path named in the module
and node; the existing source records are preserved. No shared definition or global
reducibility setting is changed. A declaration-local unused-variable linter option
preserves the public normalized-shift theorem’s original instance-binder name; the
corresponding new private binder uses an underscore name.

## New nodes

`lem-general-algebraically-closed-coefficient-stages` records the existing scalar-stage
part of the argument in the supporting module. It is strictly below the original
common-stage category: it supplies the finite stages, normalized transitions, tensor
associators and uniquely specified StageSystem, without forming the pair category,
Hom colimits, shifts or Verdier structure. Its single hole is the relocated existing
`associator_cocycle`, not an added obligation. The two newly completed transition
proofs live here. Profiling and local reduction controls preceded this split; the
combined file still exceeded 60 seconds in delivery checks. The change record is
`coord/changes/W2-general-coefficient-stages.md`.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
