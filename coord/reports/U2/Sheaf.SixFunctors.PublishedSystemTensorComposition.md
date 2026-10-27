## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.AmbientProperOpen.publishedSystemTensorComposition`
by transport of `AmbientPullbackTensor.ambientPullbackTensorCoherence` on the sequence site,
using the actual `systemClosed` and `systemTensorModel` data. The proved categorical theorem
`TensorComparisonTransport.transfer_tensor_composition` supplies the transport argument using
naturality and cancellation of invertible compositors. It works for arbitrary bifunctors and
requires no extra monoidal structure. The proved specialization
`publishedSystemAmbientCoherence` obtains the characteristic inequality from the finite-field
cardinality and instantiates the final ambient sequence-site equation. The item statement,
targets, and existing definitions are unchanged.

The actual ambient constructions are recorded in `PublishedSystemAmbientData`, whose fields
have the published sequence-category types. Its pullback identification is proved from
`sequence_derived_eq`, and the specified isomorphism is its `eqToIso`. The record introduces
no new witnesses or choices. The compositor identification binds the given compositor with
the same published functor types. The application passes the derived-category instance
constructors directly and supplies the data without local aliases. These type choices avoid
expanding large localization constructions when the kernel compares presentation aliases.

The two identifications missing from the old plan have their own modules and nodes. One concerns
a tensor comparison for one morphism; the other concerns a compositor without tensor products.
The final equation is proved from these identifications and the existing ambient theorem, rather
than left inside another proof hole. No existing module besides the item is changed. The assembled theorem compiled in 3.8 seconds;
all six modules then compiled successfully together with `lcompile.py --all`.

## Proved and sorry left

The original hole in `AlgebraicGeometry.ProEtale.AmbientProperOpen.publishedSystemTensorComposition`
is replaced by a complete Lean argument from the two identification statements.
`transfer_tensor_composition` and `publishedSystemAmbientCoherence` have complete proofs.

Two new holes remain, each exactly `:= by sorry` in its own public theorem:

- `WeilConjectures.publishedSystemTensorIdentification`, node
  `lem-sf-published-system-tensor-identification`.
- `WeilConjectures.publishedSystemCompositorIdentification`, node
  `lem-sf-published-system-compositor-identification`.

Thus this packet is a decomposition of one original obligation into two strictly simpler
identifications, not a net proof of that obligation. It closes one original hole and adds two.
No hole is left inside a definition or private declaration. The imported ambient coherence and
published representative-existence statements retain their existing proof obligations.

## No longer needed

The item no longer directly imports `Sheaf.SixFunctors.SystemPullbackCompositorIdentification`
or `Sheaf.SixFunctors.SystemPullbackTensorNormalization`. The former is used through the new
identification modules; the latter is still needed by the tensor identification's proof plan.
Consequently no existing module or DAG node is claimed as globally pruned. The original
ambient coherence dependency remains necessary. The generic source-library theorem
`map_leftDerivedTensorComparison_app_app_comp` uses a different tensor presentation and is not
an additional dependency of this proof.

## Where the brief, the DAG or earlier work was wrong

The existing compositor uniqueness lemmas compare two `Compositors` packages; they do not
identify either with `AmbientPullbackTensor.derivedComp`. Likewise representative rigidity
detects equality only after its representative equation is established. The earlier proof
plan omitted these two presentation identifications. They are now explicit, with the ordinary
section, adjunction, total-summand and localization arguments recorded in their docstrings.

The item and required imports were initially quarantined. The imports were restored in the
shared source during this session; the item is restored from its preserved source, with its
Lean attachment and target statement retained. No quarantine archive is removed. The unit
`sk-rem-sf-pf-done` is preserved; there is no bypass of a realized unit step.

## New nodes

`lem-sf-published-system-tensor-identification` identifies the single-morphism comparison under
`sequence_derived_eq`. It has no composition hypothesis or conclusion. Its proof uses the
adjunction-unit formula on pure tensors (Stacks 03EL), total summands, the specified K-flat
representative rectangle (07A4), and representative faithfulness. Its equation handles all
semilinear sequence transitions and all unbounded objects, including zero objects.

`lem-sf-published-system-compositor-identification` identifies the compositor under the same
functor equalities. It contains no tensor product or monoidal comparison. Its proof uses the
recorded section formula, conjugation under adjunction (03D3, 07A7), and faithfulness of
restriction along exact localization (015F). It applies to identities as well as arbitrary
composable morphisms. Both identification nodes are strictly parts of the argument; neither restates the
original tensor-composition obligation. There are no change records because only the item's
proof and node, and new modules and their nodes, are changed.

`lem-sf-tensor-comparison-transport` is proved by naturality and categorical cancellation.
`def-sf-published-system-ambient-presentation` records the existing ambient constructions in
the published sequence categories; its construction and pull-field identification are proved.
Neither node adds a proof obligation.

`lem-sf-published-system-ambient-coherence` is a proved specialization of the existing ambient
coherence theorem to the actual sequence categories and tensor models. It contains neither
published tensor comparisons nor an identification of a `Compositors` presentation. Giving
this equation its native category type avoids an expensive conversion in the final application.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
