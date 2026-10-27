## What changed

Proved `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace`
with its original signature. The proof encodes the native constructible sheaf into condensed
algebraic-closure coefficients, applies the existing general proper direct-image theorem, and
reflects boundedness and constructible homology. The affine finite-type hypotheses provide
Noetherianity. Empty bases and zero-dimensional projective spaces are included.

Added the fully proved comparison `AlgebraicGeometry.ProEtale.encoding_constructible_iff`.
Its proof uses finite-free local trivializations, the existing condensed local-freeness result,
and the two definitions of finite constructible stratifications.

The initial import graph was circular. To make the proof usable, extracted the native interface of `NativeEncodingDerivedOperations` into `NativeAdicEncodingCore`, publicly
reexported by the original module. Removed unused broad proof imports from
`FiniteLevelProEtaleBaseChange` and `LisseNormalizedTowerLocalModels`. Replaced the broad
`FieldStagePointers` proof import of `EllAdicProperConstructibleCohomology` with narrow imports
and proved private bounded-induction and finite-field Tor-amplitude helpers. The former wraps
the existing `DerivedCategory.prop_of_bounded` dévissage theorem. Its public
statements and proofs remain complete. Every adapted module was unclaimed when inspected.
No adopted `WeilConjectures` source file was edited.

The change record is `coord/changes/J1-native-adic-finiteness-imports.md`.

## Proved and sorry left

Original item: one hole closed, zero remain, zero new proof obligations split off.
The closed declaration is
`AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace`.
The new comparison `AlgebraicGeometry.ProEtale.encoding_constructible_iff` and all new private
helpers are fully proved. No signatures of existing declarations changed. The local
unused-section-variable lint is
disabled for the item because the original algebraic-closedness assumption is retained even
though the general proper theorem applies over an arbitrary field.

The native declarations were relocated from `NativeEncodingDerivedOperations` to
`NativeAdicEncodingCore` and remain publicly reexported. Four existing holes were also
closed there, in namespace `AlgebraicGeometry.ProEtale.NativeEncoding`:
`coefficientIsoMon` (composition of the existing ring comparisons), `encodingAdditive`
(pointwise addition of underlying maps), and `encoding_underlying` (definitional equality), and `encoding_exact_derived`
(exact equivalences and the inverse unit isomorphism for K-injectivity).
Two existing holes remain, attached to `lem-sf-native-adic-encoding-ordinary-operations`:
`encoding_isEquivalence` and `encoding_ordinary_operations`.
These are retained obligations, not new holes or newly postponed work.

Two existing holes were also closed in `NativeEncodingDerivedOperations`:
`weil_resolution_comparison` transports K-injectivity through forgetting and encoding;
`native_encoding_derived_operations` combines the existing natural pull/push comparisons
with exactness of condensed pullback. Two unchanged holes remain there, attached to
`lem-sf-native-encoding-derived-operations`, in the same namespace:
`derivedPushComparison_unit` and `native_constant_action`. The unchanged
`AlgebraicGeometry.Scheme.lisseNormalizedTower_local_models` hole remains in the adapted
local-model module. The other adapted existing modules contain zero holes. Thus the packet
closes seven existing holes and adds zero; the five retained holes all predate this work.
The main theorem still depends on existing stated native-encoding obligations, as stage 3
permits; this is a proof from existing declarations, not an axiom-free final target closure.

## No longer needed

No original proof import was removed from the item: its original proof was `sorry` and
imported no proof dependencies. Its replacement proof does not directly use the planned
nodes `lem-weil-pbc-lisse-e-constructible-integral-lattice`,
`lem-fin-proper-bounded-constructible`, `thm-fin-proper-case`,
`lem-sf-integral-direct-image-constructible`, or
`def-weil-algebraically-closed-coefficients` as a proof lemma. The last remains a statement
dependency. The general proper condensed theorem already packages the coefficient passage,
so these are removed only from this item's direct proof plan; no claim is made that they
leave the targets' transitive closure. The proper-projective-space dependency is retained.

Removed proof imports:

- `EllAdicProperConstructibleCohomology`: `WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers`
  (replaced its two used facts by narrow imports and fully proved private helpers).
- `FiniteLevelProEtaleBaseChange`:
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension`
  (only a generic derived reflection instance was used; now proved directly).
- `LisseNormalizedTowerLocalModels`: `Sheaf.Paper.CompatibleFiniteDerivedTrivializations`
  (unused).

The native core does not need the fixed-pair/Weil-sheaf imports of its former container.
Those imports and all original declarations remain in that container for its other users.
No module is withdrawn, and no upstream declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned dependency declarations exist, but the concrete Lean import graph has cycles
through native lower-star finiteness: both the general proper theorem and the original
native-encoding container reached this item. Acyclic DAG records alone did not expose this.
The packet repairs those import routes without changing their statements or replacing any
proved declaration by `sorry`.

No mathematical statement was found false. The new constructibility comparison was checked
against rank zero, empty strata, empty schemes, and disconnected local trivializations.
The compactification unit's proper case is retained; only its coefficient implementation
is reused from the existing general theorem. `tools/blueprint_refs.py ancestor` returns no
ancestor for the item (its creation chain names a Lean module), so the new nodes record the
proper-case clause and the explicit via chain with a null `from.node`; whole-blueprint
searches found no existing statement of either comparison.

The whole seven-file set compiled before the final two fixed-pair proofs; those final
proofs were then compiled in their actual container without warnings in 18.1 seconds.
The final core compiled without warnings in 10.6 seconds. All original signatures,
attributes and non-theorem data were checked unchanged. Seven existing holes are closed,
zero added.

## New nodes

- `lem-sf-native-adic-encoding-constructibility`: a fully proved comparison, not a new hole.
- `lem-sf-native-adic-encoding-ordinary-operations`: the existing native declaration group
  extracted from `lem-sf-native-encoding-derived-operations`; six existing obligations are
  reattached here; four are proved in this packet and two remain unchanged. The original node keeps the
  fixed-pair declarations and depends on this native core.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
