## What changed

Proved `WeilConjectures.purOrdinaryAdjunctionScalar_bounded` without changing its signature or any public definition. The pullback clause uses the canonical uniform reduction criterion and constructible reduction pullback. The direct-image clause uses the finite-tower constructibility theorem, a proved private Roos-triangle comparison, and a proved private exact coefficient-equivalence comparison. Both scalar clauses use `pbcEmbeddingAmbientTensor_preserves` and the coefficient-model bounded predicate equivalence. New imports are private proof imports. Full-module validation through lcompile.py passed with no warnings in 42.1 seconds. The finite-type and quasi-compact composition instances are supplied explicitly to avoid an expensive typeclass search. Updated the existing node's proof, proof dependencies and proof origin to match this route.

The four-hole G2 version present at the beginning of this session is retained; its earlier proofs are not claimed as H2 work. The shared checkout temporarily displayed a fourteen-hole pre-G2 version during synchronization and subsequently returned to the four-hole version. No source-library file, target, statement or definition is changed.

## Proved and sorry left

Closed one existing hole: `WeilConjectures.purOrdinaryAdjunctionScalar_bounded`.
Added zero holes and zero new public statements. The three new private helpers, `purBoundedIso`, `purPushTowerIso` and `purPushCoefficientIso`, are proved.

Three existing holes remain, all on node `lem-pur-ordinary-adjunction-scalar-compatibility`:

- `WeilConjectures.purScalarRightDerivedComparison_normalization`.
- `WeilConjectures.purOrdinaryAdjunctionScalar_identity`.
- `WeilConjectures.purScalarModel_coherence`.

## No longer needed

The boundedness proof does not use `Sheaf.Paper.IntegralOperationsPreserveConstructible` (`lem-pur-integral-operations-preserve-constructible`) or `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` (`lem-weil-integral-scalar-extension-constructible`). The canonical completed reduction criterion proves the pullback clause directly, and `pbcEmbeddingAmbientTensor_preserves` already handles the actual scalar functor. These were absent from the G2 proof-import list and are removed from this node's proof dependencies where no remaining step uses them. No module is withdrawn and no adopted source declaration is removed. Other public imports and the G2 proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

The boundedness plan's integral-operation route is longer than necessary given the existing completed-coefficient reduction and scalar interfaces. The ordinary direct-image endpoint requires an explicit comparison to the prescribed finite-tower output; the private helpers provide that missing glue rather than treating an arbitrary cone as definitionally equal to the actual derived image. The auxiliary structure on X is changed to the composite through f solely when applying the finite-field direct-image theorem, as required by the node; the original structures need not make f a morphism over the base.

Edge cases: the reduction interval argument permits zero complexes and empty schemes; no nonempty scheme assumption or compatible original base structures is added. The scalar clauses also allow the identity extension and ramified extensions.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
