# AlgebraicGeometry.ProEtale.integralTensorShriek_generated

## Reason

The returned restoration packet was a no-op: the current library already contains the
archived module and both complete theorem proofs. This packet instead prunes an unused
proof import and its DAG dependency and reuses existing proofs. There are zero holes.
Every public signature, public import, definition body and local attribute stays identical.
This is proof maintenance and dependency pruning, not newly closed proof-hole progress.

## Old

The private import was:

```lean
import Sheaf.Paper.ProfinitePointPullback
```

The generation proof contained the following hand-written closure induction:

```lean
    have h : ∀ r : ℕ, (condensedLocallyClosedPiece Λ X).extensionProductIter r ≤ P := by
      intro r
      induction r with
      | zero => exact hpiece
      | succ r ih =>
        rw [ObjectProperty.extensionProductIter_succ]
        rintro L ⟨A, B, f, g, k, hdist, hA, hB⟩
        exact P.ext_of_isTriangulatedClosed₂ _ hdist (hpiece A hA) (ih B hB)
    exact h r _ hr
```

The preservation proof duplicated its open-immersion argument for the open part of the
locally closed immersion. The local `hopen` was specialized to the ambient scheme X.

## New

Remove the private import. No declaration from it occurs in this module. The point
pullback, adjunction and finite-biproduct API remain available from existing public imports.
Remove lem-weil-pbc-profinite-point-pullback from proof_deps and the local-model step's uses.
The unit's open/closed localization and integral-heart resolution route is retained.

Replace the induction with the existing Mathlib theorem:

```lean
    exact (condensedLocallyClosedPiece Λ X).extensionProductIter_le_of_isTriangulatedClosed₂
      hpiece r _ hr
```

Generalize the proof-local `hopen` over a Noetherian target Y. Its first use is `hopen X`;
its second use is `hclosed Z i _ (hopen Z S v M hM)`, replacing the duplicate homology proof.
No new declaration, data or statement is introduced. Zero objects, rank zero and empty
strata are covered by the retained original construction and proofs.

## Users

A direct-import scan includes both lean/ and quarantine/. The three direct consumers
below retain the same public API. No consumer is adapted; their claims are unaffected.
The scratch public-API importer prints axioms for all three public declarations and
constructs a point complex. This change does not remove any public import or instance. The revised item compiles
in 17.7 seconds; the public-API probe compiles in 3.0 seconds and prints only the three
permitted axioms for every public declaration. Unchanged scratch copies of the direct
consumers compile in 17.2, 10.1 and 31.4 seconds respectively. tools/downstream.py --direct
confirms exactly these three importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralTensorPullback | not queried; untouched | Identical public API. |
| Sheaf.Paper.IntegralTensorProduct | not queried; untouched | Identical public API. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not queried; untouched | Identical public API and unit route. |

## Status

landed 20261021T060937-L-1674723 2026-10-21 (merge of deliver/C2/Sheaf.Paper.IntegralTensorShriek)
