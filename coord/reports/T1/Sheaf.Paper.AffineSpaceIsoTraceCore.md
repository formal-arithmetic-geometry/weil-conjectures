## What changed

Implemented `AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_eq_id` without changing its
signature. Its proof now performs the general-base part of the original three-step plan:

- Constructs the pulled-back automorphism using the affine-tower Cartesian square.
- Constructs the coefficient base-change isomorphism and proves its equivariance for
  arbitrary automorphisms from associativity of the derived pullback compositors.
- Applies `affineLinearExchange_action_naturality` to intertwine the actual actions.
- Uses `exists_affineSpaceTopTrace` to identify the fixed source with a degree-zero sheaf.
- Proves that identity on degree-zero homology detects an endomorphism of this source,
  and that jointly faithful geometric pullbacks detect identity of the resulting sheaf map.

The coefficient and exchange calculations adapt the already-proved private calculations of
`Sheaf.AlgebraicGeometry.AffineLinearActionFamily`; that existing module is unchanged.
All added imports in the item are private proof imports. No existing definition, instance,
public import, or declaration signature changes, and no other existing Lean module is changed.
The item node's proof, proof dependencies, and proof origin now describe the implemented route.

Validation: `lcompile.py --all` compiled both modules in import order without warnings;
the item compiled in 25.0 seconds, below the 60-second limit. A separate signature comparison
confirmed that the original public theorem's binders and conclusion are unchanged. The new
node's stored signature matches its Lean declaration exactly, and both node records have
proof-dependency lists equal to the union of their proof-step uses.

Added `Sheaf.Paper.AffineSpaceGeometricTopAction` for the remaining geometric calculation.
It asserts identity only on degree-zero homology over the spectrum of an algebraically closed
field. It contains no general-base descent, no claimed faithfulness of derived pullback,
and no trace-invariance hypothesis. These are strictly the geometric steps 1 and 2 of the
original plan; the parent supplies the complete Lean argument for step 3.

The constructions do not require a nonempty base. The jointly faithful family argument works
for the empty base, and neither faithfulness lemma assumes a nonzero coefficient ring.
Dimension zero is included throughout. The remaining geometric theorem's proof in words
addresses the zero-dimensional tower and the zero coefficient ring explicitly.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_eq_id`
(node `lem-pur-affine-space-iso-trace-action-id`) by a complete proof from the named
geometric homology theorem and existing declarations. The item has zero local holes.
All private helper theorems are fully proved; both private coefficient constructions contain
no holes and are explicit composites of existing isomorphisms.

Added one hole:
`AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_homology_zero`
(node `lem-pur-affine-space-geometric-top-action`) in the new module.
It has source attribution, a proof in words, and a matching DAG node.
This is a decomposition: one upper hole closed, one strictly smaller geometric-field
homology hole added, net zero holes closed. It does not claim completion of the point-class
calculation or an axiom-free proof of the original theorem's full import closure.

## No longer needed

Removed the redundant direct imports of
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` from the item and
`Mathlib.FieldTheory.IsAlgClosed.Basic` from the new field module while developing the proof.
The exchange-coherence module retains its own unbounded-exchange dependency, and the
algebraically closed field API is already publicly available through the action module.

No existing node or module is withdrawn, and no unit route is bypassed. All original
mathematical dependencies remain needed either directly or in the geometric subargument.
The matrix-specific universal family and connectedness machinery of
`AffineLinearActionFamily` is not imported: the coefficient comparison and exchange argument
are proved directly for arbitrary automorphisms. This does not prune that independently
needed existing module from the library.

## Where the brief, the DAG or earlier work was wrong

The original proof describes rational-point classes but the listed declarations do not
supply the assertion that arbitrary, potentially nonlinear affine-space isomorphisms fix
them. `exists_affineSpaceTopTrace` supplies concentration and an invertible trace, not the
naturality of those point classes for arbitrary automorphisms. The linear-invariance theorem
alone only covers matrices. No existing statement was weakened or disputed.

The strongest-looking vector Cartesian trace API depends on this item and would make a
cycle. The delivered proof instead uses the independent exchange-coherence API, and exposes
only the missing geometric-field calculation. Searches found affine-space coordinate APIs
and the single/homology comparison, but no matching geometric compact-support theorem.

## New nodes

`lem-pur-affine-space-geometric-top-action`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-space-geometric-top-action.json`, realizes
`AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_homology_zero` in
`Sheaf.Paper.AffineSpaceGeometricTopAction`. It isolates the top homology action over an
algebraically closed field, retaining the original rational-point normalization proof plan.
There are no change records because no existing interface was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AffineSpaceGeometricTopAction": "deec94aa17079c29e7ec9cfc73dc1d1a58656c0e", "Sheaf.Paper.AffineSpaceIsoTraceCore": "9a50838b7d39abc6e8b20bfa78e08e4f24b6e91e"}, "results": {"Sheaf.Paper.AffineSpaceIsoTraceInvariance": {"hash": "569bbf412f117cc8f128cd00c139d1b1bd5f9d7a", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T12:27:07+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
