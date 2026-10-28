## What changed

Replaced `exists_integral_reindexing_maps` by a proof using the existing
coefficient presentations, scalar adjunctions and exact-equivalence derived squares.
The finite constant-section normalizations identify the finite coefficient maps.
The residue equations and joint monicity of the completion projections identify
the completed maps. The native function equation then gives the coefficient square.
Its inverse gives an identity-on-sections square for scalar restriction.
Transposing this square constructs the ordinary balanced comparison; the normalized
adjunction units and scalar linearity give its pure-section rule. The universal
left-derived counits give the derived comparison with exactly the required
representative equation. All helper declarations are private and proved.

The statement and public imports are unchanged. Only the item module and its own
DAG proof record change. Added proof imports expose the proved scalar-mate and
derived-square implementation helpers within this proof.

## Proved and sorry left

Closed: `WeilConjectures.AdicQbarRealization.exists_integral_reindexing_maps`
(node `lem-sf-adic-integral-reindexing-maps`), one original hole.
Added holes: none. Split-off statements: none. Sorries left in the delivery: none.

Validation: `lcompile.py` compiled the complete item cleanly in 51.8 seconds
(exit 0), with transparency checks enabled and no profiling options remaining.
The theorem signature and public-import list match the original verbatim.

## No longer needed

The proof does not use `sk-prop-sfb-cartesian-coefficients`,
`sk-prop-sfb-qlbar-colimit-x`, or
`lem-pur-isomorphism-inverse-image-tensor-hom` as proof dependencies.
Their conclusions are unnecessary: this argument uses only a scheme isomorphism,
the already specified finite-residue presentations, and scalar adjunctions.
No claim is made that their modules leave the entire targets' import closure:
the unchanged public family-data import still exposes shared coefficient theory.
No existing public import or declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step concealed the distinction between a normalized
ordinary scalar comparison and its derived representative equation. Both can be
proved using existing library interfaces, without another existential restatement.
The realization equivalence, tensor and Hom laws supplied by `SpaceData` are
unnecessary beyond its coefficient presentations. The construction works for
identity and inverse scheme isomorphisms, empty schemes, zero modules and
unbounded complexes; no K-flatness assumption is added to the ordinary comparison.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicIntegralReindexingMaps": "f06cc5ab2e20c505b0fc9e143747c97d5d60bcd5"}, "results": {"Sheaf.Paper.AdicIntegralReindexingDescent": {"hash": "6ec8ec034cbf312bd88caba1ee1571de4b518c20", "status": "OK"}}, "seconds": 66, "time": "2026-10-28T08:32:33+0800", "transitive": 0, "version": 1}
```

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
