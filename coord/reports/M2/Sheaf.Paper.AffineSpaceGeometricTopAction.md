## What changed

Replaced the proof hole of `AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_homology_zero`
by a complete Lean proof from one strictly geometric intermediate theorem,
`AlgebraicGeometry.affineSpace_polynomial_deformation`. The original statement is unchanged.
The new intermediate contains only schemes, coordinates and matrices: it has no cohomology,
coefficient rings, trace action or homology equality.

The item proves the substantial cohomological part explicitly. Its private helpers establish
coefficient-descent coherence and compact-support action base change for arbitrary compatible
automorphisms, prove identity of every linear action using the universal GL family and rigidity,
and detect identity on the parameter line using tensor-invertibility of the affine trace source.
The zero-endpoint comparison, identity detection, and one-endpoint comparison then prove identity
of the actual derived action, and the final homology identity follows by functoriality.
The argument does not assume that general derived inverse image is faithful.

Added proof imports of `AffineLinearActionFamily`, `AffineLinearActionRigidity`,
`AffineLinearExchangeCoherence`, derived `Exchange`, `InvertibleRestriction`, `CoefficientsShift`
and the new geometry module. Kept the original public import unchanged. Updated only the item's
DAG proof, proof dependencies and proof origin; added the new geometry node. No shared definition,
existing signature, source-library declaration or target was changed.

The main item compiled on the server in 25.2 seconds before the final documentation/import cleanup;
the final all-file compile checks that cleanup too. Both files respect the 100-character limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.affineSpaceIsoTraceAction_homology_zero`
(node `lem-pur-affine-space-geometric-top-action`). Its proof and every private helper are complete.

Added one hole, exactly the public theorem
`AlgebraicGeometry.affineSpace_polynomial_deformation`
in `Sheaf.Paper.AffineSpacePolynomialDeformation`
(node `lem-pur-affine-space-polynomial-deformation`). Its proof is exactly `by sorry`.
This is a decomposition: one upper hole closed and one strictly geometric hole added, net zero.
It is not reported as a completed proof of polynomial deformation or as net sorry reduction.

The remaining construction is explicit: for polynomial F with inverse G and b=F(0), use
H(t,x)=(F(tx)-b)/t+t*b and J(t,y)=G(t*y+(1-t²)*b)/t. The docstring and node explain polynomial
divisibility, both inverse identities, the endpoint matrix and scheme-coordinate transport.
Small cases checked by hand: d=0 gives identity and the empty invertible matrix; translations
F(x)=x+b give H=x+t*b and J=y-t*b; an invertible linear map gives the constant family; for the
triangular example F(x,y)=(x+y²+2,y+3), H=(x+t*y²+2*t,y+3*t) and
J=(x-t*(y-3*t)²-2*t,y-3*t). The formula uses no characteristic-zero division: division is exact
polynomial division by the indeterminate t. It applies in every characteristic and does not
need algebraic closure. Zero coefficients are allowed by the proved cohomological argument.

## No longer needed

The rational-point-class generation subargument, pointwise Kummer-boundary naturality and
geometric-stalk conservativity are not needed by this proof. In particular the original direct
proof dependencies `def-amb-p1-trace` and `lemma-weil-pbc-geometric-stalk-conservative` were removed
from this node's proof dependency list. The ordered projective-line trace remains used through
`lem-amb-affine-space-top-trace`; this is not a claim that either old node is globally unreachable.
`lem-asd-etale-finite-twist-pullback` and the trace-action definitions remain used.

No original Lean import was removed; its sole public import remains. An exploratory import of
`WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection` was removed because the weaker
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` supplies the required sections and the
closed-zero-section instance. No module is withdrawn or claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG plans a rational-point-generator proof but does not state an ordinary
finite-coefficient point-class compatibility lemma with the actual action. The existing
pro-etale regular-immersion interfaces have different coefficient and base assumptions.
Rather than moving the same cohomology assertion yet again, this delivery proves the full
cohomological comparison and isolates a coordinate-algebra construction, independently useful
and strictly simpler. The UNIT route is retained: ordered P1 integration, affine top trace,
linear invariance and degree-zero comparisons are all used below the unit level.

The deformation is sourced in Furter--Poloni, *On the maximality of the triangular subgroup*,
Lemma 3.1, proof pp. 5–6, and Blanc, *Conjugacy classes of special automorphisms of the affine
spaces*, introduction pp. 939–940. Both PDFs were read and obtained in the sandbox scratchpad.
The combined one-parameter formula and its characteristic-independent verification are marked
as written by agent M2. These references are not currently in the project's literature catalog;
the read-only delivery contract allows no edits to that catalog, so the maintainer should add
these two already obtained references. The new node and Lean docstring give their direct URLs.

The blueprint ancestor helper reports `from.node = None` when invoked with this item's node id
because its `created.item` is a module name; the existing node's explicit blueprint ancestry
identifies `cor-pur-vector-bundle-purity`, which the new node preserves. A full blueprint search
for polynomial deformation, linear part and affine automorphism returned no matching node.

## New nodes

`lem-pur-affine-space-polynomial-deformation`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-space-polynomial-deformation.json`, states the
geometric family and its actual endpoint squares, with source, complete coordinate proof,
Lean attachment and three logged Mathlib search kinds. Its sole new Lean module is
`Sheaf.Paper.AffineSpacePolynomialDeformation`. It is strictly geometric; the item proves
how this family controls the original action using existing, proved sheaf-theoretic APIs.
No change records are needed because no existing public interface or other module is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AffineSpaceGeometricTopAction": "d71b8ca5dadb12435e95e97b3a45e44f17ade928", "Sheaf.Paper.AffineSpacePolynomialDeformation": "1f5b542c03a1b89727bcf75a03230f72653018d7"}, "results": {"Sheaf.Paper.AffineSpaceIsoTraceCore": {"hash": "9a50838b7d39abc6e8b20bfa78e08e4f24b6e91e", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T14:20:17+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
