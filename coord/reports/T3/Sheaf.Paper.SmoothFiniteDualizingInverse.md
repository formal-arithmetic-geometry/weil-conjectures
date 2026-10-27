## What changed

Proved `WeilConjectures.PurityFiniteSetting.smooth_finite_dualizing_inverse` in
`Sheaf.Paper.SmoothFiniteDualizingInverse`, with its signature and public imports unchanged.
Only this Lean module and its own DAG node change. All added helpers are private and proved;
all added imports are proof imports.

The proof uses the adopted source library's `Etale.isInvertible_dualizingComplex` and
`Etale.constructibleFiniteTor_dualizingComplex`. A tensor inverse is identified with
`RHom(omega, unit)` using `exactPairingOfTensorIso` and `MonoidalClosed.ihomObjUnitIso`;
`Etale.constructibleFiniteTor_coefficientDual` gives its finite-Tor constructibility.
This avoids proving a separate shifted-line inverse theorem.

The intrinsic assembly is explicit: normalize the selected etale monoidal structure to the
native derived structure; use `finiteHomNuTensor` for both tensor evaluations; construct the
unit comparison from the sheaf-level strong monoidal comparison and
`proEtaleConstantModuleUnit`; undo intrinsic realization and use the bounded-below derived
comparison unit to identify the actual exceptional image. Convert source constructibility
and Tor conventions and apply `finiteCoefficient_comparison_preserves_torAmplitude` to both
objects. The last helper transports the recorded intrinsic predicate along isomorphisms
by its actual homology and Tor tests.

The proof derives compactification, invertible exponent, coefficient finiteness and
algebraic closedness from the given datum. It adds no absolute separatedness assumption,
no orientation, and no positive-dimension or nonempty-source assumption. The tensor
inverse and coefficient dual arguments also apply in the zero category of the empty
scheme. The DAG proof, proof dependencies and proof origin now describe this route.

Validation: the complete delivered Lean module compiled through `lcompile.py` with
no diagnostics in 23.7 seconds, below the 60-second limit. Its original theorem
signature is byte-identical, and only `proof`, `proof_deps` and `proof_origin`
changed in the existing node.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.PurityFiniteSetting.smooth_finite_dualizing_inverse`
(node `lem-pur-smooth-finite-dualizing-inverse`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No new intermediate statement, definition hole, axiom or split-off module is added.
The proof uses existing declared dependencies, including dependencies whose proofs
are still open; this is a proof from the project's existing declarations.

## No longer needed

No original import was removed, and no module is withdrawn. The following parts of the
old planned route are not used directly by this proof:

- `lem-pur-shifted-line-site-inverse` / `Sheaf.Paper.ShiftedLineSiteInverse`: replaced
  by native smooth invertibility, an exact pairing, and coefficient-dual preservation.
- `thm-asd-smooth-tensor` / `Sheaf.AlgebraicGeometry.SmoothTensorDuality`: use the adopted
  source consequence of `lem-sf-smooth-dualizing-complex-invertible` directly.
- `lem-sf-intrinsic-realization-origin-comparison`, `lem-sf-intrinsic-realization-flat`,
  and `lem-sf-cochain-tensor-model-rigidity`: the already normalized
  `finiteHomNuTensor` comparison supplies the tensor isomorphism. The exceptional-origin
  identification uses the actual derived realization equivalence and comparison unit.
- `lem-sf-intrinsic-comparison-constructibility` and
  `lem-sf-intrinsic-comparison-tor-amplitude` are now used through the existing wrapper
  `lem-sf-comparison-tor-amplitude`, rather than reassembled separately here.

These are removals from this node's direct proof plan, not claims that these nodes
are globally unreachable. Existing public imports and source-library declarations
are preserved, and several of these results remain transitive dependencies of the
existing comparison APIs. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned shifted-line construction was unnecessary: native etale invertibility and
coefficient-dual preservation already provide the inverse and its finite-Tor property.
The remaining work was the explicit comparison with the specified intrinsic tensor,
unit and exceptional image, not a new smooth-purity assertion.

The current server queue assigns this as a proof item. Its historical build-error file
mentions an import of `Sheaf.Paper.ClopenStrictSystemComparison`; the current original
module compiled against the published artifacts before proof edits, so that historical
import failure did not require a declaration or dependency repair. No statement or
public interface was changed. The original proof docstring remains the earlier
mathematical plan; the updated DAG and this report record the implementation's shorter
route.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SmoothFiniteDualizingInverse": "a2736172be21c36fffa4b58c9ba225d42ad30aa6"}, "results": {"Sheaf.Paper.VaryingDimensionDualizingInverse": {"hash": "5208f571bcbf5193a3edbcacd08604e507aaa936", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T00:44:33+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
