## What changed

Proved `WeilConjectures.frobeniusIntegralRootTransport_additive` without changing its
statement or public imports. The map is the sheafified discrete tensor comparison.
Its inverse follows from sectionwise tensor equivalences and local bijectivity of
sheafification along the base-change site equivalence. Completed scalar compatibility
is checked first on the two coefficient factors, then on arbitrary coefficients by
tensor induction, and finally on arbitrary sheaf sections by local descent.

Three new, fully proved auxiliary modules separate discrete transport, its
invertibility, and compatibility with completed root scalars. They introduce no
unproved statements and construct all maps explicitly. Only the item's proof and
its DAG proof description, plus these new modules and their nodes, are delivered.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.frobeniusIntegralRootTransport_additive`.

Added zero holes. The following new public theorems are proved:

- `WeilConjectures.frobeniusIntegralDiscreteTransport_isIso`;
- `WeilConjectures.frobeniusIntegralDiscreteTransport`;
- `WeilConjectures.frobeniusIntegralRootScalar`.

Validation: `lcompile.py --all` compiled the four delivered modules in import
order (24.1, 18.9, 16.9, and 17.0 seconds). A temporary probe printed the axioms
of all four public theorems: exactly `propext`, `Classical.choice`, and `Quot.sound`.
The probe was removed before delivery.

Every private helper is proved. No declaration in these four modules contains
`sorry`, and no definition takes data from a new existence assumption.

The arguments allow arbitrary schemes, including the empty scheme and schemes
where l is not invertible. Tensor equivalences handle zero section rings; the
local descent argument does not assume global tensor presentations of sections.

## No longer needed

No original public import, original dependency, node, or module is withdrawn.
No global pruning is claimed. The proof uses the existing coefficient tensor
presentation instead of adding a generic semilinear tensor-presentation theorem.
The new proof modules do not need a public import of the module adjunction API.
The invertibility module also omits `IntegralCompactSupportCoefficientData`,
since it uses neither completed scalar transport nor compact support. The item's
existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan did not spell out the compatibility square for the completed
coefficient map. It is established by finite projections of the completed rings,
using cofinal reduction factors, and used to prove root scalar compatibility.

The public package `ambRootTowerPullbackCoherence` assumes invertibility of l on
both schemes, whereas this item's statement does not. Its already proved private
root-limit linearity, constant naturality, and discrete tensor sublemmas quantify
over arbitrary schemes. The proof uses those sublemmas through proof-only
`import all`, and never applies the public package with a missing hypothesis.
No additional invertibility assumption and no statement change is made.

The historical blueprint ancestry of the item is retained. The new nodes cite
the latest coefficient-twist blueprint and the actual tensor-pullback source
(Stacks Project Tags 03EK and 03EL). Their proof descriptions follow the Lean
construction, not a restatement of the original obligation.

## New nodes

- `new-weil-frobenius-integral-discrete-transport-invertible`: invertibility of an
  already specified additive map with the discrete pure-tensor formula.
- `new-weil-frobenius-integral-discrete-transport`: construction of the additive
  tensor isomorphism and compatibility with discrete integral coefficients.
- `new-weil-frobenius-integral-root-scalar`: compatibility on root tensors with
  the image of completed Z_l coefficients.

All three are proved; none is a split-off obligation left for another worker.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusIntegralDiscreteTransport": "73adc93c6f7db2f2b17f9fe2531f058800bdb0b7", "Sheaf.Paper.FrobeniusIntegralDiscreteTransportInvertible": "b3e674645141a19f9437775418964ed6fdf55e7d", "Sheaf.Paper.FrobeniusIntegralRootScalar": "107dddfeb047f10dbd351c0e5f01a001bfa25f3e", "Sheaf.Paper.FrobeniusIntegralRootTransportAux": "67fc5018fb54d191ee713e31f717c96553db070b"}, "results": {"Sheaf.Paper.FrobeniusIntegralRootTransport": {"hash": "5485d25f6d1c738e2a6eb7ed6823b7c2a1e0d897", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T10:50:09+0800", "transitive": 0, "version": 1}
```

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
