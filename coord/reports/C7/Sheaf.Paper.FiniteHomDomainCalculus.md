## What changed

Proved `WeilConjectures.finiteHomDomain_monoidal` with its statement unchanged.
`Sheaf.Paper.EtaleScalarDerivedComparison` identifies the fixed scalar adjoint and
its cochain representative with the native derived functor and counit.
`Sheaf.Paper.EtaleScalarMonoidal` transports the native strong monoidal structure,
identifies its tensorator by right-exact tensor-model uniqueness and its unit by
the left unit law, and proves signed braidedness.
`Sheaf.Paper.EtaleScalarNormalizations` proves both all-complex normalization facts.
`Sheaf.Paper.FiniteHomScalarMonoidal` packages these facts at generic rings before
the finite coefficient specialization in the assigned theorem.

The unchanged `FiniteHomDomainMonoidal` predicate is relocated verbatim to
`Sheaf.Paper.FiniteHomMonoidalData` and publicly re-exported from its original
module. Existing public imports, public names, signatures, definition bodies and
all completed proofs are preserved. The assigned module adds that public data
import and a private proof import of the generic-ring result. No existing module
besides the assigned module is changed; no source-library file is changed.

The separation is required by per-file kernel checking time: profiling the
combined file showed 33.5 s checking the generic bridge plus 15.5 s checking the
finite specialization, on top of earlier proofs. Every new theorem is proved;
this is a split into compiled proofs, with no added holes. The relocation is
recorded in `coord/changes/C7-finite-hom-monoidal-module.md`.

Validation: final files compile without profiling options, each within 60 s.
The assigned file takes 54.2 s; the derived comparison 31.9 s, monoidal support
37.1 s and generic-ring bridge 36.5 s. All three unchanged direct consumers
compile against the delivered files: EtaleLisseHomReduction (58.3 s),
FiniteCoefficientHomChange (43.5 s), and SixFunctors.FiniteCoefficientVerdier
(26.5 s). Their temporary sandbox copies are removed after verifying that they
were unchanged. Axiom probes of the assigned theorem and all four new public
theorems show exactly `propext`, `Classical.choice` and `Quot.sound`, without
`sorryAx`.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.finiteHomDomain_monoidal`
(node `lem-coef-finite-hom-domain-calculus`). This is a proof, not a decomposition.
The following new public theorems, and every private helper, are fully proved:

- `AlgebraicGeometry.Etale.ExceptionalCoefficients.scalarExtension_derivedComparison`
- `AlgebraicGeometry.Etale.ExceptionalCoefficients.scalarExtension_coreMonoidal`
- `AlgebraicGeometry.Etale.ExceptionalCoefficients.scalarExtension_normalizations`
- `WeilConjectures.finiteHomScalar_monoidal`

One original hole remains, unchanged:
`WeilConjectures.finiteHomDomain_scalarCoherence`
(node `lem-coef-finite-hom-domain-calculus`). Its existing docstring and node step 7
state the successive-scalar and identity comparison argument. In particular the
monoidality just proved does not by itself identify the specified canonical
scalar associator or identity mate with monoidal transformations. No new holes
are added, and no holes are split off.

## No longer needed

The ambient monoidality proof uses the existing native derived monoidal structure
and the normalized tensor/unit APIs instead of the planned ringed-topos detour.
The following direct proof dependencies are removed from this item's node:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-pc-kflat-resolution`
- `lem-pur-kflat-total-tensor-model`
- `lem-weil-pbc-pullback-tensor-canonical-shift-unit`
- `lem-sf-ringed-derived-closed-symmetric-monoidal`
- `def-sfb-strong-monoidal-functor`

The scalar-composition hole retains its original system-scalar and
ringed-derived-monoidal-comparison dependencies. No source-library declaration or
module is withdrawn. There are no removed Lean imports: the original imports
support the unchanged statements, definitions and earlier proofs, and each new
proof import supports an API used in the new proof. The listed nodes may remain
needed by other modules or transitively by the normalization API.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The prior monoidality plan is longer than needed:
the adopted source library already constructs strong monoidality and braidedness
of a native total left derived functor under preservation of flat objects and
K-flat quasi-isomorphisms, without requiring coefficient flatness. The missing
work here was to identify that structure with the fixed scalar adjoint and the
published normalized comparisons; this is now proved. Ordinary exact-functor
composition lemmas cannot be specialized blindly to nonflat quotient maps.

Checked the current server queue and saved build error before starting: this is
a proof assignment with two holes, rather than a zero-hole rework assignment.
Edge cases of the generic proof include the empty scheme, identity ring map,
zero coefficient ring and nonflat quotient maps; no step assumes nonemptiness,
nonzero coefficients, coefficient flatness or finite Tor dimension.

## New nodes

`lem-coef-etale-scalar-monoidal` records the fully proved generic scalar-extension
monoidality theorem in `Sheaf.Paper.EtaleScalarMonoidal`. Its proof records the
native construction, representative normalization, unit cancellation and signed
braiding transport, and its Lean signature is copied verbatim. It extracts the
ambient monoidality clause of the assigned node, keeps the same chapter and unit,
and does not bypass a blueprint unit. The change record for the literal predicate relocation is
`coord/changes/C7-finite-hom-monoidal-module.md`; the public interface and
mathematical meaning are preserved.

`lem-coef-etale-scalar-normalizations` records the fully proved normalization
choose-spec calculations in `Sheaf.Paper.EtaleScalarNormalizations`. Its conclusion
is precisely the two all-complex normalization conjuncts of the assigned theorem.
This split isolates kernel work at generic rings and adds no holes or mathematical
assumptions.

`def-coef-finite-hom-monoidal-data` owns the unchanged relocated predicate in
`Sheaf.Paper.FiniteHomMonoidalData`. Its signature and definition body are
byte-for-byte identical to the original.

`lem-coef-finite-hom-scalar-monoidal` owns the fully proved generic-ring packaging
in `Sheaf.Paper.FiniteHomScalarMonoidal`. This isolates kernel checking without
changing the mathematical statement or adding a hole.

`lem-coef-etale-scalar-derived-comparison` records the fully proved comparison
between the native and fixed scalar adjoints and their cochain counits in
`Sheaf.Paper.EtaleScalarDerivedComparison`. Its K-flat quasi-isomorphism
preservation hypothesis is supplied by the existing etale scalar preservation
proof at the call site, including for nonflat quotient coefficients.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.EtaleScalarDerivedComparison": "12e72037ffbe8b70718b13e3a41b9c0f134a5aca", "Sheaf.Paper.EtaleScalarMonoidal": "28cbc4e2bcc78d92c2ad04ee95b63c6628516df8", "Sheaf.Paper.EtaleScalarNormalizations": "4f53ddbda292148a400749af6c299fd9251fe06a", "Sheaf.Paper.FiniteHomDomainCalculus": "b31ccff7e26e33cfcbe7599ae6d8be23094d4fb8", "Sheaf.Paper.FiniteHomMonoidalData": "6ce97199f54e959a8ab74dd088dd47d1ded741a2", "Sheaf.Paper.FiniteHomScalarMonoidal": "107fa5e4486743237c718bd98f6c53fee655c569"}, "results": {"Sheaf.Paper.EtaleLisseHomReduction": {"hash": "7d7f463603e120febe4174e91bd3672466e8fc2a", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientHomChange": {"hash": "6040c31ddad1fd61407da5e854c90f3fc5f5636b", "status": "OK"}, "Sheaf.SixFunctors.FiniteCoefficientVerdier": {"hash": "a341c16bfa184e1bf084d648c57b274c9f44a6de", "status": "OK"}}, "seconds": 150, "time": "2026-10-28T07:27:39+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
