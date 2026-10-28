## What changed

Replaced the body of `WeilConjectures.finiteHomDomain_scalarCoherence` by an explicit
assembly of the published scalar tensor and regular-unit comparisons. The actual quotient
composition and identity equalities are used unchanged. Private generic helpers package the
existential and heterogeneous-equality witnesses before specialization to finite coefficients.
All existing public signatures, definitions and public imports are preserved.
Proof imports supply tensor composition, tensor identity, unit composition and unit identity.

Added `Sheaf.Paper.EtaleScalarTensorComposition`, `Sheaf.Paper.EtaleScalarTensorIdentity` and
`Sheaf.Paper.EtaleScalarUnitIdentity`. The first isolates the tensor-composition component of
original proof step 7. The tensor identity follows from it by a proved categorical cancellation
argument: identify the identity compositor by the adjunction composition law, use tensorator
naturality, cancel the tensorator and use faithfulness of an endofunctor isomorphic to identity.
The unit identity proof follows the existing private proof in
`Sheaf.SixFunctors.FiniteDualizingQuotientNormalization`; that source file is unchanged.
The regular-unit composition theorem is reused from `EtaleScalarUnitComposition`.

Added the fully proved `WeilConjectures.scalarDomain_pullback` in
`Sheaf.Paper.EtaleDomainPullbackCalculus` to share coefficient-category instances at generic rings.
`finiteHomDomain_pullback` now specializes that calculation, with its original public
signature unchanged. Its old private bounded-constructibility conversion moves to this new
module. The mathematical proof and Tor endpoints are unchanged. Profiling showed that the
concrete pullback and monoidality specialization proofs still each required about 16 seconds
of kernel checking after generic packaging and the existing irreducibility annotations.
Those two fully proved specializations are therefore extracted into private proof modules
`FiniteHomDomainPullbackProof` and `FiniteHomDomainMonoidalProof`; the main file imports
these with `import all`. Their private coefficient abbreviations expand to the unchanged
coefficient types. This distributes kernel checking without adding a public declaration,
changing a definition, or adding a proof hole. The resulting sandbox compile took
33.2 seconds for the main file and 15.9/18.2 seconds for the two private proof files.
The intentional-private-module linter is disabled in those two files; development profiling
options and markers have been removed.

The tensor-composition statement was checked on identity maps, nonflat maps, the zero ring,
zero objects and the empty site. It asserts equality of the canonical balanced maps and imposes
no flatness hypothesis. On pure tensors both routes are
`((x tensor y) tensor b) tensor c` mapped to
`(x tensor psi(b)c) tensor (y tensor 1)`. The identity proof uses only naturality and isomorphism
cancellation, so also covers all those cases.

## Proved and sorry left

Original holes: one, `WeilConjectures.finiteHomDomain_scalarCoherence`.
That declaration now has a complete Lean proof and the item module has zero local holes.
Added holes: one, `AlgebraicGeometry.Etale.ExceptionalCoefficients.scalarTensor_comp`, node
`lem-coef-etale-scalar-tensor-composition`, in its own module. This is a decomposition of one
hole into one strictly smaller tensor-composition square, not a net proof of the original hole.
The original assertion also includes two unit squares, a tensor identity square and the explicit
witness identifications; their assembly is now Lean code.

`AlgebraicGeometry.Etale.ExceptionalCoefficients.scalarTensor_id` and
`WeilConjectures.scalarUnit_id` contain no local holes. The former depends on the new
composition theorem; the latter is fully proved from the existing exact-degree-zero interface.
No other hole is added or left in the delivered modules.

## No longer needed

No module was withdrawn. The following proof imports used only by the pullback calculation move
from the main file to the generic pullback module:
`WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic`,
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`.
`Sheaf.Paper.FiniteHomScalarMonoidal` moves from the main file to the private monoidality
proof module. The main file also drops its temporary direct import of the new generic
pullback module, which the private pullback proof imports.
The main node no longer directly cites `prop-weil-pbc-inverse-image-modules-exact`,
`prop-constructible-pullback`, `lem-weil-pbc-ringed-topos-flat-module-pullback`, or
`lem-kun-kflat-criteria`; their tool-use entries move out of the main node. These remain
needed by the new generic pullback node. The direct proof of the item
no longer uses `lem-pur-system-scalar-model`, `lem-pur-system-scalar-coherence`,
`lem-pur-kflat-change-of-rings`, `lem-pur-cochain-pullback-tensor-coherence`, or
`lem-sfb-ringed-derived-monoidal-comparisons`; their obsolete direct tool-use entries were
removed. The first four remain in the proof plan of the new tensor-composition node, so this is
not a claim that they are globally pruned. The separate ringed-derived monoidal-comparisons
route is unnecessary here. Identity coherence needs no separate K-flat calculation once tensor
composition is known.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. Original step 7 described the expected
pure-tensor calculation, but its ringed scalar-model APIs do not directly identify the fixed
ModuleCat-valued etale tensorators and adjoint compositor in this statement. That remaining
compatibility is now a precise standalone theorem. The identity tensor clause does not need an
independent representative calculation; it follows formally from the composition clause.
The current item had one hole and a proof queue row, rather than a zero-hole repair.

## New nodes

`lem-coef-etale-scalar-tensor-composition` records the sole remaining hole, a generic normalized
etale tensor-compositor square, extracted from original step 7.

`lem-coef-etale-scalar-tensor-identity` records the proved identity square and its reduction to
tensor composition by naturality and cancellation.

`lem-coef-etale-scalar-unit-identity` records the proved regular-unit identity equation using
exact-degree-zero adjunction insertion. There are no definition or statement change records.

`lem-coef-etale-domain-pullback-calculus` records the fully proved generic pullback package.
It keeps the existing pullback route and avoids repeating the expensive calculation after
finite coefficient specialization. It adds no hole.

`lem-coef-finite-hom-monoidal-assembly` and `lem-coef-finite-hom-pullback-assembly` attach
the two fully proved private implementation modules. They record the existing finite
specializations; they introduce no public declarations and no proof holes. The delivery
format requires a node attachment for every new module, including private proof modules.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 5 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.EtaleDomainPullbackCalculus": "ee09cf7a5182fc4651c02b9ba18baad3ef61486c", "Sheaf.Paper.EtaleScalarTensorComposition": "83cbdbb6efe35b4137bdf2bc4120fb963c2e61f0", "Sheaf.Paper.EtaleScalarTensorIdentity": "7519f53e73623448caf87cf24f0ba9cb5a15f033", "Sheaf.Paper.EtaleScalarUnitIdentity": "c3379a057890e2eb1bdda0c06adca3e155ffcb2d", "Sheaf.Paper.FiniteHomDomainCalculus": "dd36c40787f78a59b91c4278ce39d02256b1dd1d", "Sheaf.Paper.FiniteHomDomainMonoidalProof": "48adf4dbcc5a27a07d629626fe2e5b3086d6ae68", "Sheaf.Paper.FiniteHomDomainPullbackProof": "693c10943cd1a0d80606a6cfd00bdac681687ac4"}, "results": {"Sheaf.Paper.CoefFiniteHomSiteDescent": {"hash": "9ff436f0b1d6dc4ddb9c634bdd3c73cfc7c9f0b6", "status": "OK"}, "Sheaf.Paper.CoefficientHomTensorSquare": {"hash": "cd58d5864e39da22c0f9ec26a38f95f345064b31", "status": "INFRA"}, "Sheaf.Paper.EtaleLisseHomReduction": {"hash": "7d7f463603e120febe4174e91bd3672466e8fc2a", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientHomChange": {"hash": "6040c31ddad1fd61407da5e854c90f3fc5f5636b", "status": "OK"}, "Sheaf.Paper.GeneralHomComparisonCocycles": {"hash": "d868c7f7d9bcfda76be62f0fec6e271641b39e6e", "status": "OK"}, "Sheaf.SixFunctors.FiniteCoefficientVerdier": {"hash": "a341c16bfa184e1bf084d648c57b274c9f44a6de", "status": "OK"}}, "seconds": 266, "time": "2026-10-28T12:42:52+0800", "transitive": 1, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
