## What changed

Reduced `WeilConjectures.coefFiniteHomSiteDescent_coherence` to three strictly smaller
source obligations, preserving its exact statement. The assembled proof now:

- proves existence and the precise Koszul components of the etale symmetric structure
  from the already normalized closed data and the published derived symmetric structure;
- obtains the geometric tensor data from `finiteHomSiteTensorCoherence`;
- uses `finiteHomDomain_flatModel` to preserve finite-Tor constructibility under reduction;
- applies `finiteHomSiteHomInvertible` at the original and reduced pairs;
- proves the displayed Hom square by `coefficientHomTensorSquare`, using only the
  tensor equation extracted from the monoidal square;
- applies `finiteHomSiteEquationDescent` with the existing proved constructible descent
  theorem and the just-constructed squares, then assembles the original conclusion.

`CoefficientHomTensorSquare` contains a complete, proved categorical calculation for
specified right tensor-Hom adjunctions. Uncurrying the comparisons reduces them to
images of evaluation; precomposition with the forward site component cancels the
inverse in the contravariant input; the tensor square and naturality of the site
isomorphism at evaluation finish the calculation. This proof needs neither symmetry,
unit data, constructibility, nor invertibility of any scalar-Hom map.

The fixed definitions were moved verbatim into `CoefFiniteHomSiteDescentData` to avoid
an import cycle with the three component modules. The item publicly reexports that
module, including every original public import. No existing declaration signature,
definition body, instance, global attribute, or target statement changes. Existing
private support/Tor-isomorphism helpers and the proved descent theorem are retained.

Change record: `coord/changes/F1-finite-hom-site-coherence-components.md`.

Validation: all six delivered modules compile individually within 60 seconds.
All five direct importers compile unchanged against the packet:
`FiniteCoefficientHomChange` (54.5 s), `FiniteReductionOfPurity` (56.0 s),
`NormalizedSmoothOrientationUnits` (25.1 s), `FiniteIntrinsicVerdierBounds` (26.0 s),
and `CoefFiniteSiteHomTransport` (12.9 s). Their temporary copies were removed.
All three existing public theorem signatures are textually unchanged; each relocated
definition body is byte-identical; all delivered node signatures match the delivery
parser. The original item compiled in 18.8 s before changes.

## Proved and sorry left

Original item: one hole, in `WeilConjectures.coefFiniteHomSiteDescent_coherence`.
That hole is closed by a compiling reduction; it is a decomposition, not a complete
proof of the geometric coherence theorem. The item now has zero holes. The existing
`WeilConjectures.coefFiniteHomSiteDescent_descent` and final assembly remain proved.

New proved public theorem: `WeilConjectures.coefficientHomTensorSquare`
(node `lem-coef-right-closed-tensor-square`). Its private evaluation and composite
calculation helpers are also completely proved. The private etale symmetric witness
lemma in the item is completely proved.

Three new holes remain, each the whole proof of its one public theorem:

- `WeilConjectures.finiteHomSiteTensorCoherence`, node
  `lem-coef-finite-hom-site-tensor-coherence`: geometric normalization and tensor coherence
  of source steps 2--4; no Hom square or equation descent in its conclusion.
- `WeilConjectures.finiteHomSiteHomInvertible`, node
  `lem-coef-finite-hom-site-hom-invertible`: identify the finite-duality comparison with
  the fixed evaluation-defined intrinsic map, step 5. The second input only needs
  bounded constructibility.
- `WeilConjectures.finiteHomSiteEquationDescent`, node
  `lem-coef-finite-hom-site-equation-descent`: descend the laws and tower equations,
  step 7, assuming the already supplied descent and the fixed monoidal/Hom squares.

Holes closed: 1. Holes added: 3. Net hole reduction: -2. No hole occurs in a definition,
private declaration, or partial proof. This is a source-based decomposition with a
proved categorical square and an explicit quotient-domain reduction.

## No longer needed

No module is withdrawn or globally pruned. All original public imports are preserved
by reexport from the data module. No proof-only import has been retained unused.

The coherence component no longer directly needs
`lem-sf-proetale-constructible-origin` or `lem-sf-comparison-tor-amplitude`; it calls
the already proved `lem-coef-finite-hom-site-descent-core-descent` instead. Those
results remain needed by descent and are not claimed pruned from the library.

The displayed Hom square itself does not need
`lem-coef-monoidal-square-hom-transport`, symmetry or monoidal-unit axioms: the proved
right-closed tensor-square calculation uses the tensor equation alone. The generic
transport node remains a dependency of the smaller equation-descent obligation.
The other original geometric dependencies remain in the tensor-normalization and
Hom-invertibility component plans; no such dependency is claimed obsolete.

## Where the brief, the DAG or earlier work was wrong

The existing categorical transport statement uses Mathlib's left closed structure,
whereas the finite coefficient arrows are transposes in a specified right closed
structure. They are not definitionally interchangeable. The new proved bridge
handles the square directly with the actual right adjunctions; the law-descent
obligation explicitly retains the signed-symmetry identification it needs.

The original single coherence hole grouped geometric tensor normalization,
identification of two coefficient-module encodings, the formal square, and descent
of equations. These are distinct steps. The reduction makes the formal square
complete and leaves the three genuinely geometric/transport obligations named.
No false statement or need to change the unit route was found. Identity quotients
are included throughout; no quotient-flatness or scalar-Hom invertibility was added.
The recorded old missing-file build error is historical: the current original item
compiled successfully before changes.

## New nodes

`def-coef-finite-hom-site-descent-data` records the existing fixed predicates and
canonical arrows, relocated verbatim to a publicly reexported data module. It adds
no mathematical assumption or construction.

`lem-coef-right-closed-tensor-square` records the proved general evaluation-transpose
calculation, strictly below the finite-site theorem and independent of its geometric
hypotheses.

`lem-coef-finite-hom-site-tensor-coherence` records source steps 2--4, with the
already-proved etale Koszul structure supplied as input.

`lem-coef-finite-hom-site-hom-invertible` records the normalization part of step 5
for the exact intrinsic site map, using finite-duality site comparison.

`lem-coef-finite-hom-site-equation-descent` records step 7 with explicit inputs for
descent, monoidal squares, quotient coherence and invertible site Hom squares.

All five nodes retain the parent's chapter and unit. The parent coherence proof
record follows the actual Lean assembly; the main node's Lean declaration list
points only to declarations remaining in that module. The relocated definitions
are attached to the new data node. No adopted-source module is edited.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.CoefFiniteHomSiteDescent": "9ff436f0b1d6dc4ddb9c634bdd3c73cfc7c9f0b6", "Sheaf.Paper.CoefFiniteHomSiteDescentData": "082c6641edbc2f97839a4a4a9d1087a0fccb4d42", "Sheaf.Paper.CoefficientHomTensorSquare": "cd58d5864e39da22c0f9ec26a38f95f345064b31", "Sheaf.Paper.FiniteHomSiteEquationDescent": "ded931d93cb66961bafb0bcd8546459a1a662c7b", "Sheaf.Paper.FiniteHomSiteHomInvertible": "c09ced6a1878f303bbec7ad9500e83da25ca1e9b", "Sheaf.Paper.FiniteHomSiteTensorCoherence": "ca6649abf2d2c3fdc3b49a112a0e5ccc04a74bdc"}, "results": {"Sheaf.Paper.CoefFiniteSiteHomTransport": {"hash": "25a7089419505644db4b0e43dac819a1a1a1de9d", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientHomChange": {"hash": "6040c31ddad1fd61407da5e854c90f3fc5f5636b", "status": "OK"}, "Sheaf.Paper.FiniteReductionOfPurity": {"hash": "4620554d4463beb678ddc465f0cb6a592be1f51e", "status": "OK"}, "Sheaf.Paper.NormalizedSmoothOrientationUnits": {"hash": "33f1e2787018a3fa04fc9e87753cb2c3e43d4ced", "status": "OK"}, "Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds": {"hash": "7626d3590cf3bc4e79653aa04822e4946e4c7c0c", "status": "OK"}}, "seconds": 136, "time": "2026-10-28T08:03:51+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
