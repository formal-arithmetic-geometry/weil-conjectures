# IntegralAmbientOperationModels proof-import isolation

## Reason

Reviewer C-835f8 returned head 835f89f87a8 because the added private import of
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` exposes its public semilinear
instances to `import all` consumers of the ambient module. In particular, the
original `Sheaf.Paper.PointIntegralTensorChain` fails at lines 53:80 and 62:2 with
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u … EssentiallySmall`.
The baseline paired compile reproduced both errors (result
`f70d1ede5fc5871b54783a14`).

The first repair added the reviewer's two instance removals to that consumer,
and compiled it successfully. Head d9fdf4b33d0 did not land: the consumer and its
`PointFibreDerivedTensorModels` dependency had been quarantined on 2026-10-26 at
10:20:36 UTC for the separate ProjectiveLineExceptionalBaseChange dependency
failure. The landing gate therefore refused the missing import source.

This repair uses the reviewer's alternative: prevent the new import from reaching
`import all` consumers. The new proved cochain interface imports the independent
ringed-pullback implementation privately. The ambient module imports only that
interface; its proof transports the resulting cochain counit along the same
left-adjoint isomorphism. The proof and mathematical content are unchanged.
The interface combines the existing ringed-pullback theorem and universal cochain
counit transport, with zero new holes. It is introduced for import isolation,
not compile timing.

Validation: result `d75d38e4faafa808101aecc0` compiles the new interface in 9.7 seconds
and the ambient module in 48.6 seconds with no errors or warnings. Result
`0d37ec7a9ea3c8d9897d37dd` checks that neither semilinear instance is active after
`import all Sheaf.Paper.IntegralAmbientOperationModels` (5.2 seconds), then compiles
the unchanged archived consumer against the repaired sibling ambient module
(44.4 seconds, no errors or warnings). The temporary consumer is byte-identical
to its current quarantine archive and is not delivered.

The quarantined modules are preserved: no archive, declaration, node attachment
or dependency is removed, no empty restoration is made, and no deleted.txt is
used. The previous consumer adaptation is omitted from this packet because its
necessity is removed at the importing module. This is not a withdrawal of the
consumer from the library or DAG.

## Old

In the returned ambient module:

```lean
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.CategoryTheory.CochainUniversalCounitTransport
```

The proof directly obtained a homotopy counit from the first theorem, transported
it using the second, and then postcomposed with the pullback isomorphism.

## New

In the ambient module:

```lean
import Sheaf.CategoryTheory.RingedPullbackCochainPresentation
```

The new interface privately imports both proof dependencies and proves
`SheafOfModules.ringedPullbackCochainPresentation`. Its public statement uses the
actual Mathlib module-sheaf categories and contains only cochain universality and
invertibility on flat-term K-flat complexes. The ambient proof obtains this
cochain counit and postcomposes with its original pullback isomorphism.
No ambient public signature or definition changes relative to the returned head.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralAmbientOperationModels` | S7 | obtains the same universal cochain derived data through the proved interface; both leaking instances are absent from its import-all environment |
| `Sheaf.Paper.PointIntegralTensorChain` | unclaimed; quarantined | original archived source preserved; no instance removals or other adaptation delivered |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | quarantined | source archive and dependencies preserved; no restoration or adaptation delivered |
| `Sheaf.CategoryTheory.RingedPullbackCochainPresentation` | new, S7 | fully proved interface isolates semilinear proof imports |

## Status

landed 20261026T111926-L-1778770 2026-10-26 (merge of deliver/S7/Sheaf.Paper.IntegralAmbientOperationModels)
