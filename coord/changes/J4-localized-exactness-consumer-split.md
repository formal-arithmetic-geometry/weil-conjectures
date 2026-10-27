# Sheaf.Paper.AdicPullbackPresentationTransport and Sheaf.Paper.SfCbcExtensionZeroCompletion

## Reason

The required direct-consumer checks after narrowing the exactness import exposed
existing file-level compile costs. `AdicPullbackPresentationTransport` took 84 s
against the repair and 75 s against the original baseline; a profile located the
large kernel checks in constant and evaluation normalization. Its isolated first
part compiled in 19 s. `SfCbcExtensionZeroCompletion` took 67–83 s, with the kernel
checking its derived-factorization terms accounting for most of the cost.

Scoped irreducibility of the standard derived-category construction and stricter
transparency did not make both original files pass. Split complete, self-contained
construction portions into lower modules. The existing declaration names,
statements, proof bodies, definition bodies, instance registrations and original
public imports are preserved. Existing private helpers remain private and are
accessed with `import all`; the original local elaboration attributes needed by
the second half are restored locally. No new hole or axiom is introduced.

## Modules

Both existing modules were unclaimed when inspected.

- `Sheaf.Paper.AdicPullbackPresentationTransport` retains its main presentation
  theorem and transport, quotient, completion and open-mate consequences. It
  publicly imports `Sheaf.Paper.AdicPullbackPresentationModels`, which contains
  the existing coefficient uniqueness, universal models and normalized constant
  and evaluation comparisons. Its 18 moved public declarations are attached to
  `lem-cbc-adic-pullback-presentation-models`; the original node keeps its other
  14 declarations and its full original proof route.
- `Sheaf.Paper.SfCbcExtensionZeroCompletion` retains every existing hole and all
  completion, finite-reduction and realization comparisons. It publicly imports
  `Sheaf.Paper.SfCbcExtensionModel`, which contains the existing exact module
  equivalences, extension model and exact tower extension, all with complete
  proofs. Its 43 moved public declarations are attached to
  `lem-sf-cbc-extension-model`; the original node keeps its other 45 declarations
  and its full original proof route.

This is a compilation refactor of unclaimed Sheaf modules, not a change to the
mathematical route or a replacement of a proof by a hole. The combined old/new
sources have exactly the same declarations and hole counts (0 and 9,
respectively). No adopted `WeilConjectures` source is changed.

## Direct consumers

The following modules are checked unchanged against the split and are removed
from the packet after validation:

- `Sheaf.SixFunctors.ConstantScalarQuotientComparison` (unclaimed).
- `Sheaf.Paper.CompletedSupportIntermediateTowerCore` (unclaimed).
- `Sheaf.Paper.CompletedStrictOpenExchange` (unclaimed).
- `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` (unclaimed).


## Downstream proof-import repair

The unchanged direct consumer `Sheaf.Paper.CompletedStrictOpenExchange` also
exceeded the limit (66 s). It only uses
`adicPresentationTowerUniversal_proof`, now supplied by the lower construction
module. Replace its private proof import of `AdicPullbackPresentationTransport`
by `AdicPullbackPresentationModels`, and change its pre-existing
`backward.isDefEq.respectTransparency false` to `true`, so its already-declared
local irreducibility caches actually apply. All declarations, proof and definition
bodies, public imports and attributes remain verbatim. This unclaimed module
then compiled successfully (reported wall time 44.8 s). Its node's proof dependency
now names the actual lower construction node. This module is included in the
packet; the other three unchanged consumer copies are removed after checking.

## Old

All moved declaration signatures, proof bodies, definition bodies and attributes
are the original source text. The old import boundaries were:

```lean
-- AdicPullbackPresentationTransport.lean
import all Sheaf.Paper.OpenImmersionTensorPiece

-- SfCbcExtensionZeroCompletion.lean
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

-- CompletedStrictOpenExchange.lean
import Sheaf.Paper.AdicPullbackPresentationTransport
set_option backward.isDefEq.respectTransparency false
```

## New

The original signatures and bodies are preserved across each pair of files.
Only the construction declarations' module attachments and these import boundaries
change; the last option enables existing irreducibility caches.

```lean
-- AdicPullbackPresentationTransport.lean
import all Sheaf.Paper.OpenImmersionTensorPiece
public import Sheaf.Paper.AdicPullbackPresentationModels
import all Sheaf.Paper.AdicPullbackPresentationModels

-- SfCbcExtensionZeroCompletion.lean
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Sheaf.Paper.SfCbcExtensionModel
import all Sheaf.Paper.SfCbcExtensionModel

-- CompletedStrictOpenExchange.lean
import Sheaf.Paper.AdicPullbackPresentationModels
set_option backward.isDefEq.respectTransparency true
```

The new modules retain the original public section, universes and elaboration
scope. Local attributes effective after the old section boundary are restored
in the second half of the extension-by-zero file. In addition, the second half
erases the two private instances `sfCbcTensorTotal` and `sfCbcSliceTransport_additive`
of the closed `TensorTransport` section (`attribute [-instance]`, line 72). In the
original file these erasures ended with that section, so the instances were active
again in the second half. The erasure is not exported, and the reviewer compared
the published and split builds: the type of every public declaration in
`SfCbcExtensionZeroCompletion`, `AdicPullbackPresentationTransport`,
`CompletedStrictOpenExchange` and `LocalizedModuleExactIndependent` is identical
(Expr hash). Only auxiliary `_proof_n` lemmas and definition values differ, because
the auxiliary-proof cache is per module. All 30 direct importers compile against
the split (reviewer, 2026-10-27).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Retain the main theorem and transport consequences, re-export the moved constructions. |
| Sheaf.Paper.AdicPullbackPresentationModels | J4 | Existing proved normalized construction declarations, with no new hole. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Retain completion comparisons and all existing holes, re-export the exact models. |
| Sheaf.Paper.SfCbcExtensionModel | J4 | Existing proved exact-extension construction declarations, with no new hole. |
| Sheaf.Paper.CompletedStrictOpenExchange | unclaimed | Use the actual lower proof import and respect existing local irreducibility caches; compiled. |
| Sheaf.SixFunctors.ConstantScalarQuotientComparison | unclaimed | Compiled unchanged against the split; validation copy removed. |
| Sheaf.Paper.CompletedSupportIntermediateTowerCore | unclaimed | Compiled unchanged against the split; validation copy removed. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Compiled unchanged against the split; validation copy removed. |

## Status

landed 20261027T131459-L-2941620 2026-10-27 (merge of deliver/J4/Sheaf.Paper.RingedProjectionLocalBaseData)

All split modules and all four direct consumers compiled successfully through
the remote compiler and passed its per-file time check.
