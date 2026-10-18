# Sheaf.Topology.SpectralLimitPullbackSections proof scope

## Reason

The stage-3 static interface check requires a record for the added namespace-opening
command. The proof uses the presheaf stalk and sheafification APIs through
`open TopCat.Presheaf`. This is lexical name resolution inside the existing
`TopCat.Sheaf` namespace. It exports no notation, instance, attribute or declaration.
All added declarations are private; all existing public signatures and all public
imports are identical. The local `set_option ... in` commands only affect their
following proof declarations. There is no definition or statement repair.

## Old

```lean
namespace TopCat.Sheaf

open Classical in
```

## New

```lean
namespace TopCat.Sheaf

open TopCat.Presheaf
```

The original `open Classical in` remains immediately before the public theorem.
The intervening declarations are private, fully proved proof helpers. In particular,
`TopCat.Sheaf.spectralLimit_pullback_sections` has exactly its original signature.

## Users

`tools/downstream.py Sheaf.Topology.SpectralLimitPullbackSections --uses
spectralLimit_pullback_sections` lists the following eight downstream modules and
finds no use of the declaration outside its own module. None needs adaptation:
namespace-opening commands do not propagate through Lean imports. The holding
column is inapplicable to these unchanged modules; no claim or adaptation is made.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SpectralLimitPullbackSections | T4 | Proof completed; signature identical. |
| Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite | not adapted | No interface change. |
| Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective | not adapted | No interface change. |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit | not adapted | No interface change. |
| Sheaf.Topology.SpectralFiniteCoequalizer | not adapted | No interface change. |
| Sheaf.Topology.SpectralFiniteCoequalizerEmbedsConstant | not adapted | No interface change. |
| Sheaf.Topology.SpectralLimitCohomology | not adapted | No interface change. |
| Sheaf.Topology.SpectralLimitSheafSections | not adapted | No interface change. |
| Sheaf.Topology.SpectralSheafColimitConstantEmbeddings | not adapted | No interface change. |

No target statement or definition changes, so this proof-scope addition does not
reopen statement review. The module compiles cleanly via `lcompile.py`; the maintainer's
global build will independently check all consumers after landing.

## Status

landed 20261018T062919-L-680190 2026-10-18 (merge of deliver/T4/Sheaf.Topology.SpectralLimitPullbackSections)
