# picard_h1_local_section_of_base_descent_generator

## Reason

Repair the returned equivalent-generator auxiliary: its theorem is now proved from
fibre triviality and local lifting of an arbitrary prescribed section. The general
reflection-of-generation theorem is proved. No existing interface is changed.

## Old

No declaration or module existed on sheaf-dag. The returned sandbox version stated
`picard_h1_local_section_of_base_descent_generator` with the parent's hypotheses and
local-generation conclusion, leaving its whole proof sorry.

## New

The generator signature stays unchanged. Its proof combines
`picard_h1_base_descent_fibre_generator` and
`picard_h1_base_descent_section_lifting` (the two new, separate geometric holes), then
`Modules.tensorPullback_generatesAt_reflects` (proved). The two holes have their own
modules, source-backed proof docstrings and DAG nodes. The latter lifts an arbitrary
prescribed fibre section; it does not assert generation, and permits a neighbourhood
depending on the section.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | J1 | unchanged signature; uses the proved generator auxiliary |

No existing dependent module needs a forced adaptation.

## Status

landed 20261013T022417-L-3214746 2026-10-13 (merge of deliver/J1/Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent)
