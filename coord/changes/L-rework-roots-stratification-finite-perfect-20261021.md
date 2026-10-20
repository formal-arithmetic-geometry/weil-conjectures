# Rework roots: Stratification port and FinitePerfectQuotientModels un-withdrawn (L, 2026-10-21)

Four rework roots, quarantined by upstream sync 5f7b33eac, each blocking about 1000 importers.

1. `Sheaf.Paper.LevelwiseAdicTruncations` (prop-weil-pbc-levelwise-truncations),
   `Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated`
   (lem-weil-constructible-coefficient-homology-triangulated) and
   `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` (def-pe-etale-constructible-module)
   used `LocallyClosedStratification`, which upstream commit e6847cd91 removed in favour of the existing
   `AlgebraicGeometry.Scheme.Stratification` (WeilConjectures/ConstructibleSheaf/Defs.lean). The fields are the
   same (n, stratum, locally closed, constructible, cover, disjoint, domain, immersion, range), so the name is
   replaced and nothing else changes; `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf` already uses it.
   The statements are unchanged in meaning.
2. `Sheaf.Paper.FinitePerfectAdicRealization` (lem-weil-pbc-finite-perfect-adic-realization) uses
   `FinitePerfectModelsCompatible` and `HasUniformFinitePerfectModels` from `Sheaf.Paper.FinitePerfectQuotientModels`.
   Delivery 6a40ea0e01 (W6) withdrew that module as unused because its consumer was in quarantine/, not in lean/.
   It was in fact used: the module text from 6a40ea0e01^ and the Lean attachment of node
   lem-weil-pbc-residue-perfect-finite-quotient-models are restored (its one sorry in
   residuePerfect_quotient_models_succ is back as an open hole).

All five files compile singly against the published build (tools/lean_file.sh, group RW mirror).
