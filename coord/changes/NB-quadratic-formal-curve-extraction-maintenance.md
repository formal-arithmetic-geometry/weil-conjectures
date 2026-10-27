# Quadratic formal-curve dependency extraction

Maintenance repair for NB lem-sfb-quadratic-coefficient-proj-branches, returned head d5db8d844923 (H2/H13).

The retained worker repair was correct but delivery of another node only carries lean on a dependency node, dropping the required normalization stmt_deps citation. The shared extraction is landed first as maintainer-owned dependency maintenance. Both normalization and the next coefficient-chart item can now cite def-sfb-quadratic-formal-curve within the existing delivery contract.

All six abbreviation declarations are unchanged. QuadraticSeriesIntegralClosure publicly re-exports QuadraticFormalCurve; the normalization theorem and its docstring/proof are unchanged. The new definition node owns the six abbreviations, and the normalization stmt_deps cites it. Original coefficient-chart item, claim and return remain for the worker to deliver normally.

The ordinary per-file merger was also tested and refused the extraction at the first new module because the old module still declared the moved names. Its failed landing restored everything. The existing land_set.sh supports the required atomic move, compiles files separately using lean_file.sh at 60 seconds, checks imports, and registers one interface landing for global verification. No delivery, landing or review tool was changed.

Validation: byte comparisons of six abbreviation bodies and the complete normalization theorem; deliver2 dry-run/preflight of the dependency item; clean separate server compiles of both modules, NodalLocalAlgebraComparison and QuadraticCoefficientProjBranches; land_set per-file compile and import checks. Full-library verification remains the normal build service's responsibility.
