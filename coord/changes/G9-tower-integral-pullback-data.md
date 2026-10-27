# Integral pullback data and derived transport interfaces

Item: `Sheaf.Paper.TowerIntegralClassPullback` (G9).

The nine public constructions originally preceding `tower_integralClass_pullback` move
verbatim to the new module `Sheaf.Paper.TowerIntegralPullbackData`. The assigned module
publicly imports that module and retains all three original public imports. Names,
signatures, attributes and construction bodies are preserved; only their documentation's
blueprint ownership changes. The original theorem statement is unchanged.

The separation permits proved realization and pullback-square interfaces to import the
constructions without a cycle. The canonical derived single and shift endpoint maps have
explicit objectwise source types before specialization. These definitions retain the
original composites and avoid repeated expensive conversion of composed functors.

No other existing Lean module is modified. The direct consumers are
`Sheaf.Paper.TowerChernPullbackData` and `Sheaf.Paper.TowerChernRealizationPullback`.
Their originals are compiled against the delivery, and unchanged validation copies are
removed before delivery. No forced adaptation or extra claim is needed.

The assigned DAG node retains the theorem. The new data node owns the moved constructions;
the realization and square nodes own their new proved interfaces. No DAG node or unit
route is deleted. The report lists the single new ordinary site-endpoint obligation.
