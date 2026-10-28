# Change record: complete chart proof decomposition

## Reason

The complete standard-chart proof depends on independent injectivity and surjectivity
arguments. The existing target had one deferred hole and no Lean declarations for these
component conclusions.

## Old

`ProjScalarExtensionTwistChartBasic` contained only the target theorem with a `sorry`
and imported the chart-calculus modules directly.

## New

Two public component modules state the injective and surjective halves, each with its
own DAG node and deferred proof. The target combines them using the constructor for
`Function.Bijective`; its signature and hypotheses are unchanged.

## Users

The target module is the only existing user. Its direct proof-only imports were moved
behind the two component modules; the public `ProjScalarExtensionTwistData` and Proj
functor imports remain available to the target statement.

## Status

The three modules compile in import order. The target hole is closed by decomposition;
the two component theorem holes remain for later stage-3 workers.
