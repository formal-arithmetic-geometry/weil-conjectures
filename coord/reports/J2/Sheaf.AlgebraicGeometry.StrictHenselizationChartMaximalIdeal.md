## What changed

Repaired `Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal`.
The theorem now constructs the comparison between the chosen small affine
strict-henselization ring and the full affine chart colimit with an explicit
`HasColimit D` instance, `Functor.Final.colimitIso`, and
`colimit.isoColimitCocone ⟨cn, hcn⟩`.  The resulting coprojection equation is
used by the existing chart compatibility and maximal-ideal transport proof.
The theorem statement, docstring, visibility, and imports are unchanged.
The existing node proof description and proof origin now record this explicit
comparison route.

## Proved and sorry left

`AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal` compiles with
a complete proof.  This repair closes 0 textual `sorry`s, adds 0 `sorry`s, and
leaves 0 `sorry`s in the delivered module.  No intermediate statements were
split off.

## No longer needed

No imports, nodes, or modules were removed.  The four recorded proof
dependencies remain needed: the affine chart and triple comparison, the strict
henselization triple colimit, the strict-henselization affine-ring construction,
and the structural-map equation.

## Where the brief, the DAG or earlier work was wrong

The earlier repair used a direct `coconePointUniqueUpToIso` expression whose
elaboration was sensitive to the restored upstream colimit interfaces.  The
explicit final-functor comparison is definitionally aligned with the actual
small affine diagram and makes the required `HasColimit D` witness explicit.
The prior global-build return therefore identified a real interface fragility;
the repaired route preserves the exact theorem statement and its unit route.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
