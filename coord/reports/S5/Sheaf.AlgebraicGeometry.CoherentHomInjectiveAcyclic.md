## What changed

Proved `AlgebraicGeometry.coherent_hom_injective_acyclic` in
`Sheaf.AlgebraicGeometry.CoherentHomInjectiveAcyclic`, preserving its signature and the
three-step DAG proof. Install the declared flasqueness of internal Hom into an injective,
apply positive-degree flasque abelian cohomology vanishing, and transport subsingletonness
along the component of `zariskiModuleAbelianCohomologyNatural`. A module whose underlying
group is subsingleton is a zero object. The local enough-injectives and Ext instances
match those used by the natural comparison.

The source library also contains `moduleCup_flasque_acyclicity`, which packages the last
two steps. The direct proof here uses the three dependencies already declared in this
node and introduces no further dependency. No statement, definition, public import,
or DAG route changes.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.coherent_hom_injective_acyclic`
(`lem-sc-ext-coherent-hom-injective-acyclic`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module. The existing imported theorem
`AlgebraicGeometry.isFlasque_homObj_of_coherent_injective` remains a proof dependency;
this delivery does not claim to close that theorem or all transitive axioms.

## No longer needed

Removed private imports
`WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology` (the older objectwise
comparison is unnecessary because the natural comparison supplies the component) and
`Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` (a redundant re-export of the directly
imported source module). No declarations or modules are withdrawn. All three declared
proof-dependency nodes remain needed. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The current comparison node names the natural
comparison in the source library, and the proof uses that declaration directly.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
