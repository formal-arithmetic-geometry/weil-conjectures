## What changed

The statement of `AlgebraicGeometry.Scheme.adicPerfectModels_residueOrigin` is unchanged.
Its proof now separates completeness, bounds for K and its canonical residue, and
constructible etale origin of individual residue homology sheaves. The actual
bounded-heart devissage and the quotient-functor transport are proved in the item.

The private helper `bounded_residueOrigin` applies the existing proved
`DerivedCategory.prop_of_bounded` to the essential image of bounded constructible
etale objects. It reuses the existing proved private helper
`etaleOrigin_triangulated` from `Sheaf.Paper.AdicConstructibleTriangulated` via a
proof-only `import all`, rather than restating its proof. That helper uses the landed
Noetherian constructible extension theorem and bounded-below full faithfulness.
The proof then chooses the standard cochain preimage of the etale derived object,
transports its homology by `homologyFunctorFactors` and `Q.objObjPreimageIso`, widens
its bounds using min and max, and composes `mapDerivedCategoryFactors` with the
comparison isomorphism. No definitions or existing public interfaces were changed.

Three new modules each contain one named component theorem, with the proof source,
complete proof in words, and matching DAG node. All four modules compiled through
`lcompile.py`; the final item compiled in 10.1 seconds after removing redundant
proof imports. The delivery tool performs the required axiom and packet checks.

## Proved and sorry left

This is a decomposition, not a completed mathematical proof: one original hole is
closed by a complete Lean proof from three strictly smaller component statements.
There are zero literal holes in the item module and three holes in the delivery as
a whole; holes closed minus holes added is -2 before any broader closure accounting.

Closed: `AlgebraicGeometry.Scheme.adicPerfectModels_residueOrigin` (1 of 1 original
holes), using the following three new holes:

- `AlgebraicGeometry.Scheme.adicPerfectModels_completeness`, node
  `lem-sfb-adic-perfect-models-completeness`: only completeness, with no bounds or
  etale residue descent.
- `AlgebraicGeometry.Scheme.adicPerfectModels_cohomologicalBounds`, node
  `lem-sfb-adic-perfect-models-cohomological-bounds`: only two cohomological
  vanishing intervals, with no completeness or constructible descent.
- `AlgebraicGeometry.Scheme.adicPerfectModels_residueHomology`, node
  `lem-sfb-adic-perfect-models-residue-homology`: only descent of individual heart
  objects, with no derived descent, cohomological bounds, or completeness.

The private bounded-heart argument has a complete proof and adds no hole. In
particular the residue homology theorem does not merely rename the derived-origin
obligation: the finite Postnikov argument that assembles its sheaf antecedents,
the bounded etale representative, and all final isomorphisms are proved here.

## No longer needed

No existing module is withdrawn or globally pruned, and no original public import
is removed. Redundant proof imports of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure` were removed;
the final proof compiles through the remaining imports.

The original direct dependencies on the perfect-model calculation, completion-unit
detection, stratified bounds, Noetherian global constructibility, constructible
comparison, finite presentation, immersion limits and localization are needed
inside the corresponding new components. Their nodes therefore remain needed
transitively and are not claimed as pruning. The main node now cites the three
components and the proved full-faithfulness and constructible-extension results
used by its bounded-heart descent. No unit statement or realized unit step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed, and no correction to a definition or hypothesis is made.
The original geometric proof plan remains valid. Its local-to-global and scalar/site
normalization glue is now exposed as separate components; the remaining argument
is an explicit finite bounded-heart proof, without assuming a derived etale
antecedent in a new hypothesis.

Edge cases were checked when formulating the three components: empty schemes and
empty refinements use zero objects and interval [0,0]; zero complexes are allowed;
min/max handles unordered choices of local endpoints; the residue field may be
infinite, since finite-dimensional vector spaces are finitely presented. No
finite-underlying-set hypothesis on the residue field was introduced.

The automatic blueprint ancestry walk for the item is broken by an earlier
`created.item` that names a module instead of a node. The new records preserve the
explicit ancestor and route already recorded by the original item's reviewed
`blueprint.from`, namely `det-lem-integral-models-stacks`. Maintainer-owned ancestry
fields of the original node are not changed.

## New nodes

`lem-sfb-adic-perfect-models-completeness`, realized in
`Sheaf.Paper.AdicPerfectModelsCompleteness`, states only the completeness sentence
of Bhatt--Scholze Proposition 6.6.11, reverse implication. Its two proof steps use
the existing complete-model calculation and completion-unit detection.

`lem-sfb-adic-perfect-models-cohomological-bounds`, realized in
`Sheaf.Paper.AdicPerfectModelsCohomologicalBounds`, isolates finite-stratum
cohomological bounds for K and the normalized residue. Its plan combines the
existing local model calculation with stratified local cohomological bounds.

`lem-sfb-adic-perfect-models-residue-homology`, realized in
`Sheaf.Paper.AdicPerfectModelsResidueHomology`, isolates constructible etale origin
of each residue homology sheaf. Its plan uses local residue calculation,
Noetherian global constructibility and the sheaf comparison theorem. It makes no
assertion about splitting extensions or descending a derived object.

All three share the original paper source and the unit `sk-lem-integral-models`.
Whole-blueprint searches for perfect completeness, constructible cohomology and
stratified bounds found no node with any of these exact fixed-scalar component
statements. Mathlib searches are recorded from the actual search log. There are
no change records because no existing definition or public statement changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
