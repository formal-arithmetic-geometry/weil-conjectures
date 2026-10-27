## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleTopologicalDimensionAtPoint` states
`AlgebraicGeometry.Scheme.Hom.topologicalKrullDimAt_eq_of_etale`, with proof `sorry`.
No definition, dependency repair, statement correction, or new node is needed.
The node copy changes only `lean`.

Clause-by-clause correspondence:

- Arbitrary schemes U and V: `{U V : Scheme.{u}}`, with `universe u` explicit.
- Morphism e from U to V: `(e : U ⟶ V)`.
- Etaleness: `[Etale e]`, the recorded Mathlib notion, equivalently flat,
  formally unramified, and locally of finite presentation by
  `Etale.iff_flat_and_formallyUnramified`.
- A point u of U: `(x : U)`; the variable is renamed to avoid colliding with
  the universe name. The node's v = e(u) is substituted directly as `e x`.
- Equality of topological dimensions at these points:
  `topologicalKrullDimAt x = topologicalKrullDimAt (e x)`.
  The recorded definition is exactly
  `⨅ (W : TopologicalSpace.Opens X) (_ : x ∈ W), topologicalKrullDim W`.
  The codomain `WithBot ℕ∞` includes infinity, and the infimum is the stated
  minimum in this well-ordered extended dimension range.
- No finite-type-over-a-field, Noetherian, quasi-compact, separated, or
  surjective hypothesis occurs. There is no hidden field or finite-dimension binder.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. The full class and its equivalence above were read.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`.
  Its full definition and docstring were read. This is dimension of
  neighbourhoods, not Krull dimension of the stalk ring.

Proof-dependency modules are plain imports, preserving the six-step DAG proof plan:
`Mathlib.AlgebraicGeometry.Properties` (scheme sobriety),
`Mathlib.Topology.KrullDimension` (`topologicalKrullDim`),
`Mathlib.AlgebraicGeometry.Fiber` (`Scheme.Hom.fiber`, its projections and homeomorphism),
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
(`Scheme.Hom.etale_fibre_discrete_separable_points`),
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (`UniversallyOpen.of_flat`),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (`Flat` and its stalk criterion),
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
(`Scheme.fromSpecStalk_local_properties`), and
`Mathlib.RingTheory.Ideal.GoingDown` (`Algebra.HasGoingDown.of_flat`).
The declaration docstring gives all six steps, including the finite-chain
interpretation, strictness from discrete fibres, flat going-down lifts staying
inside a source open, both neighbourhood infima, and infinite dimensions.

Source checked: `literature/stacks-project/descent.tex`,
`lemma-dimension-at-point-local`, lines 5172–5227 (Stacks Tag 04N4).
It has exactly the two schemes, étale morphism, point, and equality used here.

Edge cases checked mathematically before drafting:

- Empty source: the universally quantified point has no values; no Nonempty
  assumption is needed. Empty target cannot receive a nonempty source scheme.
- Identity and open immersions: the equality agrees with invariance under open
  restriction. Surjectivity is unnecessary; e.g. a proper open immersion is allowed.
- Dimension zero and arbitrary residue-field extensions: neither is excluded.
- Infinite dimension: both sides remain in `WithBot ℕ∞`, with no natural-number
  finiteness witness. Supremum arguments use finite chains of unbounded length.
- Arbitrary non-Noetherian/non-quasi-compact/non-separated schemes: no such
  typeclass constraints are imposed. The category of schemes uses its standard
  single arbitrary universe u, with no additional size restriction.

Searches performed:

1. `msearch.py N9 lem-sfb-etale-topological-dimension-at-point leanfinder
   "An etale morphism of schemes preserves topological Krull dimension at a point"`:
   eight hits for étale/smooth properties and affine étale loci; no matching theorem.
2. `msearch.py ... loogle '"topologicalKrullDimAt"'`: zero hits.
3. `msearch.py ... grep 'topologicalKrullDimAt|etale.*[Dd]im|[Dd]im.*etale'`:
   eighteen hits concerning relative dimension zero and standard-smooth charts;
   no neighbourhood-dimension invariance theorem.
4. `rg -n 'topologicalKrullDimAt' lean/WeilConjectures lean/Sheaf`, followed by
   contextual search in matching files for étale theorem names and `[Etale ...]`:
   the definition exists upstream. Other hits give field/smooth dimension
   formulae, open-immersion or homeomorphism helpers, algebraic-space chart
   comparisons, or zero-dimensional fibres. None states this arbitrary-scheme
   étale invariance result.
5. `rg -n 'lem-sfb-etale-topological-dimension-at-point' lean/WeilConjectures`:
   no existing blueprint-tagged declaration. Searches in `dag/lean_names_upstream.json`
   and both project roots for combined étale/local-dimension names also found none.
   The selected new declaration name does not already occur.

Validation: prescribed `scompile.py` compiled both sandbox and actual library
module cleanly (1.4 s and 1.5 s), without errors or warnings. Every universe and
variable is explicitly bound. The only theorem proof is `sorry`.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by N9

This is the dispatch worker's separate final self-check; the maintainer performs
an independent review after delivery, as the brief specifies. No other agent was
started.

Reopened the node and the final file. The hypothesis list has precisely two
schemes, one morphism, its etaleness, and one source point. The target point is
its image rather than an arbitrary extra point. Both occurrences of dimension
use the recorded neighbourhood definition, so this does not accidentally state
the distinct local-ring dimension theorem following Tag 04N4 in the source.
The equality retains the extended codomain and makes no finiteness assumption.
The proof-dependency imports and six-step docstring match the DAG plan.
No mismatch was found, and no mathematical statement was changed.
