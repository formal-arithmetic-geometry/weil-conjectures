## What changed

Replaced the proof of `AlgebraicGeometry.polynomial_chart_local_algebra` without changing its
signature, universe or visibility. Its ring and local map are now concrete constructions in
`Sheaf.AlgebraicGeometry.PolynomialChartFibreStalk`: a residue-field base change of the chart,
followed by the inverse stalk isomorphism of the open fibre inclusion. No data is chosen from
an unproved existence theorem. This module proves regularity and quasi-finiteness of that map.

`Sheaf.AlgebraicGeometry.PolynomialChartFibreDimensions` proves both local dimensions and the
topological dimension formulas. It uses the existing finite-type field dimension formula,
Mathlib's quasi-finite residue-field finiteness and transcendence-degree tower formula, and
the proved source-library smooth relative dimension theorem. Private helpers in the original
module prove the dimension inequality and zero-dimensional closed fibre directly from
quasi-finite incomparability. They follow the already proved local argument in
`Sheaf.AlgebraicGeometry.Morphisms.RegularLocalSurfaceDepthTwoFlat`.

The original module adds proof-only imports of Mathlib's Noetherian morphisms module and the
new dimension and flatness modules. Original public imports are unchanged. No existing
statement or definition is changed; no forced adaptations or change records are required.
Four Lean modules compile together with the launcher compiler. All new nodes carry the
three required kinds of search; LeanSearch was unavailable, while LeanFinder, Loogle and
local grep found ingredients rather than an existing combined theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.polynomial_chart_local_algebra` (one of one),
by a complete Lean proof from the stated flatness comparison and proved constructions and
dimension formulas. Added exactly one hole:
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison`, in
`Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparison`, node
`lem-sbc-polynomial-chart-stalk-flat-comparison`.

This is a decomposition: one upper hole closed, one strictly smaller lower hole added,
net zero holes. The new theorem concerns only flatness of the specified canonical map;
it supplies none of the original regularity, existence, Noetherian, quasi-finite closed-fibre,
dimension or inequality conclusions. The construction and these conclusions have real Lean
proofs. The imported field dimension theorem is now proved in the compiled baseline: the axiom
check of `polynomial_chart_fibre_dimensions` contains only the three permitted axioms.
There are no other sorries in the delivery, including the definitions and private helpers.

Proved new public declarations include
`AlgebraicGeometry.PolynomialChart.fibreInclusion_fiberι`,
`AlgebraicGeometry.PolynomialChart.fibreInclusion_asFiber`,
`AlgebraicGeometry.PolynomialChart.quasiFinite_stalkMap`,
`AlgebraicGeometry.PolynomialChart.isRegularLocalRing_sourceStalk`, and
`AlgebraicGeometry.polynomial_chart_fibre_dimensions`; the associated local-hom and
base-change instances are also proved.

The remaining comparison has a complete proof in words, using the local tower of stalks
and the existing local fibre flatness criterion. The outstanding implementation is compatible
quotient/stalk base-change isomorphisms and the algebra/module structures for that criterion.
Its statement was checked against the source criterion, including arbitrary non-Noetherian
base rings. Edge cases: when n=0 the polynomial fibre stalk is a field and flatness agrees
with the assumed flat restriction of f; generic image primes likewise give a field stalk;
nonclosed points retain the residue transcendence degree t rather than assuming t=0;
an empty U has no point x. Quasi-finiteness is unnecessary for the remaining comparison.

## No longer needed

No original public import was removed. The proof route no longer needs these planned nodes
or their statement modules:

- `lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite`,
  `Sheaf.RingTheory.IsolatedPrimeResidueFinite`: use Mathlib's finite residue extension for
  a quasi-finite algebra directly.
- `lem-weil-pbc-dimension-inequality-quasi-finite`,
  `Sheaf.RingTheory.QuasiFiniteLocalDimension`: the private proof uses strict monotonicity
  of prime contraction and proves the closed-fibre dimension directly.
- `lem-weil-pbc-fibre-product-affine-spectra`: an explicit tensor-product presentation of
  the affine fibre is unnecessary; categorical pullbacks and affine-space base change suffice.
- `lem-weil-pbc-standard-smooth-over-field-dimension-at-points`,
  `Sheaf.RingTheory.StandardSmoothDimensionAtPoints`: use the already proved
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` theorem
  `topologicalKrullDimAt_eq_of_smoothOfRelativeDimension` directly.

The regular polynomial, stalk localization, field dimension and open-subspace dimension
facts remain mathematical ingredients, mostly through Mathlib or proved source-library
results rather than extra Sheaf imports. The flatness criterion remains needed under the
new flatness comparison node. These are route-local pruning claims, not assertions that
other targets cannot use the named modules. No blueprint unit statement or realized step
was removed or bypassed; the local polynomial-chart route is retained.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or tool workaround. The DAG's isolated-prime residue finiteness and
quasi-finite dimension nodes are unnecessary for this implementation. The dimension step
can be proved without flatness of f and without local finite presentation of f; the original
theorem's assumptions stay unchanged. The new flatness comparison needs explicit compatible
stalk quotient identifications, which are not supplied directly by the planned criterion;
these form the remaining, strictly smaller obligation.

## New nodes

`lem-sbc-polynomial-chart-canonical-fibre-stalk` records the concrete fibre inclusion,
base changed chart, source stalk and transported map, with locality, quasi-finiteness and
regularity proved in `PolynomialChartFibreStalk.lean`. Its primary declaration is
`AlgebraicGeometry.PolynomialChart.isRegularLocalRing_sourceStalk`.

`lem-sbc-polynomial-chart-fibre-dimensions` records the proved natural-number local
and topological dimension formulas, in `PolynomialChartFibreDimensions.lean`.

`lem-sbc-polynomial-chart-stalk-flat-comparison` records the only new sorry, the equivalence
between the original chart stalk's flatness and the canonical closed-fibre map's flatness,
in `PolynomialChartStalkFlatComparison.lean`. Its proof in words is the local criterion
of Stacks Tag 00R7 as applied in Tag 00RH. All three nodes inherit the original unit and
blueprint ancestry. The original node's proof, proof_deps and proof_origin now follow
this reduction. There are no change records.

## Second reading by K2

1. **Unchanged interface: pass.** Read the repository and sandbox versions and their diff.
   The only existing declaration is `AlgebraicGeometry.polynomial_chart_local_algebra`;
   its signature, docstring, universe and public visibility are byte-for-byte unchanged.
   All seven original public imports remain. The additions to this file are three plain
   proof imports, two private proved helpers and its proof body. None of the three other
   delivered modules exists in the reviewed repository baseline. No target, existing
   definition, or foreign module is changed, and no change record is needed.

2. **Proof and construction: pass as a decomposition.** Ran `lcompile.py --all` on all four
   files; each compiled without errors or warnings. Read every definition and proof.
   `fibreInclusion` and `fibreMap` are pullback composites, `fibrePoint` uses the proved
   fibre homeomorphism, `sourceStalk` is the actual polynomial fibre stalk, and `stalkMap`
   composes the chart stalk map with an inverse open-immersion stalk isomorphism and point
   transport. There is no arbitrary witness from an unproved existence statement.
   `Spec.map_surjective` in the dimension proof is proved fullness of the affine spectrum
   functor; it introduces the actual ring map of the given morphism.
   A scratch axiom check covered these five definitions, the three fibre comparison
   lemmas, quasi-finiteness, regularity, the dimension theorem, the remaining comparison,
   and the item. Every construction, regularity, quasi-finiteness and dimension declaration
   uses only `propext`, `Classical.choice`, `Quot.sound`. Only the remaining comparison and
   the item also use `sorryAx`. The sole literal sorry is the named public flatness theorem
   already listed above; no definition or private helper contains a hole or forbidden code.

3. **Split statements and source: pass.** Read [00R7](https://stacks.math.columbia.edu/tag/00R7),
   [00RH](https://stacks.math.columbia.edu/tag/00RH),
   [00RE](https://stacks.math.columbia.edu/tag/00RE), and
   [00P1](https://stacks.math.columbia.edu/tag/00P1), and the actual declarations of
   `Module.flat_of_flat_closedFiber` and
   `topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`.
   The only unproved split-off statement is flatness of the specified canonical map,
   without the regularity, dimension, quasi-finiteness, or existential conclusions.
   It is strictly smaller than the item. For 00R7 set R=A=O_T,p, S=P=O_AffineSpace,e(x),
   S'=B=O_U,x and M=B. The scheme stalk maps are local; P and B are essentially finitely
   presented over A; B is nonzero and finitely presented over itself; f-flatness and the
   open immersion give A-flatness. The two closed-fibre quotients are the fibre stalks
   used here, with the chart-induced quotient map and the open stalk isomorphism.
   Thus the docstring supplies the full mathematical reduction, without a Noetherian
   base assumption. Its remaining Lean work is compatibility of these identifications.
   Repeated searches with different wording using LeanFinder, Loogle and launcher grep,
   and `rg` in Sheaf and the upstream geometry/ring theory files, found stalk-flatness
   and smooth-fibre ingredients, but no theorem proving this chart/fibre equivalence.
   Checked n=0 (P/m_A P is a field and the original chart is the flat restriction of f),
   a generic polynomial image (d=0, t=n), nonclosed images (t may be positive), arbitrary
   non-Noetherian bases, and empty U (no x). No hidden closed-point or nonempty-open
   assumption occurs. The two other new statements are fully proved, not new holes.

4. **Top-down route and pruning: pass.** The item explicitly constructs R and phi, obtains
   the dimension witnesses from the proved dimension theorem, derives the inequality
   and zero-dimensional closed fibre by quasi-finite prime incomparability, and invokes
   the smaller flatness comparison only for its last conjunct. `hI` in the private fibre
   proof prevents the zero-ring edge case and gives dimension exactly zero.
   The dimension proof uses the already proved smooth polynomial dimension result and
   the finite residue extension, rather than the planned isolated-prime or standard-smooth
   obligations. All added proof-only imports are plain `import`; public imports of new
   modules provide declarations used in their public signatures or definitions.
   Compared all ten old proof dependencies: the four unused planned nodes are explicitly
   listed in `No longer needed`. The other six remain through the new nodes: scheme fibre,
   stalk localization and polynomial regularity through the construction node; field
   dimension and open-subspace dimension through the dimension node; and the fibre
   flatness criterion through the comparison node. They are not claimed to be pruned.
   `dag/units/sk-prop-normal-form.json` has `realized.statement=[]` and
   `realized.steps=[[],[]]`; no realized node is bypassed or removed, and the inherited
   `sbc-lem-slicing` polynomial-chart route and blueprint ancestry are preserved.

5. **DAG agreement: pass.** The original node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its three steps match the construction, dimension/incomparability,
   and flatness assembly in Lean. Read all three new nodes and checked their statements,
   source, chapter/unit, blueprint ancestry, creation records, searches, Lean records,
   proof steps and dependency unions. The construction node records the canonical map
   and its proved properties; the dimension node records both local and topological
   dimension formulas; the flatness node names precisely the only new hole and cites
   the existing fibre criterion. Each dependency used in their plans supplies the
   claimed mathematical ingredient, with Mathlib replacing the elementary localization
   and regularity implementations as recorded in the proofs.

**Changes by the second reader:** corrected the report's stale claim that the imported
field dimension theorem remains open: its current axiom closure is fully proved. Added
this independent reading and the explicit accounting of the six retained old dependencies.
No Lean proof, statement, definition, import or node required repair. The one remaining
flatness comparison needs compatible stalk/quotient constructions and is not a short
lemma application; it remains the single declared split-off obligation. Hole accounting
is one original hole closed, one smaller hole added, net zero, not an axiom-free proof
of the original item.
