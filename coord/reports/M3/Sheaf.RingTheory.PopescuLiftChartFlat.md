## What changed

Replaced the sole `sorry` in `Algebra.popescu_lift_chart_flat` by a complete Lean
reduction along the existing Tag 07CP route. The existing statement, universes,
binders and visibility are unchanged. No existing dependency interface changes.

Added two modules:

- `Sheaf.RingTheory.PopescuLiftPartialChart`: explicit partial-chart equations,
  quotient, comparison map, prime and localization; explicit renumbering by
  `finSumFinEquiv`; proved quotient-equivalence and equation-count application.
  It also proves the polynomial key identity, local vanishing of every original
  equation, and pi-torsion of every other chart equation.
- `Sheaf.RingTheory.PopescuLiftChartComparison`: the remaining pi-divisibility
  calculation, followed by a proved annihilator argument and a proved comparison
  bijection. Its private generic localization lemma proves that a surjective ring
  map whose kernel vanishes in the source local ring induces a bijection of local
  rings, by lifting fractions and applying the localization zero criterion.

The item's private `polynomial_value` helper extends `hc` from variables using
`MvPolynomial.algHom_ext` between actual R-algebra maps. The main proof checks
membership of pi and non-membership of a_k in qD, applies chart flatness, uses
`RingHom.annihilator_element_flat_base_change` twice, obtains an R-algebra
comparison equivalence, transports `Module.Flat`, and proves the scalar tower for
`Module.flat_iff_of_isLocalization` at the base prime.

Read the online Stacks Tag 07CP, especially its displayed D_k presentation,
special-fibre identification and final conormal/kernel calculation. The source
TeX is absent locally, as the existing node's source record already says.

## Proved and sorry left

Closed the original hole: `Algebra.popescu_lift_chart_flat`, node
`lem-weil-pbc-popescu-lift-chart-flat`.

Added exactly two holes, each the entire proof of one public theorem in its own
new module, with source and complete proof in words:

- `Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension`, node
  `lem-weil-pbc-popescu-lift-partial-chart-dimension`: identify the special fibre
  and compute its topological dimension. It assumes neither annihilator equality
  nor flatness, and concerns the partial chart, not the final lifting algebra.
- `Algebra.PopescuLiftPresentation.chart_relations_pi_divisible`, node
  `lem-weil-pbc-popescu-lift-chart-relations`: show the other chart equations are
  divisible by pi locally. It assumes no flatness or annihilator equality and
  does not assert vanishing, bijectivity or flatness.

This is a decomposition, not an axiom-free proof of the original theorem: one
original hole closed and two smaller holes added (net -1 holes closed). All other
new definitions and helpers are proved without new holes. In particular,
`equation_key_identity`, `chart_original_equation_eq_zero`,
`chart_other_equation_pi_mul_eq_zero`, `partial_chart_flat`, and
`chart_comparison_bijective` have complete Lean proofs; the last two depend on
one of the stated new holes. No data are chosen from an unproved existence
statement: every chart, equation, quotient map and equivalence is constructed.

The complete sandbox compiles through `lcompile.py` in import order without
warnings. A scratch Lean check proves vanishing of the other equations when pi
is a unit, using only the already proved pi-torsion lemma. `#print axioms` for
`equation_key_identity`, `chart_original_equation_eq_zero` and
`chart_other_equation_pi_mul_eq_zero` lists only propext, Classical.choice and
Quot.sound. The delivery dry run also passes its declaration/axiom checks and
preflight, with the second reading left to the designated second reader.

## No longer needed

Removed these proof-only imports from the item's module:

- `Sheaf.RingTheory.EquationCountFibreDimensionFlat`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`

They are now imported by `PopescuLiftPartialChart`, where their statements apply.
They remain necessary in the targets' import closure; this is relocation of
proof dependencies, not pruning. The item now imports
`Sheaf.RingTheory.PopescuLiftChartComparison`. No node or module from the old
route is claimed globally pruned. The DAG retains the smoothness, differential,
localization and equation-count ingredients through the new dimension node.
No principal neighbourhood killing the kernel is introduced.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy or established mathematical error was found. The old
DAG treated constructing D_k and extending hc as elementary; these are now
explicit Lean constructions and proofs. The pre-existing dependency statements
do not themselves supply the special-fibre identification or the conormal
coefficient clearing calculation. Those strictly smaller parts are the two
remaining nodes, rather than another name for chart flatness.

Edge cases were checked before stating the reductions: m=0 makes the
pi-divisibility assertion vacuous and leaves the polynomial chart; E_k empty
uses empty sums and requires n-dimensional differential rank; E_k all indices
makes the normalized current-chart p equations zero and leaves n-|E_k|
coefficient variables plus |E_k| free auxiliary variables. For pi a unit the
special-fibre dimension hypotheses have no prime, while the independently proved
pi-torsion forces every other chart equation to vanish, so the divisibility
statement holds with y=0. For pi=0 the divisibility assertion really asserts
vanishing of the other chart equations; the conormal coefficient argument is
needed, and no cancellation by pi is used anywhere. Zero lifting algebras have
no prime q. The statements impose no Nontrivial or positive-cardinality assumptions.

The unit `sk-thm-p1` and its `realized` route are unchanged. This item is not one
of the unit's own realized statements or steps, and the reduction follows the
existing lifting-lemma subargument.

LeanSearch searches for both new statements returned Internal Server Error;
this is recorded as unavailable, with no negative conclusion. LeanFinder,
Loogle and local searches found only general smooth/differential, annihilator
and localization ingredients. Relevant existing modules and signatures were
read before introducing the two missing computations.

## New nodes

`lem-weil-pbc-popescu-lift-partial-chart-dimension` records the explicit
n+m-variable, m-equation chart and the missing special-fibre dimension n
calculation. It follows the D_k/pi D_k paragraph of Tag 07CP. Its proof keeps the
existing smooth base change, differential base change/localization, polynomial
differential decomposition and smooth-over-field dimension nodes. Its main
Lean declaration is `partial_chart_fibre_dimension`; the equation-count and
localization-equivalence corollary is already proved in the same module.

`lem-weil-pbc-popescu-lift-chart-relations` records only pi-divisibility of the
other charts' equations, using the final conormal coefficient calculation of
Tag 07CP. The key identity, original-equation vanishing and pi-torsion are
already proved separately. Equality of annihilators then kills these divisible
equations in a complete Lean proof, and a complete generic fraction argument
proves the comparison bijection. Its main Lean declaration is
`chart_relations_pi_divisible`.

Updated the original node's proof, proof dependencies and proof origin to agree
with the implemented reduction. No change record is needed: no existing
signature, definition or public import was changed, and no forced adaptation
was made.

## Second reading by M3

1. Compared the delivered `PopescuLiftChartFlat` module with the repository version. The
   theorem signature of `Algebra.popescu_lift_chart_flat` is byte-for-byte unchanged;
   the only existing declaration change is its proof and proof-only imports. The two
   added modules and two DAG nodes are explicitly listed above, and no target or
   existing definition was altered.

2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds
   without errors or warnings. The only remaining `sorry`s are the two named public
   split-off theorems, each with a matching node and a proof docstring. No definitions
   contain `sorry`, and no forbidden axiom, unsafe, opaque, extern, or implemented_by
   declaration was added. The completed helper and main declarations use only the
   permitted foundational axioms (the two split-off declarations necessarily expose
   `sorryAx` until proved).

3. Checked the statements of `partial_chart_fibre_dimension` and
   `chart_relations_pi_divisible` against their docstrings, node records, and edge
   cases. The former is only the special-fibre dimension calculation for the explicit
   partial chart; the latter asserts only local pi-divisibility of the other chart
   equations. Neither is a restatement of chart flatness, and neither adds a hidden
   flatness or annihilator hypothesis. The nodes contain the corresponding source,
   proof steps, dependencies, Lean declarations, and split status.

4. Followed the proof from the target downward. It uses the constructed partial chart,
   its equation-count flatness corollary, the proved polynomial evaluation identity,
   proved vanishing/pi-torsion lemmas, the split divisibility statement, and the
   localization comparison. The three old proof-only imports removed from the item are
   still imported where their declarations are used. The unit `sk-thm-p1` route and
   its realized fields remain unchanged; this item is downstream of that route.

5. Reviewed the DAG proof and `proof_deps` against the Lean proof, including both new
   nodes and the updated item node. The proof origin records the Tag 07CP route, and
   the report records the two unavoidable decomposed holes. No shorter existing
   declaration was found by local search or the documented Mathlib searches.

I changed only this report section: it records the independent second reading and no
Lean or DAG content was modified during review.
