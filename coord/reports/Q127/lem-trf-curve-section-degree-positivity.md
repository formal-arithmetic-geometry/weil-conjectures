## Worker report

The module `Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity` states
`AlgebraicGeometry.Scheme.Modules.curve_section_degree_nonneg_and_pos_of_nonvanishingLocus_ne_univ`
with a single `sorry`. It introduces no definitions. The node's statement and dependency lists
are unchanged. The source was read in `literature/stacks-project/varieties.tex`,
`lemma-check-invertible-sheaf-trivial` (Tag 0B40), including its proof: a regular nonzero
section gives an effective Cartier divisor D, whose degree is nonnegative and is zero
exactly when D is empty. These are precisely clauses (1) and (2).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k is `{k : Type u} [Field k]`.
- The scheme C over k is `{C : Scheme.{u}} [C.Over (Spec (.of k))]`; this supplies the
  structure morphism without adding a choice of another morphism.
- Integrality is `[IsIntegral C]`, including nonemptiness and reduced irreducibility.
- Properness over k is `[IsProper (C ↘ Spec (.of k))]`. It supplies finite type and
  separatedness as required by the source's curve convention.
- Topological Krull dimension one is
  `hdim : topologicalKrullDim C = (1 : WithBot ℕ∞)`.
- The invertible module is `(L : C.Modules) [L.IsInvertible]`.
- Its global section is `(s : Γ(L, ⊤))`, and nonzeroness is `hs : s ≠ 0`.
- The first conclusion is `0 ≤ degree k L`, with the recorded Euler-characteristic degree.
- The additional vanishing hypothesis is `nonvanishingLocus L s ≠ Set.univ`, exactly the
  node's C_s ≠ C. The second conclusion is the implication from this hypothesis to
  `0 < degree k L`. The conjunction retains the first conclusion even for nowhere-vanishing s.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, defined by local triviality.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`, the difference of Euler characteristics.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`, the locus where the germ is outside
  the maximal ideal times the stalk. Its recorded definition, including the full germ/stalk
  expression, was read in the shared source.

All recorded modules of proof dependencies are also imported: `Sheaf.AlgebraicGeometry.Dimension`,
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`,
`Sheaf.AlgebraicGeometry.CartierDivisorFinite`,
`Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier`, and
`WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`; the degree and ample modules already
supply the other proof-dependency imports. The declaration docstring records all four proof
steps and their DAG inputs. No proof dependency imports the new module.

Edge cases checked:

- The empty scheme is excluded by integrality, exactly as for a curve in the source.
- A zero section is excluded explicitly; it could have zeros even for degree-zero L, so
  nonzeroness cannot be omitted.
- A nowhere-vanishing section of the trivial line bundle has degree zero. The first clause
  allows this, and the premise of the second clause fails.
- A section with a zero imposes no rationality condition on that point. The nonvanishing
  locus uses all scheme points, including non-rational closed points.
- There is no smoothness, geometric integrality, algebraic closure, characteristic,
  rational-point or H⁰(O_C) = k assumption. The arbitrary field and singular integral
  proper curves remain included.
- The common arbitrary universe u follows the recorded degree and scheme interfaces and
  is the same convention as the consumer `proper_integral_curve_isAmple_iff_degree_pos`.
- The dimension condition is equality to one, not merely a bound allowing dimension zero.

Searches made with `msearch.py Q127 lem-trf-curve-section-degree-positivity`:

- LeanFinder: “A nonzero global section of a line bundle on a proper integral curve has
  nonnegative degree and strictly positive degree if its nonvanishing locus is not the
  whole curve”. Eight results concern restrictions to basic opens, evaluations, and
  Weierstrass coordinate-ring degrees. None states the item.
- LeanSearch: “A line bundle on a proper integral curve with a nonzero global section has
  nonnegative degree”. Eight results include finite global sections of a proper integral
  scheme, polynomial degree, analytic divisors, and zero sections. None states the item.
- Loogle: `"degree", "nonvanishing"`: zero hits.
- Mathlib grep: `degree_nonneg|degree_pos|nonzero.*section.*degree` in AlgebraicGeometry:
  zero hits.
- Source/project `rg`: `degree_nonneg|degree_pos|nonvanishingLocus.*degree|degree.*nonvanishingLocus`
  and the item id. The upstream degree positivity results assume ampleness or concern
  smooth proper curves; none is this statement. The landed consumer
  `Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree` mentions this node in its proof
  plan and has the ampleness/degree equivalence, not this section theorem.
- `dag/lean_names_upstream.json` was searched for the same names; the matches were the
  ampleness/degree results. The proposed declaration name was searched in Mathlib, upstream,
  the shared `lean/Sheaf` tree, and the upstream-name index; no existing declaration matched.

Validation: `scompile.py Q127 lem-trf-curve-section-degree-positivity` compiled the delivered
module cleanly as both sandbox and library module. All variables and universe u are explicit,
with both auto-implicit options disabled. There are no new nodes, dependency repairs,
statement corrections, or disputed statements. The maintainer performs the independent review.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
