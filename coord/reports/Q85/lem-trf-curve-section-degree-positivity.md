## Worker report

The module `Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity` states
`AlgebraicGeometry.Scheme.Modules.curve_section_degree_nonneg_and_pos` with `sorry`.
It is exactly clauses (1) and (2) of Stacks Varieties Tag 0B40,
`lemma-check-invertible-sheaf-trivial`, for the integral proper curve of the node.
The source was read in `literature/stacks-project/varieties.tex`, including its proof
via an effective Cartier divisor and the degree formula of Tag 0AYY.
No definition, additional hypothesis, or statement correction is introduced.
Only the item's `lean` record changes. All variables and the universe are explicit;
`autoImplicit` and `relaxedAutoImplicit` are disabled.

Hypothesis and conclusion correspondence:

- Field k: `(k : Type u) [Field k]`.
- Integral scheme C: `(C : Scheme.{u}) [IsIntegral C]`. This includes nonemptiness,
  reducedness and irreducibility; smoothness and geometric integrality are not required.
- C is over k: `[C.Over (Spec (.of k))]`, its specified structure morphism.
- Proper over k: `[IsProper (C ↘ Spec (.of k))]`. Universally closed implies
  quasi-compact, so Mathlib's locally finite type proper morphism is finite type.
- Topological Krull dimension one: `(hC : topologicalKrullDim C = 1)`, with 1 in
  `WithBot ℕ∞`; this uses exactly the topological dimension dependency.
- Invertible O_C-module: `(L : C.Modules) [L.IsInvertible]`, the recorded scheme-module
  notion of local freeness of rank one, which implies quasi-coherence.
- Global section: `(s : Γ(L, ⊤))`, with `(hs : s ≠ 0)` for nonzero.
- Nonnegative degree: the first conjunct `0 ≤ L.degree k`.
- Vanishing at some point, expressed by the node as C_s not all of C:
  `nonvanishingLocus L s ≠ Set.univ`. The recorded definition is the set of points
  where the germ is outside the maximal ideal times the stalk module, equivalently
  nonzero in the residue-field fibre. It applies directly to L, without a tensor-power
  replacement or an additional witness.
- Conditional strict positivity: the second conjunct
  `(nonvanishingLocus L s ≠ Set.univ → 0 < L.degree k)`.
  Both degrees are the integer-valued Euler-characteristic degree over k.

Statement-dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (mathlib_match of def-weil-field).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`, defined as chi(L) minus chi(O_C).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`, the declaration recorded
  alongside IsAmple in def-weil-pbc-ample-invertible-module. The full definition was
  read from the project's current source, not replaced by an ad hoc locus.

Proof dependencies are included as ordinary imports: NonzeroSectionIntegralCartier,
CartierDivisorFinite, Dimension, Modules.ZeroLocus, and Picard.ZeroScheme, with the
remaining recorded proof declarations residing in EulerChar and Ample, already publicly
imported for the statement. The theorem docstring records each of the node's four proof
steps, including the dimension comparison and the finite nonzero algebra argument.
Every supplied theorem has only `sorry` as its proof.

Edge cases checked before writing:

- Empty curves are already excluded by integrality, and also cannot have dimension one.
- The zero section is excluded precisely by hs, without a fibrewise-nonzero hypothesis.
- A nowhere-vanishing nonzero section trivializes L, whose degree is zero. The first
  conjunct allows equality; the premise of the strict-positivity implication is false.
- A section of O(1) on the projective line with one zero has degree one, as required.
- Vanishing at a non-rational closed point contributes its positive residue-field degree;
  no rational-point or algebraically-closed-field hypothesis is imposed.
- Singular integral curves and curves with a larger constant field remain included.
- Every characteristic is permitted. There is no genus or regularity restriction.
- C and k have the common ambient universe required by the recorded Spec and degree
  interfaces; the theorem is universe polymorphic and imposes no additional size equation.

Searches made (raw remote search records are in the sandbox's searches.jsonl):

- msearch.py leanfinder: "A nonzero global section of an invertible sheaf on a proper
  integral curve has nonnegative degree, and positive degree if it has a zero".
  Eight hits: division-polynomial and coordinate-ring degree facts, plus the function
  field instance; no match for the line-bundle assertion.
- msearch.py loogle: `"degree", "nonneg"`. Zero hits.
- msearch.py grep: `degree_nonneg|degree_pos|nonzero.*section|section.*degree` in
  Mathlib AlgebraicGeometry. Zero hits.
- msearch.py leansearch: "A line bundle on a proper integral curve with a nonzero
  global section has nonnegative degree and strictly positive degree if the section
  vanishes somewhere". Eight hits on polynomial degree, local evaluations, meromorphic
  divisors and integral-scheme sections; none states the requested assertion.
- rg of WeilConjectures and lean/Sheaf for the degree/section patterns, plus the item id:
  no exact statement. `Modules.finrankH_zero_eq_zero_of_degree_neg` in upstream
  Curve.RiemannRoch assumes a smooth proper curve with GlobalSectionsBijective and only
  gives the negative-degree vanishing assertion, so is not an exact existing declaration.
  The existing proper-integral-curve ampleness theorem cites this node in its proof and
  gives the ampleness criterion, rather than this statement about a chosen section.
- Name search for the new theorem: no existing declaration with that full name found.

Validation: the module compiled successfully through scompile.py, both its sandbox and
library-path checks, within the 60-second per-file limit and without warnings or errors.
The final delivery dry run recompiles the final file and checks the node record.
There is no STATEMENT-DISPUTED finding and no source-based correction is needed.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
