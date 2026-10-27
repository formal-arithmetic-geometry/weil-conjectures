## Worker report

The module `Sheaf.AlgebraicGeometry.LocalDimensionFormulaGenericComponents` states
`AlgebraicGeometry.local_dimension_formula_generic_components`, with one `sorry` and no new
definitions. Source read: literature/stacks-project/morphisms.tex, Tag 0BAE,
`lemma-dimension-formula-general`, including its proof. The preceding integral case, Tag 02JU,
is exposed by the recorded proof dependency `Sheaf.TraceFormula.LocalDimensionFormula`.
The accepted Q29 stage-1 split is preserved verbatim. The inherited unchanged-stage-1
rejection does not concern this stage-2 delivery: the item has no Lean record on the base,
and there is no released repair note.

Hypothesis and conclusion correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`, with arbitrary explicit
  universe `u`. These use `AlgebraicGeometry.Scheme` and `Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme).
- Locally finite type: `[LocallyOfFiniteType f]`, the recorded
  `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (def-weil-finite-type-morphism).
- Locally Noetherian base: `[IsLocallyNoetherian S]`, the recorded
  `AlgebraicGeometry.IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`
  (pqf-def-locnoeth). No global Noetherian or quasi-compact hypothesis is added.
- Prescribed point: `(x : X)`; `s` is written directly as `f x` throughout.
- `G_x` finite: an existential `G : Finset X` represents precisely that set, through
  `(∀ ξ : X, ξ ∈ G ↔ ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ IsGenericPoint ξ Z)`.
  `irreducibleComponents` is the exact Mathlib match of def-weil-irreducible-components,
  imported from `Mathlib.Topology.Irreducible`. `IsGenericPoint` is the recorded declaration
  of def-sc-generic-point in `Mathlib.Topology.Sober`, namely closure of the singleton = Z.
  The equivalence ensures that no components through x are omitted and no extra points
  are inserted.
- `G_x` nonempty: the separate conjunct `G.Nonempty`.
- Residue fields and their specified extension structures: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`, exactly
  def-weil-residue-field. Every `@Algebra.trdeg` uses explicitly
  `(f.residueFieldMap ξ).hom.toAlgebra` (and the analogous expression at x), rather
  than an arbitrary field embedding or an unrelated inferred algebra structure.
- All transcendence degrees are finite nonnegative integers: the witnesses `tx : ℕ` and
  `t : X → ℕ`, with cardinal equalities `trdeg ... = (tx : Cardinal)` and
  `∀ ξ ∈ G, trdeg ... = (t ξ : Cardinal)`. This uses precisely `Algebra.trdeg` from
  `Mathlib.RingTheory.AlgebraicIndependent.Basic` (def-kun-transcendence-degree).
  Values of t outside G have no constraint and no use; any finite component-indexed
  family extends to such a total function by zero. Hence no extra condition is imposed.
- Maximum `E_x`: `G.sup t : ℕ`, the finite supremum of exactly those natural numbers.
  Since G is nonempty this supremum is attained and is exactly the stated maximum.
  An explicit inner ℕ annotation prevents coercion from changing the codomain of t.
- Local rings: `X.presheaf.stalk x` and `S.presheaf.stalk (f x)`, the structure-sheaf
  stalks referred to by def-weil-pbc-module-stalk. Its recorded
  `WeilConjectures.Topology.PresheafModuleStalkFunctor` is publicly imported; the theorem
  needs only the underlying ring stalk, not the additional module-stalk functor.
- Dimensions and inequality: `ringKrullDim` from
  `Mathlib.RingTheory.KrullDimension.Basic` (def-weil-pbc-krull-dimension-ring), and
  `ringKrullDim (X.presheaf.stalk x) + (tx : WithBot ℕ∞) ≤
  ringKrullDim (S.presheaf.stalk (f x)) + ((G.sup t : ℕ) : WithBot ℕ∞)`.
  All finite terms embed in Mathlib's extended dimension domain; no subtraction or
  truncation is used.
- There are no binders for irreducibility, reducedness, dominance, universal catenarity,
  quasi-compactness, or separatedness. This also covers non-dominant components.

All recorded statement-dependency modules are public imports. Already stated proof
dependencies are plain imports: the integral local dimension inequality, affine scheme
point/stalk descriptions, finite-type algebras, residue field finiteness, finite transcendence
bases, localization and quotient descriptions, minimal primes, and spectrum components.
The theorem docstring carries the nine accepted proof steps, identifying the DAG lemmas
and the elementary fraction and prime-chain arguments. No dependency record is repaired.

Edge cases checked against the source before writing:

- Empty X admits no point x, so the assertion is vacuous without assuming X nonempty.
- For the identity morphism, every residue extension has degree zero and the inequality
  reads dim O_x ≤ dim O_x, with all components through x retained.
- Affine n-space over a field gives local dimension + residual transcendence degree ≤ n;
  at its generic point the left local dimension is zero and tx = n.
- For Spec k[a,b]/(ab) at its crossing, G contains the two component generic points;
  the result concerns the maximum, and does not assume a unique generic point.
- Nilpotents and embedded primes do not introduce component generic points; they do not
  change the relevant prime chains, and no reducedness hypothesis is needed.
- Spec F_p[t] → Spec Z is permitted: its component image is not dense in the base,
  but the quotient-base integral argument in the proof applies.
- G cannot be empty for a point in a locally Noetherian scheme; G.Nonempty explicitly
  states that result. Zero transcendence degrees are allowed by ℕ, including n = 0.
- Ring dimensions retain the WithBot ℕ∞ convention; stalks at genuine points are
  nonzero, so the zero-ring bottom case is never silently cast to dimension zero.

Searches run in this session with the prescribed msearch.py wrapper:

- leanfinder: “Local dimension inequality for a locally finite type morphism over a
  locally Noetherian scheme with maximum residue transcendence degree at generic
  components”. Eight hits: locally finite type, local Noetherian permanence, smooth
  relative dimension and residue maps; no matching inequality.
- loogle: `ringKrullDim, Algebra.trdeg`. Zero hits.
- grep: `ringKrullDim.*trdeg|trdeg.*ringKrullDim|dimension.formula` in AlgebraicGeometry.
  Zero hits in the Mathlib search.
- leansearch: “Local ring dimension inequality with maximum relative transcendence
  degrees of generic points of irreducible components for a locally finite type
  morphism”. Eight hits on trdeg, height and quotient bounds; none states this result.
- Direct rg over lean/WeilConjectures and lean/Sheaf for dimension-formula and
  trdeg/ringKrullDim patterns found the integral dominant local_dimension_formula and
  results over fields, but no generic-components version. Read the full integral
  local_dimension_formula signature and proof docstring: it is a proof dependency,
  and its integral/dominant assumptions prevent it being an existing match here.
- Direct grep of the item's blueprint id in lean/WeilConjectures: no hits. Direct rg
  for the proposed declaration name in both libraries and dag/lean_names_upstream.json:
  no collision. The broader generic/components/dimension search found unrelated
  plurinodal, nodal-curve, and closed-fibre passages, no duplicate statement.

No new nodes, statement correction, or STATEMENT-DISPUTED issue is needed.
Independent second reading is left to the maintainer as instructed in the current brief.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
