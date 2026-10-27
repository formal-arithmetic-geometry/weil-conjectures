## Worker report

The module `Sheaf.AlgebraicGeometry.GenericResidueTranscendenceDimensionBound`
states `AlgebraicGeometry.generic_residue_transcendence_dimension_bound`, with
the sole proof `by sorry`. It introduces no definitions. The node changes only
in `lean`; its statement, dependencies, and proof are preserved.

The source was read in `literature/stacks-project/morphisms.tex`:
`lemma-alteration-dimension-general` (Tag 0BAG) and
`lemma-dimension-formula-general` (Tag 0BAE). Tag 0BAG gives exactly the
dimension inequality using the supremum of generic residue degrees; finite
bounds d and n give this node's formulation. No source-based correction is
needed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Morphism f : Y → S of schemes | `{Y S : Scheme.{u}} (f : Y ⟶ S)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| S locally Noetherian | `[IsLocallyNoetherian S]` |
| Nonnegative integers d,n | `(d n : ℕ)`, the exact parametrization of nonnegative integers |
| Topological Krull dimension, empty dimension −∞ | `topologicalKrullDim : WithBot ℕ∞`, with bottom for the empty space |
| dim S ≤ d | `hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)` |
| Every generic point η of every irreducible component Z of Y | `∀ (η : Y) (Z : Set Y), Z ∈ irreducibleComponents Y → IsGenericPoint η Z → ...` |
| Extension induced by f | `(f.residueFieldMap η).hom.toAlgebra`, explicitly supplied to `@Algebra.trdeg` |
| trdeg over κ(f(η)) of κ(η) ≤ n | `@Algebra.trdeg (S.residueField (f η)) (Y.residueField η) _ _ (f.residueFieldMap η).hom.toAlgebra ≤ (n : Cardinal)` |
| dim Y ≤ d+n | `topologicalKrullDim Y ≤ ((d + n : ℕ) : WithBot ℕ∞)` |
| No irreducibility, reducedness, dominance, quasi-compactness, separatedness, properness, or surjectivity assumptions | None of these appears as a binder or instance requirement. |
| Empty schemes allowed | Neither scheme has a `Nonempty` requirement. |

All universes and variables are explicitly bound, and `autoImplicit` is false.
The two `Scheme.{u}` objects use the universe of the category of scheme morphisms;
u is arbitrary. No test-object quantifier has a smaller independent universe.

Recorded dependency declarations, with source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (schemes and their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the local affine finite-type condition.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`, every affine open having Noetherian
  section ring, equivalent to the node's affine-cover definition.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, the Krull dimension
  of the order of irreducible closed subsets with values in `WithBot ℕ∞`.
- `Mathlib.Topology.Sober`: `IsGenericPoint η Z`, namely `closure {η} = Z`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents Y`, the maximal
  irreducible subsets. This dependency is a Mathlib leaf whose `mathlib_match`
  is the declaration; it needs no new Lean record.
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`. The latter is induced by the
  local stalk map, not an arbitrary field extension.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`, the
  supremum of cardinalities of algebraically independent subsets.

The proof-only dependencies are imported without `public`:

- `Sheaf.AlgebraicGeometry.LocalDimensionFormulaGenericComponents`:
  `AlgebraicGeometry.local_dimension_formula_generic_components`. Its finite
  nonempty component set and canonical residue algebra structure are exactly
  those required by proof step 2.
- `WeilConjectures.AlgebraicGeometry.Dimension`:
  `AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`, together with the real
  definition `Scheme.dim` as the supremum of stalk ring dimensions. It gives
  the input in proof steps 2 and 3, including the empty case.

Edge cases checked mathematically against the signature:

- Empty Y: the generic-point condition is vacuous and the conclusion is the
  true bottom inequality; an empty S forces Y empty for any such morphism.
- d = 0 or n = 0: both are admitted. Algebraic generic extensions have degree
  zero, and the resulting source bound is exactly d when n = 0.
- Reducible and nonreduced Y: the condition ranges over all components and
  uses residue fields, with no integral or reduced instance imposed.
- A component mapping into a proper closed subset of S: the base field is
  κ(f(η)), rather than a function field of S, so nondominance is included.
- Infinite unions of components and non-quasi-compact schemes: no finite
  global component set or finite covering is assumed. The proof uses only
  finitely many components through each fixed point, then a supremum.
- The hypotheses are substantive: dim S ≤ d can fail, and the generic degree
  bound excludes affine space of relative dimension n+1 over a field.

Searches for an existing exact theorem (2026-10-24):

- `msearch.py ... leanfinder "Dimension of a locally finite type scheme over a
  locally Noetherian base bounded by base dimension plus generic residue field
  transcendence degree"`: eight hits, including local Noetherianity under
  locally finite type maps, zero-dimensional locally Artinian schemes, finite
  transcendence degree, and polynomial ring dimension. No exact inequality.
- `msearch.py ... leansearch "dimension bound locally finite type morphism
  locally Noetherian generic residue field transcendence degree"`: eight hits
  on finite type definitions, `Algebra.trdeg`, transcendence bases, and local
  Noetherianity; none states the node.
- `msearch.py ... loogle '"topologicalKrullDim", "trdeg"'`: zero hits.
- `msearch.py ... grep
  'topologicalKrullDim.*trdeg|trdeg.*topologicalKrullDim|generic.*dimension'
  AlgebraicGeometry`: zero hits in Mathlib.
- `rg -n 'topologicalKrullDim.*trdeg|trdeg.*topologicalKrullDim|generic_residue|generic.*dimension'
  lean/WeilConjectures lean/Sheaf`: related dimension-formula results and generic
  geometry constructions, but no matching bound. In particular
  `ClosedIrreducibleDimensionTrdeg` concerns a closed irreducible subset over
  a field; `FiniteTypeDimensionFormula` concerns dimension at a point over a
  field; neither is the general morphism statement here.
- `rg -n 'lem-sfb-generic-residue-transcendence-dimension-bound'
  lean/WeilConjectures`: no hit.
- `rg -n 'generic_residue_transcendence_dimension_bound|topologicalKrullDim_le_of_generic'
  dag/lean_names_upstream.json lean/.lake/packages/mathlib/Mathlib
  lean/WeilConjectures lean/Sheaf`: no declaration-name collision.

Validation: `scompile.py Q88 lem-sfb-generic-residue-transcendence-dimension-bound`
compiled the delivered file cleanly as both sandbox and library module (4.5 s
and 20.5 s). No error or warning was printed. No statement dispute or node fault
was found. No helper node or dependency interface repair is needed.

## Second reading by Q88

Independent second reading by the maintainer's review service (the delivered
section was a self-audit by the same worker, delivery-errors H11; it is
replaced here). The Lean module and node record are unchanged.

Source read: literature/stacks-project/morphisms.tex, Tag 0BAG
(lemma-alteration-dimension-general): f : X → Y locally of finite type, Y
locally Noetherian, dim X ≤ dim Y + E with E the supremum of
trdeg_{κ(f(ξ))} κ(ξ) over generic points ξ of irreducible components of X.
The node specialises to dim S ≤ d and E ≤ n for natural numbers d, n.

Clause-by-clause (node → Lean → verdict):

1. Schemes Y, S and a morphism f : Y → S → `{Y S : Scheme.{u}} (f : Y ⟶ S)`
   (def-pc-scheme record: AlgebraicGeometry.Scheme). Correct; u arbitrary.
2. f locally of finite type → `[LocallyOfFiniteType f]`
   (def-weil-finite-type-morphism record). Correct; no quasi-compactness.
3. S locally Noetherian → `[IsLocallyNoetherian S]` (pqf-def-locnoeth
   record). Correct; nothing assumed on Y.
4. Integers d, n ≥ 0 → `(d n : ℕ)`. Exact.
5. Topological Krull dimension with dim ∅ = −∞ → `topologicalKrullDim`
   (def-kun-topological-krull-dimension record), valued in `WithBot ℕ∞`
   with ⊥ for the empty space. Correct.
6. dim S ≤ d → `hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)`. Correct.
7. For every generic point η of an irreducible component of Y →
   `∀ (η : Y) (Z : Set Y), Z ∈ irreducibleComponents Y → IsGenericPoint η Z → …`
   (def-weil-irreducible-components, def-sc-generic-point records). Correct.
8. trdeg_{κ(f(η))} κ(η) ≤ n for the extension induced by f →
   `@Algebra.trdeg (S.residueField (f η)) (Y.residueField η) _ _
   (f.residueFieldMap η).hom.toAlgebra ≤ (n : Cardinal)`
   (def-weil-residue-field: Scheme.residueField and Hom.residueFieldMap, the
   map induced by the local stalk map; def-kun-transcendence-degree:
   Algebra.trdeg). The algebra structure is the one induced by f, not an
   instance search result. Correct.
9. Conclusion dim Y ≤ d + n →
   `topologicalKrullDim Y ≤ ((d + n : ℕ) : WithBot ℕ∞)`. Correct, neither
   weaker nor stronger.
10. No irreducibility, reducedness, dominance, quasi-compactness,
    separatedness, properness, surjectivity → none present. Correct.

Edge cases: Y empty (hypothesis vacuous, conclusion ⊥ ≤ …, true); S empty
forces Y empty; d = 0, n = 0 admitted; reducible / non-reduced Y (residue
fields, all components); non-dominant components (base field κ(f(η)), as in
the source); non-quasi-compact Y with infinitely many components (no finite
cover assumed). Universes: one universe u, trdeg in Cardinal.{u}, nothing
unbound.

Records: stmt_deps are the eight definition nodes, all Mathlib leaves with
`existing: true` records naming exactly the declarations used. Proof-only
imports (`Sheaf.AlgebraicGeometry.LocalDimensionFormulaGenericComponents`,
`WeilConjectures.AlgebraicGeometry.Dimension`) are the landed records of the
proof_deps lem-sfb-local-dimension-formula-generic-components and
lem-pc-scheme-dimension-local-rings, imported non-publicly. `lean.statement`
is verbatim the signature in the file. The node differs from the live node only
in the new `lean` field (no rebind, no statement change). One theorem, proof
`sorry`, no definitions; docstrings carry the source place, the blueprint id
and the three proof steps.

Searches: Mathlib and lean/WeilConjectures, lean/Sheaf for
topologicalKrullDim/trdeg combinations, 0BAG/0BAE, dimension_formula: no
existing statement (FiniteTypeDimensionFormula and
ClosedIrreducibleDimensionTrdeg are narrower, over a field).

No mismatch in the Lean; only this report section was replaced.
