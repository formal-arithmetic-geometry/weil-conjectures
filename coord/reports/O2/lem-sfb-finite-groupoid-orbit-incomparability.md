## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidOrbitIncomparability` states
`AlgebraicGeometry.IsGroupoidScheme.not_mem_closure_singleton_of_isFinite` with a
single `sorry` proof. It introduces no definitions and proves nothing. The node
copy changes only `lean`. No new nodes, dependency repairs or statement changes
are needed.

Hypotheses and clauses, matched to the node:

- The schemes U and R are `{U R : Scheme.{u}}`, with an explicit universe `u`.
- The source, target, identity, inverse and composition morphisms are `(s t : R ⟶ U)`,
  `(e : U ⟶ R)`, `(i : R ⟶ R)` and `(c : pullback s t ⟶ R)`.
- The groupoid hypothesis is `(_hG : IsGroupoidScheme s t e i c)`, using exactly
  the recorded declaration of `def-a1-groupoid-scheme`. It includes the functor-of-points
  groupoid laws, rather than assuming a groupoid merely on underlying points.
- Finiteness of both source and target is `[IsFinite s] [IsFinite t]`, using
  the recorded declaration of `def-weil-finite-integral-morphism`.
- The arbitrary points are `(x y : U)`; distinctness is `(_hxy : x ≠ y)`.
- The orbit O(x) is written inline as `t.base '' (s.base ⁻¹' {x})`.
  The hypothesis `(_hy : y ∈ t.base '' (s.base ⁻¹' {x}))` is precisely the node's
  `y ∈ O(x)`, with ordinary scheme points and no rational-point restriction.
- The conclusion is `y ∉ closure ({x} : Set U)`, literally the node's singleton
  closure exclusion. Mathlib's `specializes_iff_mem_closure` confirms its orientation:
  `x ⤳ y` means `y ∈ closure {x}`.
- The final sentence about any two distinct points of one orbit follows from
  quantifying x and y arbitrarily and the groupoid inversion/composition laws, which
  identify the orbits of related points. It does not require a stronger conjunct.
- The remark on comparing and composing arrows after extending residue fields is
  an explanation of underlying-point composition, not an additional hypothesis.
  It is retained explicitly in step 1 of the proof docstring: a prime of the nonzero
  residue-field tensor product supplies the needed composable-arrow point.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`, `AlgebraicGeometry.IsGroupoidScheme`:
  its full structure and docstring were read, including the six endpoint identities,
  identity and inverse laws, and associativity on all test schemes. Public import.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`:
  the full class signature and docstring were read. It extends `IsAffineHom` and
  requires a finite map on sections of every affine open. Public import.
  The integral companion is `AlgebraicGeometry.IsIntegralHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`.

All recorded proof-dependency modules are imported privately when not already public:
`Mathlib.RingTheory.TensorProduct.Nontrivial` (nonzero tensor product),
`Mathlib.RingTheory.Spectrum.Maximal.Basic` (existence of maximal primes),
`Mathlib.AlgebraicGeometry.PullbackCarrier` (fibre-product points),
`Mathlib.RingTheory.Ideal.GoingUp` (integral incomparability),
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` (closed maps and finite fibres),
`Mathlib.AlgebraicGeometry.Properties` (scheme sobriety), and
`Mathlib.Topology.Inseparable` (closed maps lift specializations).
The scheme and affine spectrum declarations and finite-implies-integral instance
are supplied through the public finite-morphism import. The declaration docstring
records all five proof steps and the DAG inputs used in them.

Source checked: `literature/stacks-project/more-groupoids.tex`,
`lemma-no-specializations-map-to-same-point`, Tag 0ABG, lines 2747–2767.
Its proof uses the closed source map to iterate strict target specializations inside
one finite orbit. The node correctly places orbit points in U (the source text has
an evident R-for-U typo, resolved by its own equations `s(r) = u`, `t(r) = u'`).
The accepted node itself needs no correction.

Edge cases checked before drafting:

- Empty U is allowed: the assertion quantifies over its points and is vacuous.
  No `Nonempty` instance is imposed on either scheme.
- For x = y the distinctness hypothesis excludes the case, as necessary because
  every point lies in its own singleton closure.
- For a singleton orbit or the identity groupoid, there is no distinct orbit member,
  so the implication has the intended vacuous meaning.
- Points and residue fields are not assumed closed, rational, equal, or separable.
  Composition of point-arrows uses a common extension via a tensor-product prime.
- No flatness, finite type over a field, separatedness of U, Noetherian assumption,
  reducedness, dimension restriction, or positive degree is added.
- The scheme universe u is explicit and arbitrary, matching the dependency interface.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query: "Distinct points in an orbit of a scheme
  groupoid with finite source and target do not specialize to each other".
  Eight hits: local specialization-map facts, scheme specialization order,
  inseparability, and open-set separation. None states the groupoid theorem.
- `msearch.py ... leansearch`, query: "Orbits of a scheme groupoid with finite
  source and target have no nontrivial specializations". Eight hits: scheme
  specialization order and ordinary monoid-action orbit facts; no exact match.
- `msearch.py ... loogle`, query: `"Groupoid", "Specializes"`. Zero hits.
- `msearch.py ... grep`, query: `orbit.*speciali|speciali.*orbit`. Zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` with the same expression found
  `ProEtale/Adic/LisseCover/FiniteOrbit.lean` and
  `AffineGroupoidEtaleInvariantComparison.lean`. Those files were inspected:
  the former concerns finite subsets of descent-cocycle coefficient sets; the latter
  an etale comparison of invariant spectra. Neither states this theorem.
- Searches for `IsGroupoidScheme`, `finiteGroupoid`, `finite_groupoid`,
  `not_mem_closure_singleton_of_isFinite`, and the item's id in the project and
  `dag/lean_names_upstream.json` found the existing groupoid definition and consumers,
  but no existing version of this assertion or clash with the chosen name.
  `rg` for `specializes_iff_mem_closure` located the precise closure convention in
  `Mathlib/Topology/Inseparable.lean`, line 118.

Validation: `scompile.py O2 lem-sfb-finite-groupoid-orbit-incomparability` on the
module succeeded in both sandbox mode (10.7 s) and library mode (3.7 s), with no
errors or warnings. Every variable and universe is explicit. All lines are within
100 characters. There are no disputed statements or node faults.

## Second reading by O2

I reopened the node and Lean file for a separate second pass; no other agent was
started, as the dispatcher brief prohibits delegation. This is a self-review,
with the maintainer's independent review still to follow.

The morphism binders and `IsGroupoidScheme s t e i c` reproduce exactly the tuple
in the node. Both finite assumptions are present. The points are points of U,
not R, and orbit membership has the correct source-fibre/target-image order.
The closure conclusion excludes y from the closure of x, not the reverse closure.
The point-distinctness assumption is essential and present. The common-extension
argument is retained in the docstring, with no spurious equality of residue fields
or arbitrary composability assumption. The last sentence follows for arbitrary
ordered pairs in a common orbit by the existing groupoid laws. No hypothesis,
conclusion or definition mismatch was found, so this pass required no changes.
