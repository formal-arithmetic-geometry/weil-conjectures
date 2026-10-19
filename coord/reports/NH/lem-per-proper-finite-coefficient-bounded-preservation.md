## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFiniteCoefficientBoundedPreservation` states
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_isProper_of_noetherian`.
Its only theorem has proof `by sorry`; no definition or instance is introduced.
The node changes only in `lean`. No statement correction or additional node is needed.
No repair note exists for this item.

Clause-by-clause correspondence:

- Schemes and the indicated morphism: `{Y S : Scheme.{u}}` and `(f : Y ⟶ S)`.
- Both schemes Noetherian, in the finite-affine-cover sense: `[IsNoetherian Y]`
  and `[IsNoetherian S]`. Mathlib's `IsNoetherian` is locally Noetherian plus
  quasi-compact, equivalent to exactly the stated finite affine Noetherian cover;
  see `isNoetherian_iff_of_finite_affine_openCover` and
  `isNoetherian_iff_of_finite_iSup_eq_top` in `Mathlib.AlgebraicGeometry.Noetherian`.
  The affine ring condition is the dependency's `IsNoetherianRing`.
- Properness: `[IsProper f]`. This means separated, universally closed and locally
  of finite type; universal closedness supplies quasi-compactness, hence finite type.
- Arbitrary finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  There is no nonzero-ring, invertibility, field, or coefficient-order assumption.
- Ordinary constant-A module sheaves on the small etale site:
  `DerivedCategoryModule A Y` is definitionally the derived category of
  `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)`. This is the encoding used by
  the recorded bounded-constructible predicate, not a pro-etale or adic category.
- Every bounded constructible input L: `(L : DerivedCategoryModule A Y)` and
  `(hL : DerivedCategory.isBoundedConstructible A Y L)`.
- The output is the actual derived direct image:
  `(rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj L`.
  Its definition is the right derived functor of the recorded `lowerStar`, whose
  sections and restriction maps are precomposition with small-etale base change.
  The total functor restricted to bounded-below objects is the usual Rf_* on D+;
  bounded inputs are precisely the objects needed here. No arbitrary functor or
  comparison hypothesis replaces Rf_*.
- The conclusion is `DerivedCategory.isBoundedConstructible A S` of this output,
  asserting both constructible cohomology in every integer degree and a finite
  interval outside which all cohomology sheaves are zero.
- Neither scheme's Krull dimension is restricted. The statement has no dimension
  bound parameter or finite-dimensionality hypothesis.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (available through the public imports).
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; used through Mathlib's equivalent
  `IsNoetherian` scheme condition in `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The current location of
  the associated `rightDerivedLowerStarPlus`, and of its unbounded counterpart
  `rightDerivedLowerStar` used here, is
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; both are
  actual right-derived functors of this same `lowerStar`. Both modules are public
  imports. The secondary declaration's historical module location in the record
  does not require a replacement construction.
- `def-weil-pbc-constructible-complexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`,
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.

Every stated proof dependency's module is imported, as required for the stage-3
proof plan. `def-weil-pbc-scheme-conventions` is a convention collection with no
Lean declaration of its own; its finite-presentation components are supplied by
Mathlib. The compactification record points to the pro-etale module
`Sheaf.Paper.ProjectionCompactification`, retained as its recorded proof import;
its closed upstream audit also provides the exact etale construction
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, imported through the
compactification-constructibility theorem. The proof docstring explicitly carries
all five steps, their source places, and the DAG references.

Source checks: read `literature/stacks-project/more-etale.tex`,
`theorem-constructible-shriek` (Tag 0GL0) and
`lemma-derived-lower-shriek-bounded` (Tag 0G2A), and
`literature/stacks-project/etale-cohomology.tex`,
`lemma-cohomological-dimension-proper` (Tag 095U). The former constructibility
statement applies to torsion Noetherian coefficients, which includes every finite
commutative ring; the latter bound concerns fibres rather than the base dimension.

Edge cases checked before writing:

- Empty schemes and empty fibres are allowed. No nonemptiness assumption appears;
  the usual zero sheaf and zero complex remain within the predicate.
- The zero coefficient ring is a commutative finite ring and is included. Positive
  torsion exponent one suffices in the proof plan; no `Nontrivial A` is imposed.
- Coefficients divisible by residue characteristics are included, since neither
  an invertible integer nor a prime-to-characteristic hypothesis occurs.
- A Noetherian scheme of infinite Krull dimension is included. Proper finite type
  over a quasi-compact base gives only the fibre bound needed in the proof.
- A complex supported in one degree, shifted by any integer, and the zero complex
  are permitted. Bounds are existential integers in the shared predicate.
- The coefficient universe and module universe are both u+1, exactly as in the
  recorded constructibility interface, with schemes in u; universes and variables
  are explicitly bound and `autoImplicit` is disabled.
- The identity proper morphism is included; there is no nonidentity or surjectivity
  condition on f.

Searches for an existing statement:

- `msearch.py` LeanFinder, query `proper finite coefficient bounded preservation`:
  eight unrelated polynomial/Finsupp finiteness hits, no sheaf theorem.
- `msearch.py` Loogle, query `Proper, Finite, Coefficient, Bounded`: unknown
  identifier `Proper`; repeated with valid substring query
  `"IsProper", "Constructible"`, yielding zero hits.
- `msearch.py` LeanSearch, query `proper derived direct image preserves bounded
  constructible finite ring etale module sheaves`: eight hits about underived
  pushforward, finite-type module sheaves and properness stability, no match.
- `msearch.py` Mathlib grep in `AlgebraicGeometry`, query
  `IsProper.*[Cc]onstructible|[Cc]onstructible.*IsProper|boundedConstructible`:
  zero hits.
- Direct `rg` of Mathlib, the upstream WeilConjectures tree, and `lean/Sheaf`
  for finite coefficients and proper/bounded constructible preservation:
  found `Sheaf.AlgebraicGeometry.ProperBoundedConstructible` and read its entire
  theorem/docstring. Its
  `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_proper`
  requires finite-type schemes over a field and smooth-base-change coefficient
  conditions. Those hypotheses exclude cases expressly retained here, so it
  cannot be recorded as an exact existing match.
- Direct `rg` for the item id in the upstream source tree: no hits. Direct `rg`
  for the new file name and declaration name in upstream and project sources:
  no pre-existing declaration.

Validation: `scompile.py NH lem-per-proper-finite-coefficient-bounded-preservation`
compiled the delivered file cleanly in both its sandbox and library module forms.
No warnings or errors were reported. Lines are at most 100 characters.
No `STATEMENT-DISPUTED` flag is warranted.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
