## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyFreeGroupoidInvariantAffine` states
`AlgebraicGeometry.exists_invariant_affine_of_finiteLocallyFree_groupoid`, with its
whole proof `sorry`. No definitions, helper nodes, dependency repairs, or statement
corrections are needed. The original node is unchanged except for `lean`.

Source read: `literature/stacks-project/groupoids.tex`, Tag 03JE,
`lemma-find-invariant-affine`, statement and complete proof (lines 4924–4977).
The source's invariant neighbourhood of x contains the whole orbit: identity puts
x in its orbit and invariance transports containment along every arrow. Thus the
node's formulation containing O(x) matches that source. The absolute groupoid is
the dependency's specified notion (equivalently a groupoid over Spec Z).

Hypotheses and conclusion, clause by clause:

- The schemes U and R are `{U R : Scheme.{u}}`, for arbitrary explicit universe u.
- The supplied arrows s,t,e,i,c have exactly the node's domains and codomains,
  including `c : pullback s t ⟶ R`. `_hG : IsGroupoidScheme s t e i c` supplies
  all identity, inversion, source/target, composition and associativity laws;
  the source declaration's full structure and docstring were read.
- Finite locally free source and target are `[s.IsFiniteLocallyFree]` and
  `[t.IsFiniteLocallyFree]`, using the recorded class extending finite, flat,
  locally of finite presentation. No fixed fibre degree is assumed.
- The point is `(x : U)`. Its orbit is exactly `t '' (s ⁻¹' {x})`; the assertion
  about comparing/composing arrows after field extension is an explanation of
  this point-orbit convention, not an additional input hypothesis. The common
  extension of residue fields is in proof step 1 and its dependency is imported.
- Containment in an affine open is `hx : ∃ A : U.Opens, IsAffineOpen A ∧
  t '' (s ⁻¹' {x}) ⊆ (A : Set U)`.
- The conclusion quantifies `∃ W : U.Opens`, requires `IsAffineOpen W`, and
  includes exactly `t '' (s ⁻¹' {x}) ⊆ (W : Set U)`.
- Invariance is `s ⁻¹ᵁ W = t ⁻¹ᵁ W`, equality in `R.Opens`, so the corresponding
  restricted open subschemes are equal. This is not merely an isomorphism or
  a claim about rational points over one field.
- There is no Noetherian, separatedness, dimension, field-base, constant-rank,
  surjectivity, reducedness or nonemptiness binder.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme` (statement dependency, public import).
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (statement dependency,
  public import); its actual class signature and parents were read.
- `WeilConjectures.AlgebraicGeometry.DescentNormLocusAffine`:
  `CategoryTheory.Over.DescentDatum.isAffineOpen_descent_norm_locus` (proof).
- `WeilConjectures.FieldTheory.CommonExtensionFields`:
  `Field.exists_common_extension` (proof).
- Mathlib scheme and spectrum declarations `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map` are already available
  through the public statement imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, including its
  finite-morphism instance; `Scheme.Hom.isClosedMap` from its universally
  closed import, for the closed-image clause.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`:
  `Scheme.Hom.finite_preimage_singleton` for finite orbits.
- `Mathlib.RingTheory.Ideal.Operations`: `Ideal.subset_union_prime`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`,
  `PrimeSpectrum.localization_away_comap_range`.

All proof-only dependencies with declarations are imported without `public`.
Their source signatures were read; the docstring carries all five DAG proof
steps, including the invariant interior H(E), finite prime avoidance and the
final norm-locus affineness criterion. No assertion is proved in this delivery.

Edge cases checked before writing: empty U admits no x, so the statement is
vacuous; a supplied x forces a nonempty orbit by e. An empty R with a nonempty
U cannot satisfy the identity map data. The identity groupoid reduces to an
affine neighbourhood of a point. Rank may vary across components; no degree
binder excludes this. Zero-dimensional, nonreduced, nonseparated and
non-Noetherian schemes remain allowed. The initial affine A need not be
invariant. The conclusion neither asks W to be that A nor adds an unnecessary
W ⊆ A condition. Singleton and multiple-point orbits are covered by the same
set image. No rational-point restriction or independent small test universe
makes the orbit condition vacuous.

Searches run with `msearch.py Q12 lem-sfb-locally-free-groupoid-invariant-affine`:

- leanfinder: "A finite locally free groupoid scheme has an invariant affine open
  neighbourhood of an orbit contained in an affine open". Eight hits, including
  `exists_isAffineOpen_mem_and_subset`, `Scheme.local_affine`, and affine cover
  lemmas; these supply point neighbourhoods without groupoid invariance, not
  this result.
- loogle: `"IsAffineOpen", "Groupoid"`. Zero hits.
- grep: `invariant.*affine|affine.*invariant|GroupoidScheme` in Mathlib's
  AlgebraicGeometry. Zero hits.
- leansearch: "An orbit of a finite locally free groupoid contained in an affine
  open has an invariant affine open neighborhood". Eight hits concerning
  manifold structure groupoids, group-action orbits and flows; no scheme result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for groupoid/invariant-affine
  names, and for this node id. The item id occurs only in proof docstrings of
  consumers. `CategoryTheory.Over.DescentDatum.exists_invariant_affine_neighbourhood`
  in `WeilConjectures.AlgebraicGeometry.InvariantAffineNeighbourhoods` was opened
  and read in full: it applies to a specified descent datum of a finite locally
  free surjection and assumes every finite subset has an affine neighbourhood.
  It is not the present arbitrary absolute groupoid statement.
- The proposed declaration name was searched in both project roots, Mathlib,
  and `dag/lean_names_upstream.json`: no match.

No statement dispute or node fault was found. The example CompactObject module
is now withdrawn; its node points to the upstream module, which was read for
the current module-mode/public-section convention.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
