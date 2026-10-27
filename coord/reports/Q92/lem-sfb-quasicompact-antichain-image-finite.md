## Worker report

The new module `Sheaf.AlgebraicGeometry.QuasiCompactAntichainImageFinite` states
`AlgebraicGeometry.Scheme.Hom.finite_range_of_specialization_antichain`, with `sorry`
as its sole proof. It introduces no definitions and makes no statement correction.
Only the item's `lean` field changes.

Clause correspondence:

- Schemes X and Y: `{X Y : AlgebraicGeometry.Scheme.{u}}`. The category is Mathlib's
  category of schemes, with arbitrary explicitly bound universe `u`.
- Quasi-compact X: `[CompactSpace X]`. This means compactness of the entire underlying
  Zariski space, without a Hausdorff assumption. Mathlib's `isCompact_univ_iff` and
  `isCompact_iff_finite_subcover` identify it with the stated finite-subcover property.
- Locally Noetherian Y: `[AlgebraicGeometry.IsLocallyNoetherian Y]`, precisely the
  declaration recorded by `pqf-def-locnoeth`. Its equivalence with a Noetherian affine
  covering is `isLocallyNoetherian_iff_of_affine_openCover`.
- Any morphism h: `(h : X ⟶ Y)`, with no property imposed on h.
- For all y and y' in the image: `∀ (y : Y), y ∈ Set.range h → ∀ (y' : Y),
  y' ∈ Set.range h → ...`. The scheme-morphism function coercion is its underlying
  continuous map on points; `Set.range h` is exactly its point-set image.
- The specialization condition and conclusion: `y' ∈ closure ({y} : Set Y) → y = y'`.
  The closure is taken in Y itself, as required, rather than in a different topology.
- Finite image: `(Set.range h).Finite`.
- No additional finite-type or Noetherian condition on X, and no separation or
  quasi-compactness condition on Y, occurs. There is no nonemptiness assumption.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (public import).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian` (public import).
- `lem-weil-pbc-affine-opens-basis`: `AlgebraicGeometry.Scheme.isBasis_affineOpens`,
  `Mathlib.AlgebraicGeometry.AffineScheme` (ordinary proof import).
- `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`:
  `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`, same module.
- `lem-sc-finite-minimal-primes-over-ideal`:
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`,
  `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian` (ordinary proof import).
- `lem-weil-pbc-injective-minimal-prime-lift`:
  `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`,
  `Mathlib.RingTheory.Ideal.MinimalPrime.Localization` (ordinary proof import).
- `lem-weil-pbc-prime-contains-minimal-prime`: `Ideal.exists_minimalPrimes_le`,
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic` (ordinary proof import).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (already publicly imported).

The theorem's docstring includes all five DAG proof steps, including quotient prime
correspondence, lifting minimal primes of the kernel quotient, ambient specialization,
and finite union. Read local Stacks sources: morphisms.tex lemma-quasi-compact-dominant
(Tag 01RL), properties.tex lemma-Noetherian-irreducible-components (Tag 0BA8), and
algebra.tex lemmas lemma-image-dense-generic-points (00FL) and
lemma-injective-minimal-primes-in-image (00FK). The node explicitly gives this as an
agent-formulated consequence, not a theorem stated verbatim by either cited tag.

Edge cases checked before writing: empty X gives empty range and vacuous hanti;
empty Y permits only empty X; a singleton image satisfies the hypothesis; a patch
with kernel equal to the whole ring has zero target algebra and empty spectrum.
For an affine target with a genuine strict specialization in the image the hypothesis
fails, as intended. The proof uses no finite-type property of the source algebras.
A non-quasi-compact or non-separated locally Noetherian Y remains allowed, since only
finitely many paired affine charts are chosen using compactness of X. Both schemes
live in the arbitrary universe of Mathlib's scheme category; no index universe or
universe equality beyond that category's own morphism type is introduced.

Searches (all 2026-10-24; raw wrapper summaries in sandbox searches.jsonl):

- msearch.py leanfinder: "The image of a morphism from a quasi compact scheme to a
  locally Noetherian scheme is finite if its points are incomparable under
  specialization". Eight hits, including LocallyQuasiFinite, quasiCompact_of_noetherianSpace_source,
  instQuasiCompactToImage and isClosedMap_iff_specializingMap. None is this result.
- msearch.py loogle: `Set.Finite, Set.range, AlgebraicGeometry.Scheme.Hom`.
  Zero hits.
- msearch.py grep: `antichain|finite_range|finite.*image|image.*finite`, restricted to
  Mathlib/AlgebraicGeometry. Twenty-three hits, concerning finite fibres, quasi-compact
  covers and related morphism properties; no antichain image criterion.
- msearch.py leansearch: "A quasi compact scheme has finite image in a locally
  noetherian scheme if the image has no nontrivial specializations". Eight hits on
  quasi-compactness, dominance and finite morphisms, no exact result.
- rg in lean/WeilConjectures and lean/Sheaf for antichain, specialization.antichain,
  quasi.compact.*finite image, finite image.*quasi.compact and finite_range_of.*Noetherian:
  only unrelated monomial/graded-prime antichains and site comments. A broader finite
  image search returned assorted finite-fibre and finite-image lemmas with different
  hypotheses. The item id has no match in lean/WeilConjectures.
- rg in Mathlib, WeilConjectures and Sheaf for the chosen declaration name found no
  collision. Read the upstream CompactObject example after the requested Sheaf module
  was found withdrawn, using the example node's current upstream lean record.

No new nodes, dependency repair, disputed statement or node fault was needed.

## Second reading by Q92

This is the dispatched worker's own final rereading; the brief assigns the independent
review to the maintainer and prohibits starting another agent. Reopened the node and
module and checked each binder against the clause correspondence above: scheme objects,
compact source, locally Noetherian target, unrestricted morphism, both image-membership
premises, ambient closure direction, equality order, and finite range all agree.
The `lean.statement` is extracted verbatim from the theorem signature. The proof-only
imports cover every recorded proof dependency; theorem proof is only `sorry`. There
are no helper definitions, auto-bound variables, file-local notations or instances,
and no changed hypotheses. No mismatch was found in this rereading.
