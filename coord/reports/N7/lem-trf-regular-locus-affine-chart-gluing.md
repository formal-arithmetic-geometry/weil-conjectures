## Worker report

The module `Sheaf.AlgebraicGeometry.RegularLocusAffineChartGluing` states
`AlgebraicGeometry.regularLocus_affine_chart_gluing` with one whole-proof `sorry`.
There are no new definitions, dependency modules, or statement corrections. The
node copy changes only `lean`. The declaration docstring reproduces all three
proof steps and their dependency uses.

The statement is rendered clause by clause as follows.

- The locally Noetherian scheme is `(Y : Scheme.{u}) [IsLocallyNoetherian Y]`.
  The notation Reg(Y) is expanded, without a second definition, as
  `{z : Y | IsRegularLocalRing (Y.presheaf.stalk z)}`.
- For any commutative coordinate ring C, E(C) is expanded as
  `{q : PrimeSpectrum C | IsRegularLocalRing (Localization.AtPrime q.asIdeal)}`.
  These expressions use the dependency's regular-local-ring predicate, including
  its local and Noetherian conditions, rather than only the scheme-wide predicate.
- Every affine open is `W : Y.affineOpens`, with coordinate ring `Γ(Y, W)`.
  The first conjunct equates the inverse image of Reg(Y) under the subtype
  inclusion `fun z : (W : Y.Opens) ↦ (z : Y)` with the inverse image of E(C)
  under `W.2.primeIdealOf`. Thus both sides are subsets of W, exactly the
  subspace interpretation of W intersect Reg(Y).
- The canonical chart is the actual Mathlib `IsAffineOpen.primeIdealOf`, whose
  definition is `hU.isoSpec.hom x`, not a supplied or arbitrarily chosen map.
  `isoSpec` is the canonical scheme isomorphism from the affine open to the
  spectrum of its sections, and its underlying map is the required homeomorphism.
- An arbitrary affine open covering is `(J : Type v) (W : J → Y.affineOpens)`
  with `(⨆ j : J, (W j : Y.Opens)) = ⊤`. The second conjunct asserts exactly
  `IsOpen Reg(Y) ↔ ∀ j : J, IsOpen E(Γ(Y,W j))` under that covering hypothesis.
  There is no finiteness or nonemptiness assumption on J.
- The final conjunct quantifies independently over `(B : Type w) [CommRing B]
  [IsNoetherianRing B]`. Points of `Spec (CommRingCat.of B)` are definitionally
  `PrimeSpectrum B`; the equality of set comprehensions is literally
  Reg(Spec B) = E(B) under that canonical identification. The following `↔`
  states the openness equivalence explicitly. No identification with the
  unrelated input scheme Y is assumed or required.
- All three universes u, v, w are declared explicitly. In particular the
  covering index universe is independent of the point universe. There are no
  auto-bound variables, `let` binders, auxiliary assumptions or local notation.

Dependencies and source declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`; the former is a locally
  ringed space with local affine charts, and the latter has prime-spectrum points.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, declaration
  `AlgebraicGeometry.IsLocallyNoetherian`, equivalent to the node's affine-cover form.
- `def-weil-regular-scheme`: imported
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, declaration
  `AlgebraicGeometry.IsRegularScheme`, whose body is
  `IsLocallyNoetherian X ∧ IsRegular X`; its recorded ring clause uses Mathlib's
  `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`.
  This node asks about pointwise regularity, so its set comprehensions use exactly
  that ring predicate on stalks, not regularity of the entire scheme.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- Proof dependency `lem-weil-pbc-affine-open-stalk-localization` is a Mathlib leaf:
  `Mathlib.AlgebraicGeometry.AffineScheme`,
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.fromSpec_primeIdealOf`,
  `IsAffineOpen.isLocalization_stalk`, `IsAffineOpen.isOpenImmersion_fromSpec`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`, its stalk-map isomorphism instance;
  `Mathlib.AlgebraicGeometry.Scheme`, `Scheme.Hom.germ_stalkMap`.
  These modules are imported with proof-only imports where not already public
  statement imports; no replacement of the leaf's canonical map was introduced.
- Proof dependency `lem-trf-regular-local-ring-isomorphism` is a Mathlib leaf:
  `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularLocalRing.of_ringEquiv`.

Sources inspected: `literature/stacks-project/morphisms.tex`, lemma-J
(Tag 07R4), second and final proof paragraphs; and
`literature/stacks-project/schemes.tex`, lemma-spec-sheaves (Tag 01HV),
particularly (1) and (6). The chart equality and arbitrary-union gluing are
exactly the regular-locus argument there, without the unrelated J-2 hypothesis.

Edge cases checked mathematically before writing: an empty scheme, the empty
cover of the empty scheme, an infinite cover, a zero coordinate ring (empty
prime spectrum), a field (one regular point), and the nonregular local ring
k[ε]/(ε²). The latter has an empty regular locus, so the statement makes no
unjustified assertion of regularity or universal openness. Repeated charts are
allowed. No separation, finite type, J-2 or nonzero-ring hypotheses are needed.
No statement fault or dispute was found.

Searches for an existing declaration, using the prescribed msearch.py wrapper:

- LeanFinder: "The regular locus of a locally Noetherian scheme corresponds on
  affine charts to prime localizations that are regular local rings, and openness
  is equivalent on any affine open cover". Eight hits: Noetherian open-cover
  criteria, `Scheme.affineOpens`, `IsAffineOpen` and affine-neighbourhood reduction;
  none states the requested conjunction or regular-locus comparison.
- Loogle: `IsRegularLocalRing, IsOpen`. Zero hits.
- Mathlib grep: `regularLocus|regular_locus|IsRegularLocalRing`, restricted to
  `AlgebraicGeometry`. Zero hits. A direct rg search there confirmed this.
- LeanSearch: "Regular locus comparison on affine charts and openness on affine
  open covers of a locally Noetherian scheme". Eight hits about affine covers
  and Noetherianity, none the requested regular-locus statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for regularLocus, regular_locus,
  regular-locus prose and IsRegularLocalRing found stalkwise regularity,
  regularity under localizations and J-2 criteria. In particular upstream
  `IsAffineOpen.isRegularLocalRing_localization` assumes all stalks on a chart
  regular and is not the pointwise comparison or cover-openness equivalence.
  `Sheaf.AlgebraicGeometry.JTwoAffineCover` states the J-2 consequence and is a
  consumer, not a duplicate. No existing declaration states this whole node.
- rg for the item's id in `lean/WeilConjectures` returned no match. The proposed
  declaration name was also absent from the library and upstream-name index.

Validation: scompile.py compiled both the sandbox and destination module forms
against the published live library, 1.7 seconds each, with no diagnostics.

## Second reading by N7

Author's second reading, as required for direct dispatcher delivery; independent
review is performed by the maintainer. I reopened the node and the exact Lean
signature after compilation and checked the three conjuncts separately.

The first uses the canonical chart's point function and equality on the subtype
W, which faithfully renders the intersection clause on the ambient scheme.
The second quantifies over the full family before imposing exactly the cover
condition, and asserts both directions of openness. The third retains the
Noetherian assumption on B and includes both equality and openness equivalence
on the same prime-spectrum topology. The ring clause's independent universe
adds no constraint on the scheme or cover. No finite/nonempty requirement or
extra regularity assumption slipped in. No definitions or dependency interfaces
needed repair and no mismatch was found; nothing changed on this reading.
