## Worker report

Stage 2, Q54. The module `Sheaf.AlgebraicGeometry.OpenRelativeLinePrincipalGeometry`
states `AlgebraicGeometry.openRelativeLine_principal_geometry`. Its sole theorem has
proof `sorry`; there are no definitions, new nodes, dependency repairs, or statement
corrections. The source node is unchanged except for its Lean attachment. The previous
worker's stage-1 “already split and reviewed” refusal is not a stage-2 completion:
the live node has a reviewed split but no Lean attachment. The retained sandbox had
only dispatcher marker files, with no previous Lean packet to reuse.

Source read: Stacks `more-etale.tex`, Tag 0GKY,
`lemma-loc-constant-shriek-rel-dim-1` and its Noetherian-open reduction;
`morphisms.tex`, Tags 01T6 (`lemma-finite-type-noetherian`), 01VC
(`lemma-open-immersion-smooth`), 02NL (`lemma-composition-relative-dimension-d`);
`schemes.tex`, Tag 01I3 (`lemma-standard-open-affine`). Read all eight node proof
steps and all statement-dependency statements and their recorded interfaces.
The general geometry lemma does not require the finite-dimension/coefficient
hypotheses of the cohomological 0GKY result: its cited general scheme lemmas give
precisely the node's geometry for every Noetherian affine base.

Hypothesis and clause correspondence:

- `R : CommRingCat.{u}` supplies an arbitrary commutative ring; the base is exactly
  `Spec R`. `[IsNoetherian (Spec R)]` means locally Noetherian plus quasi-compact,
  since Mathlib's class extends `IsLocallyNoetherian` and `CompactSpace`.
- The line is the node's explicit affine model `Spec (.of (Polynomial R))`.
  Its projection is `Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))`,
  the canonical coefficient inclusion. This is the one-variable affine chart of
  the recorded relative-affine-space notion, not an arbitrary structure map.
  `U : (Spec (.of (Polynomial R))).Opens` supplies the arbitrary open subscheme,
  with its canonical restricted structure sheaf `U.toScheme` and inclusion `U.ι`.
- The first four conjuncts give `IsNoetherian` and `QuasiSeparatedSpace` for both
  the ambient line and `U.toScheme`. No extra quasi-compactness assumption is
  imposed: quasi-compactness is contained in `IsNoetherian`.
- `IsSeparated (U.ι ≫ Spec.map ...)` is the restricted separated projection.
  The next conjuncts `LocallyOfFiniteType` and `QuasiCompact` together mean
  finite type, in the recorded scheme conventions (there is no bundled
  Mathlib finite-type scheme-morphism predicate).
- `∃ (r : ℕ) (s : Fin r → Polynomial R)` supplies the finite polynomial family,
  allowing `r = 0`. `∀ i, PrimeSpectrum.basicOpen (s i) ≤ U` is containment,
  and `U = ⨆ i, PrimeSpectrum.basicOpen (s i)` is equality of open subschemes.
  `PrimeSpectrum.basicOpen` is exactly the locus of primes not containing the
  given polynomial, equipped here with the canonical open-scheme structure.
- For each finite nonempty subfamily `J : Finset (Fin r)`, `J.Nonempty → ...`
  states its intersection equals `PrimeSpectrum.basicOpen (∏ i ∈ J, s i)` and
  `IsAffineOpen` of that intersection. Nonempty means a nonempty subfamily,
  not a nonempty intersection; empty resulting intersections are included.
  A subfamily uses distinct indices, as usual; repeated indices in a list do
  not change the intersection and the corresponding basic-open product
  identity still follows from the basic-open identities.
- The next universal clause treats every `s : Polynomial R`: its principal
  open is affine, and its canonical projection to `Spec R` has `IsAffineHom`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `SmoothOfRelativeDimension 1`. In particular, combined with the preceding
  intersection equality, this supplies every listed projection property
  for each finite intersection. No nonemptiness assumption is used.
- The final universal clause supplies arbitrary `T : Scheme.{u}` and
  `g : T ⟶ D(s).toScheme`, assumes exactly `IsFinite g` and `Etale g`, and
  takes `V : T.Opens` with `IsClosed (V : Set T)`. This expresses precisely
  an open-and-closed subscheme with restricted structure sheaf.
  `IsAffine V.toScheme ∧ IsNoetherian V.toScheme` is its scheme geometry.
  The five following morphism predicates apply to the actual composite
  `V.ι ≫ g ≫ D(s).ι ≫ Spec.map (CommRingCat.ofHom Polynomial.C)` and express
  affine, separated, finite type, smooth of relative dimension one.

Dependency declarations used (read their full signatures and docstrings):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Scheme.Opens`,
  `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; `IsNoetherian` combines it with
  `CompactSpace`, the match of `def-weil-pbc-quasi-compact-scheme`
  (`Mathlib.Topology.Defs.Filter`).
- `def-nagata-relative-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace`. The statement uses its specified affine
  one-variable model `Spec R[t]`; the module is imported for the recorded
  dependency and the stage-3 affine-space smoothness proof.
- `def-weil-pbc-scheme-conventions` defines no independent notion: use
  `AlgebraicGeometry.IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` and
  `AlgebraicGeometry.LocallyOfFiniteType` plus `AlgebraicGeometry.QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom` (preimages of affine opens are affine).
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` (standard-smooth charts of
  the specified relative dimension).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; only the finite notion is needed here.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.

Proof imports retain the stated proof dependencies: the affine-space smoothness
instance `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`; the bridge
`AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale` in
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`; the Mathlib permanence,
immersion, finite, proper, and Noetherian APIs used in the eight-step proof plan.
The docstring records every step, with the matching DAG names. There is no
private replacement of a dependency notion and no import cycle.

Edge cases checked: the zero ring (empty base and line), `U = ⊥` with the
possible cover `r = 0`, `s = 0` or nilpotent (empty principal open), `s = 1`
(the whole line), empty intersections of nonempty subfamilies, repeated factors,
`T` empty, `V = ⊥`, and non-surjective finite étale maps. No nonzero-ring,
nonempty-space, cover-nonempty, surjectivity, or connectedness hypothesis occurs.
Relative dimension one is vacuous at points of an empty source, as required.
The one universe `u` for rings and schemes is the usual scheme category size
and does not impose any site/coefficient universe restriction. Auto-bound
implicits are disabled explicitly with `set_option autoImplicit false`.

Searches actually executed through `msearch.py`, recorded in `searches.jsonl`:

- LeanFinder: “Open subsets of the relative affine line over a noetherian ring
  have finite principal open covers and affine smooth relative dimension one
  finite etale clopen covers”. Eight results: general affine covers, an
  affine-basis cover, Noetherian affine-cover criteria, affine-space open-map
  geometry, and an affine-transition-limit auxiliary declaration. None states
  the full conjunction or its finite étale clopen clause.
- Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.IsNoetherian`.
  Completed successfully with zero hits.
- Mathlib grep: `principal.*cover|open.*relative.*line|finite.*etale.*clopen`,
  subdirectory `AlgebraicGeometry`. Completed successfully with zero hits.
- Project source `rg` searched `principal.*[Gg]eometry|principal.*[Cc]over|openRelativeLine|open_relative_line`
  in `lean/WeilConjectures` and `lean/Sheaf`. The returned cover/descent and
  constructibility declarations do not state this geometry conjunction.
  The prescribed node-id grep in `lean/WeilConjectures` returned no match.
  Exact-name search for `openRelativeLine_principal_geometry` in Mathlib,
  both project roots and `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py Q54 lem-weil-pbc-open-relative-line-principal-geometry`
compiled the delivered module on the live server, both sandbox and real module
contexts, with no errors or warnings. Initial invalid field notation for
principal opens was repaired by explicitly specifying the ambient scheme in
`Scheme.Opens.ι` and `Scheme.Opens.toScheme`; no mathematical statement changed.
The final theorem proof remains `sorry`. Required dry run and delivery follow.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
