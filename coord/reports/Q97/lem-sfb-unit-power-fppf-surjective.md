## Worker report

Item: `lem-sfb-unit-power-fppf-surjective`; group Q97; stage 2.

The module `Sheaf.AlgebraicGeometry.UnitPowerFppfSurjective` states
`AlgebraicGeometry.Scheme.exists_fppf_cover_unit_pow_eq` with `sorry` as its
only proof. It introduces no definitions and changes only the item's `lean`
record. No dependency repairs, new nodes, or statement corrections are needed.

Source read: `literature/stacks-project/etale-cohomology.tex`, Tag 040N,
`lemma-kummer-sequence-syntomic`, statement and complete proof, lines 2920–2966.
The source adjoins a root by `A[X]/(X^n-a)` and obtains a finite free, surjective
cover. The node already imposes positivity, repairing the source's displayed
`n ∈ ℕ` at `n = 0`; this delivery preserves that accepted statement. The node
asks for the fppf conclusion, which follows from flatness and finite presentation
without the source's stronger syntomic assertion.

Clause-by-clause correspondence:

- The scheme `S` is `(S : Scheme.{u})`. An arbitrary `S`-scheme `T` is
  `(T : Over S)`; `T.left` is its underlying scheme and `T.hom` its structure
  morphism. Mathlib's `Over S` is the category of schemes over `S`, with its
  commuting triangles, rather than just a family of underlying schemes.
- The integer `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`. Positive integers have this
  exact natural-number encoding. In particular, there is no invertibility,
  characteristic, nonzero-ring, or finite-type assumption on `S` or `T`.
- `G_m(T) = Γ(T,O_T)^×` is used directly as `(a : Γ(T.left, ⊤)ˣ)`.
  This is Mathlib's group of units of the actual global section ring, not a
  newly introduced object with prescribed properties.
- The family of `S`-schemes and `S`-morphisms is the existential
  `(I : Type u) (U : I → Over S) (f : ∀ i : I, U i ⟶ T)`.
  `Over.Hom.left` gives each underlying morphism to `T.left`, and the over
  category includes its compatibility with `S` in its definition.
- Flatness is `(∀ i : I, Flat (f i).left)`, using the exact recorded
  dependency declaration. `Flat.iff_flat_stalkMap` identifies this with the
  dependency node's stalkwise definition.
- Local finite presentation is
  `(∀ i : I, LocallyOfFinitePresentation (f i).left)`, using the recorded
  declaration with its affine-local finite-presentation condition.
- Joint surjectivity is
  `∀ t : T.left, ∃ (i : I) (x : (U i).left), (f i).left x = t`.
  There is no claim that each individual member is surjective.
- The roots are `(b : ∀ i : I, Γ((U i).left, ⊤)ˣ)`, so they really are units.
  Their equations are
  `∀ i : I, b i ^ n = Units.map (f i).left.appTop.hom.toMonoidHom a`.
  `Scheme.Hom.appTop` is the contravariant map on global sections and
  `Units.map` is its canonical homomorphism on units. Thus the right side is
  exactly `a|_{T_i}`, with equality in the unit group.
- The node's “Equivalently” sentence is rendered by its explicit
  covering-family formulation: each target section has a lift locally on
  a jointly surjective flat locally finitely presented family. This is the
  meaning of local surjectivity of the multiplicative fppf power map, not
  a separate additional hypothesis or a choice of an arbitrary map.
- No assumption says `I` is nonempty. The index universe is the same `u`
  as the schemes' point and ring universes. This accommodates the empty
  family and the affine-cover construction, whose cover can be indexed
  by points. `u` is explicitly declared; all binders are explicit, with no
  auto-bound variables or independent smaller test-scheme universe.

Statement dependencies read in full, including their actual source signatures
and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  declaration `AlgebraicGeometry.Flat`, and `Flat.iff_flat_stalkMap`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, declaration
  `AlgebraicGeometry.LocallyOfFinitePresentation`.

The public auxiliary imports expose existing general machinery:
`Mathlib.CategoryTheory.Comma.Over.Basic` (`Over`, `Over.Hom.left`) and
`Mathlib.Algebra.Group.Units.Hom` (`Units.map`). `Scheme.Hom.appTop` is
already in the recorded scheme module. No missing notion needs a new node.

All twelve proof-dependency node statements and records were read. Their
Mathlib interfaces are included by plain proof imports where they are not
already public statement imports: `AffineScheme` (affine-open basis and
canonical spectra of affine opens), `OpenImmersion`, `AdjoinRoot` (monic
power basis and finite free module), `Algebra.Module.FinitePresentation`,
`Algebra.Module.Projective`, `RingTheory.Flat.Basic`, and
`RingTheory.Flat.FaithfullyFlat.Basic` / `.Algebra` (faithful flatness and
surjective spectrum). Flat composition and the affine-flat equivalence
are in the public flatness import; affine spectrum is in the public scheme
import. The theorem docstring records all five proof steps and their node
names, including the explicit inverse `a_i⁻¹ X^(n-1)` and empty-scheme case.

Edge cases checked before writing:

- `n = 1`: the identity cover with the original unit is a witness.
- `n = 0` is correctly excluded; for example, the unit `2` on `Spec ℚ`
  cannot locally equal a zeroth power on a jointly surjective cover.
- If the characteristic divides `n`, `X^n-a` may be inseparable or
  nonreduced. Its monic quotient remains free of positive rank; the fppf
  conclusion remains valid. No étale condition was added.
- Empty `T` (including the spectrum of the zero ring) permits the empty
  family; joint surjectivity and all equations are then vacuous.
- A general nonaffine, non-quasi-compact `T` is allowed. The family is not
  required finite, and sources are not required affine or quasi-compact.
- The result is uniform in `u`; neither a nonempty index set nor a finite
  point set nor a lower-universe test family is imposed.

Searches actually run:

- `msearch.py ... leanfinder` with query “Positive power maps on units of
  global sections of schemes are locally surjective for flat locally
  finitely presented covers”: eight hits, on jointly surjective
  precoverages, scheme surjectivity, local representability and flat
  descent. No statement about roots of arbitrary global units.
- `msearch.py ... loogle` with query `"Units", "pow", "Surjective"`:
  zero hits.
- `msearch.py ... grep` with query
  `Kummer|power.*surjective|surjective.*power`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` with query “Every unit on a scheme has an
  nth root after a flat locally finitely presented covering for a positive
  integer n”: eight hits, on roots of unity, local nilpotence, powers of
  units and localizations. None states the desired covering assertion.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for Kummer, unit powers,
  fppf surjectivity and root covers found the upstream
  `AlgebraicGeometry.Scheme.exists_etale_surjective_pow_eq_appTop` in
  `WeilConjectures.AlgebraicGeometry.Sites.Kummer`, lines 98–138. I opened
  its full signature and docstring. It assumes `IsUnit (n : Γ(U, ⊤))`,
  so it does not supply this node's arbitrary-characteristic assertion.
  The related Kummer sequence and fundamental-group covers likewise use
  invertible exponents. No exact fppf unit-power statement was found.
- `rg` for the item id in `lean/WeilConjectures` found no declaration.
  Searches for `unit-power-fppf`, `fppf.*[Rr]oot`, `[Rr]oot.*fppf`,
  `flat.*pow_eq`, and `pow_eq.*flat` across both source trees and
  `dag/lean_names_upstream.json` found none. The final declaration name
  and module path were also checked for collisions in those locations.

Validation: prescribed `scompile.py Q97 lem-sfb-unit-power-fppf-surjective`
compiled the file both as a sandbox module and at its library module path,
with exit code 0 and no errors or warnings. Every theorem proof is `sorry`.
No statement dispute or source-interface fault remains.

## Second reading by Q97

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
