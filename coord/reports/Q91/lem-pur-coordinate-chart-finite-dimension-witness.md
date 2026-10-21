## Worker report

The module `Sheaf.AlgebraicGeometry.CoordinateChartFiniteDimensionWitness` states
`AlgebraicGeometry.Scheme.Hom.exists_coordinate_chart_finite_dimension_witness`.
Its only proof is `sorry`; there are no new definitions, axioms or helper theorems.
The node's statement and nine proof steps are unchanged. The declaration docstring
contains those nine steps and identifies their supporting DAG nodes.

### Hypotheses and conclusions

All schemes are `Scheme.{u}`, with explicit universe `u` and `autoImplicit false`.
The map `p : X ⟶ S` fixes the arbitrary base. The base maps on `Y`, `T` and `Z`
are respectively `i ≫ p`, `e ≫ p`, and `pullback.fst i e ≫ i ≫ p`.
These are the induced structures in the given chart; no independently chosen
base map or additional compatibility hypothesis is introduced. The pullback
condition identifies the two routes from `Z` to `S`.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary schemes `S`, `X`, `Y` and etale chart source `T` | `{S X Y T : Scheme.{u}}`, `p : X ⟶ S` |
| Closed immersion `i : Y → X` | `i : Y ⟶ X`, `[IsClosedImmersion i]` |
| Etale `e : T → X` | `e : T ⟶ X`, `[Etale e]` |
| `Z = Y ×_X T` | The actual scheme `pullback i e`; its projections are `pullback.fst i e` to `Y` and `pullback.snd i e` to `T` |
| Nonnegative integers `a`, `b` | `(a b : ℕ)`, including both zero cases |
| Etale `S`-map to affine `(a+b)`-space | `h : T ⟶ AffineSpace (ULift.{u} (Fin (a+b))) S`, `[Etale h]`, and `coordinatesOver` equating its structure composite with `e ≫ p` |
| Scheme-theoretic inverse image of the first `a` coordinate subspace | `g : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S` and `cartesian : IsPullback g (pullback.snd i e) (AffineSpace.homOfVector …) h`, where `Fin.addCases` retains the first `a` coordinate sections and sets the last `b` to zero |
| `Z` nonempty | `nonemptySupport : Nonempty (pullback i e : Scheme.{u})` |
| An affine open `S₀ = Spec R` | `∃ (U : S.Opens) (hU : IsAffineOpen U)`; `R` is the actual section ring `Γ(S,U)`, and `hU.fromSpec` is its canonical open immersion into `S` |
| A minimal prime `s` and point `t ∈ Z` over it | `s : PrimeSpectrum Γ(S,U)`, `t : (pullback i e : Scheme.{u})`, `s.asIdeal ∈ minimalPrimes Γ(S,U)`, and `(pullback.fst i e ≫ i ≫ p) t = hU.fromSpec s` |
| `κ(s) = Frac(R/s)` | `Nonempty (s.asIdeal.ResidueField ≃+* FractionRing (Γ(S,U) ⧸ s.asIdeal))`; Mathlib also supplies the `IsFractionRing` interpretation of this residue field |
| Generic image in `A^a_κ(s)` | `IsGenericPoint ((AffineSpace (ULift.{u} (Fin a)) S ↘ S).asFiber (g t)) Set.univ`; this is in the actual fibre of the relative affine space, canonically `A^a_κ(s)` |
| `y` and `x` are the prescribed images | `y` is written explicitly as `(pullback.fst i e) t`; `x` is `i ((pullback.fst i e) t)`. The point of `T` is `(pullback.snd i e) t` |
| `dim O_Z,t = dim O_Y,y = 0` | The first two `ringKrullDim ... = 0` conjuncts |
| `dim O_T,t = dim O_X,x = b` | The next two `ringKrullDim ... = (b : WithBot ℕ∞)` conjuncts |
| Preservation of prime-poset dimensions in passage to each fibre local ring | Four further equalities of `ringKrullDim`, one each for `Z`, `Y`, `T` and `X`, using each structure map's actual `.fiber` and `.asFiber` |
| Ambient affine-space fibre local ring `κ(s)(u)[v]_(v)` | An existential prime `q` of `MvPolynomial (Fin b) (FractionRing (MvPolynomial (Fin a) s.asIdeal.ResidueField))`, constrained by `q.asIdeal = Ideal.span (Set.range MvPolynomial.X)`, and a ring equivalence between the actual ambient affine-space fibre stalk at the image of `t` and `Localization.AtPrime q.asIdeal` |
| No further geometric finiteness or regularity assumptions | No `IsNoetherian`, `IsReduced`, finite dimension, `Smooth` or `LocallyOfFiniteType` binder occurs |

Genericity uses the point of the target fibre corresponding to `g t`. This is the
image of the corresponding point of `Z_s`: both descriptions have projection
`g t`, and `fiberι` embeds the fibre topologically. The base points coincide by
`cartesian` and `coordinatesOver`. The same observation identifies the ambient
fibre point with the image under `h_s`. Using actual fibres avoids a new private
base-change or affine-space comparison construction. Finite polynomial rings
with `Fin a`/`Fin b` give the rational-function/localized-ring model independently
of the harmless `ULift` used for the relative affine-space coordinate type.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, including
  `Etale.etale_isStableUnderBaseChange` and the projection instances.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `AlgebraicGeometry.baseChange_morphism_projections`; its recorded conventions use
  the actual `Limits.pullback` scheme and its two projections, as this file does.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, its
  structural projection, `SpecIso` and `isPullback_map`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, whose value is in
  `WithBot ℕ∞` and measures strict prime-chain lengths.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace.homOfVector` and
  `AffineSpace.coord` give the coordinate-subspace inclusion inline. The vector
  uses `Fin.addCases` to retain the first coordinates and set the last ones to zero.
  No theorem from `SmoothPairLocalCoordinates` is needed or imported.

The proof-only imports retain the recorded plan:
`Scheme.Hom.isOpenMap` in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Ideal.exists_minimalPrimes_le` in `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`,
`IsAffineOpen.fromSpec`, `primeIdealOf` and `isLocalization_stalk` in
`Mathlib.AlgebraicGeometry.AffineScheme`, `Localization.AtPrime` and
`Ideal.ResidueField`, `MvPolynomial.polynomial_origin_regularLocal` in
`WeilConjectures.RingTheory.PolynomialOriginRegularLocal`,
`RingHom.Etale.ringKrullDim_localization_eq` in
`WeilConjectures.RingTheory.Etale.LocalDimension`,
`Ring.KrullDimLE.of_isLocalization` and `nilradical_eq_maximalIdeal` in
`Mathlib.RingTheory.KrullDimension.Zero`, and
`Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv` in
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`.
Their full recorded signatures and explanatory docstrings were read. In particular,
the ring etale-dimension theorem has no Noetherian hypothesis, and the fibre-stalk
quotient theorem specifies the canonical projection and its kernel.

### Edge cases and sources

- `a = 0`: the tangential polynomial ring has no variables, and its fraction field
  is the base residue field. Genericity is the unique point of its spectrum.
- `b = 0`: the variable ideal is zero in a field; both ambient dimensions are zero.
- The empty support is precisely excluded by `nonemptySupport`. An empty base or
  an empty `Y` cannot satisfy that hypothesis; no nonempty-base assumption is added.
- Nilpotents on the base are allowed. The proof needs a nil ideal at a minimal prime,
  not a nilpotent ideal with a common exponent. Infinite dimensions elsewhere are
  permitted by `WithBot ℕ∞`.
- The witness is one point in one affine base open, with no connectedness,
  quasi-compactness or finite-dimensionality assumption on the original schemes.
- `q` is not an arbitrary localization prime: its equality with the whole variable
  ideal is a required conjunct. Its primality is supplied by the existential prime
  spectrum element, not a new assumption or data chosen from an unproved theorem.

Sources read: the node's full nine-step witness argument; local Stacks
`morphisms.tex`, `lemma-smooth-open` (056G);
`more-algebra.tex`, `lemma-dimension-etale-extension` (07QP);
`schemes.tex`, `lemma-local-ring-fibre` (0HA1); and
`algebra.tex`, `lemma-minimal-prime-reduced-ring` (00EU) and
`lemma-dim-affine-space` (00OP). Also read the current blueprint's
`sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md`, whose first
paragraph is the etale-local comparison context recorded by this node.
The node correctly describes 056G as supporting the openness step, not as a tag
asserting the entire witness.

### Searches performed

All service searches used the prescribed `msearch.py Q91` wrapper for this item.

- LeanFinder: `A nonempty etale coordinate chart of a closed immersion has a point
  over a minimal base prime with local dimensions zero and codimension`.
  Eight general etale-locus, residue-field and closed-immersion hits; none states
  the combined witness.
- Loogle: `AlgebraicGeometry.Etale, ringKrullDim`. Zero hits.
- Mathlib grep service: `coordinate.*[Dd]imension|[Ee]tale.*[Dd]imension`, under
  `AlgebraicGeometry`. Five hits in `Morphisms/Etale.lean`, about equivalence with
  smooth relative dimension zero; no witness.
- LeanSearch: `Nonempty etale coordinate subspace chart contains a point over a
  minimal base prime where ambient local rings have dimension the number of
  normal coordinates`. Eight hits including `Algebra.exists_etale_of_isEtaleAt`,
  `Algebra.IsEtaleAt`, etale loci, and unrelated manifold chart statements; no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `coordinate.*[Cc]hart|[Cc]oordinate.*[Ss]ubspace|finiteDimensionWitness|coordinate_chart`:
  found the existing `RelativeSupportCoordinates` and `zeroLastCoordinates`
  interfaces, but no complete witness. `RelativeSupportCoordinates` has smoothness
  and a chosen ground field, so it cannot replace this arbitrary-base statement.
- `rg` over `lean/WeilConjectures` for this item's exact id: no matches.
- `rg` over both source roots and `dag/lean_names_upstream.json` for
  `finite.*dimension.*witness|coordinate_chart_finite|coordinateChartFinite`:
  no matching declaration (one unrelated finite-dimensional-complex comment).
- `rg zeroLastCoordinates` in the DAG and project source identified the helper in
  `SmoothPairLocalCoordinates`. On repair, its definition and the inline inclusion
  in `SmoothClosedCoordinateLift` were read alongside Mathlib's `homOfVector`:
  the same concrete Mathlib construction can be written inline without adding the
  smooth-pair theorem to the statement dependencies.

There is no statement dispute, source correction, new node, or dependency repair.
The repaired node changes only its Lean record; `stmt_deps` equals the base list.

### Validation

`scompile.py Q91 lem-pur-coordinate-chart-finite-dimension-witness` compiled the
complete final module twice, as a sandbox module and under its actual library
module name. The repaired module succeeded with no errors or warnings (3.3 s and 2.6 s).
The initial elaboration diagnosed an implicit category choice for the carrier
binder; the final binder explicitly gives `(pullback i e : Scheme.{u})`.
All lines are at most 100 characters, and the only theorem body is `by sorry`.

## Second reading by Q91

I reopened the node and final module for a separate clause audit after compilation.
This is a rereading by the single dispatcher worker; the independent maintainer
review follows delivery, as the brief specifies. No additional agent was started.

The affine witness supplies an actual affine open, a minimal prime in its actual
section ring and a point of the actual pullback. The image equation places the
point over that prime. Genericity is in the target affine-space fibre, not in
`Z_s`; imposing genericity in `Z_s` would have been an incorrect strengthening.
Each of `Z`, `Y`, `T` and `X` has its own original stalk dimension and its own
fibre-stalk comparison. The ambient local ring is the target affine-space fibre
stalk, not the generally different etale source stalk; its comparison ring is
localized at exactly the normal variable ideal. The coordinate-square hypothesis
is categorical `IsPullback`, so no equality of mere point sets is substituted.
The inline zero-last-coordinate map is definitionally the existing helper, with no smoothness assumption.
The two zero-coordinate edge cases and a nonreduced, non-Noetherian base remain
in scope. No mathematical mismatch or statement change was found in this audit.

## Repair of return H2

The immutable returned head was `cfbce1bdee09`. The retained packet had added
`lem-pur-smooth-pair-local-coordinates` solely to obtain its concrete coordinate
inclusion helper. The initial saved-packet dry run passed as `0423b22e0b9`, but
that mechanical result does not address the independent review's H2 objection.

Applied option (a) of the return: removed the added statement dependency and
`SmoothPairLocalCoordinates` import. The cartesian-square hypothesis now writes
`AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)` with the vector
`fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k)) (fun _ ↦ 0) j.down`.
This is the exact body of `AffineSpace.zeroLastCoordinates`, and matches the
existing inline construction in `SmoothClosedCoordinateLift`.

A fresh clause audit confirms that the affine open, minimal prime, point over it,
residue-field comparison, generic image in the actual tangential fibre, four
local dimensions, four fibre-dimension comparisons, and ambient fibre-stalk
comparison with the prime pinned to the normal variable ideal are unchanged.
The proof remains only `sorry` and both docstrings are unchanged. Both `a = 0`
and `b = 0` remain admitted, as do nonreduced and non-Noetherian bases.
No new nodes or definitions were introduced. Against the current read clone,
the repaired node has no changes outside `lean`; the delivery wrapper rebases
and validates the packet against the live server branch.

Repair validation: the prescribed `scompile.py` compiled the repaired file in
sandbox and library modes in 3.3 s and 2.6 s, with no errors or warnings. The
self-check confirms the exact signature record, unchanged non-Lean node fields,
100-character line width, explicit universe, disabled auto-implicits and sole
`sorry` proof. The full final delivery is checked again by `deliver2.py --no-push`
before pushing.
