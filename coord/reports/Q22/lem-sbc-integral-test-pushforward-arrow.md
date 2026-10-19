## Worker report

`lean/Sheaf/AlgebraicGeometry/IntegralTestPushforwardArrow.lean` states
`AlgebraicGeometry.Etale.integralTestPushforward_baseChange_arrow`. Its only theorem
has proof `sorry`; it defines no new objects, functors, or base-change maps.
The node copy differs from the base only in `lean`. No node correction is needed.

The statement matches the node hypothesis by hypothesis and clause by clause:

- `Λ : Type (u + 1)` and `[CommRing Λ]` give the arbitrary commutative coefficient
  ring in the established module-sheaf size convention.
- `{X S T Y T' Y' : Scheme.{u}}`, `{p : X ⟶ S}`, `{g : T ⟶ S}`, and
  `(π : T' ⟶ T) [IsIntegralHom π]` give the named schemes and morphisms. The
  composite `g'` is written directly as `π ≫ g`.
- `(sq : ChosenCartesianSquare h e p g)` and
  `(sq' : ChosenCartesianSquare h' e' p (π ≫ g))` give exactly the two fibre
  products and their named projections. The map constructor accepts `IsPullback`
  in the exchanged orientation; the standard `IsPullback.of_iso_pullback` followed
  by `.flip` obtains precisely that proof from the chosen square's recorded data.
- `(r : ℤ)` admits every integer degree.
- The existential `A` is a natural isomorphism from
  `lowerStar (ModuleCat Λ) π ⋙ baseChangeSourceFunctor Λ p g r` to
  `baseChangeSourceFunctor Λ p (π ≫ g) r`. By the recorded source functor, its
  component is the displayed `A_M : p⁻¹ Rʳg_*(π_*M) ≅ p⁻¹ Rʳg'_*M`.
- The existential `B` is a natural isomorphism from
  `lowerStar (ModuleCat Λ) π ⋙ baseChangeTargetFunctor Λ e h r` to
  `baseChangeTargetFunctor Λ e' h' r`. Its component is the displayed
  `B_M : Rʳh_*e⁻¹(π_*M) ≅ Rʳh'_*e'⁻¹M`.
- `∀ M : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)` supplies every module
  sheaf without a torsion or invertibility restriction. Naturality is part of the
  types of `A` and `B`, rather than an unrecorded choice of pointwise isomorphisms.
- The equality is `b_{π_*M} ≫ B.hom.app M = A.hom.app M ≫ b'_M`, exactly
  `B_M ∘ b_{π_*M} = b'_M ∘ A_M` in mathematical composition order. Both arrows
  are the recorded `baseChangeHomologyMap`, without an arbitrary comparison map.
- The signature has no surjectivity, qcqs, positivity, or lower-degree hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `AlgebraicGeometry.IsIntegralHom`,
  the integral clause of `def-weil-finite-integral-morphism` (its finite clause is
  `IsFinite`, whose signature was also checked).
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, with `isoPullback`, `hom_fst`, `hom_snd`
  and the inherited `toCommSq`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the shared category conventions
  `CategoryTheory.Sheaf` and `ModuleCat`, specifically the recorded six-functor
  encoding `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. The locally constant
  predicates in the dependency record are not hypotheses of this item.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and their derived counterparts,
  used through the source and target functors; these define the same pushforward and
  inverse image as the dependency nodes.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`:
  `AlgebraicGeometry.Etale.baseChangeSourceFunctor`, `baseChangeTargetFunctor`,
  `baseChangeHomologyNatTrans`, and `baseChangeHomologyMap`, the map recorded by
  `sk-def-bc`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: retains the original module
  derived map while repairing its abelian/set variants. This statement uses the
  original module map's degreewise presentation, not the abelian-only specialization.

All recorded proof-dependency modules that exist are imported without `public`.
`lem-sbc-integral-morphism-base-change` is the Mathlib stability instance supplied
by the integral import. `sk-lem-pbc-exchange-pasting` has no recorded module, so
there is no import to add for it. Its use is retained in the complete six-step
proof docstring. Each step follows the node: integral base change; exactness and
comparison with a degree-zero pushforward; invertible canonical derived exchange;
canonical composition comparisons; vertical pasting and naturality; and taking
cohomology. The source's Tag 0F04 final paragraph and IntegralBaseChange.lean:95-123
were read against this plan.

Edge cases were checked before settling the signature: `π = 𝟙 T`, a non-surjective
closed immersion, `T'` empty, other empty schemes, `M = 0`, the zero coefficient
ring, `r < 0`, and `r = 0` are all included. Negative-degree higher direct images
vanish, consistently with the stated isomorphisms. No extra coefficient universe
restricts test objects, and all universes and variables are explicitly bound.

Searches and results:

- LeanFinder via `msearch.py`, query "integral pushforward identifies base change
  arrows in every degree": eight generic integral/base-change or pushforward results,
  no natural isomorphism statement for these arrows.
- Loogle via `msearch.py`, query
  `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar, baseChangeHomologyMap`:
  no hits; the upstream identifier is outside the index.
- Indexed grep via `msearch.py`, query
  `nonempty_arrowIso_baseChangeHomologyMap_lowerStar|baseChangeHomologyMap`:
  no Mathlib hit. Direct `rg` of the upstream source located the pointwise theorem
  at `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/IntegralBaseChange.lean:95`.
- Direct `rg` of upstream and `lean/Sheaf` for `baseChangeHomologyNatTrans` and the
  new declaration name found the shared map definitions and unrelated consumers,
  but no theorem stating natural endpoint isomorphisms for integral test-base change.
- The upstream pointwise candidate was read and its type confirmed by `scompile.py`.
  It has `F'` before its conclusion `Nonempty (Arrow.mk ... ≅ Arrow.mk ...)` and
  asserts no naturality of the endpoint isomorphisms. It is therefore insufficient
  for the node's explicit naturality clause. This delivery states that clause using
  existing functors; no duplicate definition or weakened pointwise theorem is added.

Validation: `scompile.py Q22 lem-sbc-integral-test-pushforward-arrow
lean/Sheaf/AlgebraicGeometry/IntegralTestPushforwardArrow.lean` passed both sandbox
and library-path checks with no diagnostics. The only postponed proof is
`AlgebraicGeometry.Etale.integralTestPushforward_baseChange_arrow`.

## Earlier second reading (a previous round; superseded)

Pending the separate second reader required by the dispatch brief. The preceding
checks are the worker's self-check, not an independent review.

## Second reading by Q22

I independently opened the node, its source places, the statement module, and the
recorded statement-dependency declarations. The sandbox contains one module and
one node, with no new nodes or dependency repairs. The node differs from the
shared base only in `lean`; it has no `statement_change` to audit.

My object/hypothesis/conclusion checklist, read against the Lean signature:

1. Arbitrary commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`.
   This is the six-functor module-sheaf encoding explicitly permitted by
   `def-weil-pbc-etale-sheaves`'s record, rather than a restriction to a field,
   torsion coefficients, or coefficients of invertible order. Verdict: matches.
2. Schemes `X,S,T,T',Y,Y'` and morphisms `p,g,e,h,e',h'`: the explicitly bound
   `Scheme.{u}` objects and Hom binders introduce all of them. The composite
   `g'` is `π ≫ g`, with no independently chosen composite. Verdict: matches.
3. Integral `π : T' ⟶ T`: `[IsIntegralHom π]` is precisely the recorded affine,
   affine-locally integral notion; its declaration in Mathlib extends
   `IsAffineHom` and requires `isIntegral_app`. No surjectivity is required.
   Verdict: matches.
4. The two fibre products with the named projections: `sq` and `sq'` have types
   `ChosenCartesianSquare h e p g` and
   `ChosenCartesianSquare h' e' p (π ≫ g)`. I read that structure's
   `isoPullback`, `hom_fst`, `hom_snd`, and inherited commutativity. The
   `IsPullback.of_iso_pullback` terms use exactly those data; `.flip` puts the
   squares in the `e,h,g,p` orientation required by `baseChangeHomologyMap`.
   Verdict: matches, including arbitrary choices of fibre-product identification.
5. Every integer degree: `(r : ℤ)`. Verdict: matches, without positivity or a
   lower-degree base-change hypothesis.
6. The first natural isomorphism: existential `A` compares `lowerStar π`
   followed by `baseChangeSourceFunctor Λ p g r` with
   `baseChangeSourceFunctor Λ p (π ≫ g) r`. Reading the functor definitions gives
   exactly `p⁻¹ Rʳg_*(π_*M) ≅ p⁻¹ Rʳg'_*M`. Verdict: matches.
7. The second natural isomorphism: existential `B` compares `lowerStar π`
   followed by `baseChangeTargetFunctor Λ e h r` with
   `baseChangeTargetFunctor Λ e' h' r`, hence
   `Rʳh_*e⁻¹(π_*M) ≅ Rʳh'_*e'⁻¹M`. Verdict: matches.
8. Every module sheaf `M` on the small etale site of `T'`: the final universal
   binder is `Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. The existential
   witnesses precede this binder and are functor isomorphisms, so both endpoint
   families are natural in every morphism of sheaves, not merely separately
   chosen pointwise isomorphisms. Verdict: matches the naturality clause.
9. Compatibility of the canonical arrows: the left side is
   `baseChangeHomologyMap ... (π_*M) ≫ B.hom.app M`; the right side is
   `A.hom.app M ≫ baseChangeHomologyMap ... M`. In ordinary composition order
   this is exactly `B_M ∘ b_{π_*M} = b'_M ∘ A_M`. Verdict: matches.

Dependency/interface checks: Mathlib's `Scheme` and `Scheme.Hom` supply the
objects and morphisms. `ChosenCartesianSquare` supplies the recorded square,
not a private pullback predicate. In `UpperLowerStar.Defs`, I read `lowerStar`
as precomposition with etale base change and `upperStar` as the left Kan
extension followed by sheafification, with the declared adjunction. These
are the functors of the direct/inverse-image nodes. The etale-sheaves dependency
is a mixed record: its locally constant predicates are irrelevant here, while
its note explicitly supplies the module-valued sheaf encoding being used. Its
source was absent from the older checkout, so I also read the current source
with `scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
I read `baseChangeSourceFunctor`, `baseChangeTargetFunctor`,
`baseChangeHomologyNatTrans`, and `baseChangeHomologyMap` in the recorded
`SmoothBaseChange.Defs`. They use bounded-below derived functors on sheaves in
degree zero, exactly the higher-direct-image convention of the dependency node.
The existing `baseChangeSourceFunctorIso` and `baseChangeTargetFunctorIso` in
`SmoothBaseChange.Coefficients` confirm the endpoint identifications.
`BaseChangeMapAbelianAndSets` retains the module map by importing its original
module; its abelian/set helper arrows do not replace the map used here.

Source check: I read `etale-cohomology.tex`, Tag 0F04, including the surrounding
definition of BC and the entire lemma/proof. Surjectivity, qcqs, annihilation by
`n`, `q ≥ 1`, and lower-degree BC occur in the surrounding descent application;
the three identifications in its last paragraph use integral exactness and
integral exchange. I checked those in Tags 04C2 and 0EYP, which assume only an
integral morphism and a Cartesian square. I also read the arbitrary-ring arrow
statement and construction at `IntegralBaseChange.lean:95-123`: it explicitly
has no additional assumptions. The six-step proof docstring faithfully carries
the node's construction of `k`, exactness and degree-zero comparison, canonical
derived integral exchange, composition isomorphisms, pasting/naturality, and
cohomology. The proof-only imports cover the recorded modules; the unstated
`sk-lem-pbc-exchange-pasting` has no module to import.

Edge cases: identity `π`, non-surjective integral closed immersions, `T'` empty
and other compatible empty schemes, the zero sheaf, the zero ring, degree zero,
and negative degrees are all admitted. There is no characteristic assumption,
finiteness condition on coefficients, or nonempty indexing type. Universes and
variables are bound explicitly; the coefficient size follows the shared
six-functor convention and adds no independent small test-object quantifier.

Independent searches used different wording from the worker: LeanFinder query
"natural isomorphism between higher direct image base change transformations
under integral pushforward" and LeanSearch query "Naturally isomorphic
cohomological etale base change arrows after integral direct image of module
sheaves" returned generic pushforward, differential, and ordinary base-change
lemmas, not this statement. Loogle `CategoryTheory.Sheaf, "integral"` and
indexed grep `integral.*[Nn]at[Ii]so|[Nn]at[Ii]so.*integral|integralTestPushforward`
returned no matches. An initial Loogle query used an unknown `NatIso`
identifier; the valid sheaf query replaced it. Direct `rg` across pinned
Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for integral
arrow comparisons and the base-change functor/map names found two nearby
candidates, which I opened: upstream
`nonempty_arrowIso_baseChangeHomologyMap_lowerStar` is pointwise in `F'` and
does not assert naturality; project `integralPushforward_baseChange_arrow`
concerns the other operation, integral change of the base of `p`, with abelian
coefficients and nonnegative degrees. Neither is an exact existing match.

Mismatches found: none. I preserved the Lean module and node record and added
only this independent review and its searches. The signature was checked
verbatim against `lean.statement`; all lines are at most 100 characters. There
are no private definitions, file-local notation, extra proved theorems, or
hollow constructions; the single postponed theorem has its source, blueprint
identifier, and complete proof plan.

Independent validation: the required `scompile.py Q22
lem-sbc-integral-test-pushforward-arrow
lean/Sheaf/AlgebraicGeometry/IntegralTestPushforwardArrow.lean` passed both
the sandbox and library-path checks, with no diagnostics (3.9 s and 4.3 s).
