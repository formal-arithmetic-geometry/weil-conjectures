## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralPushforwardBaseChangeArrow` states
`AlgebraicGeometry.Etale.integralPushforward_baseChange_arrow`, with its entire proof
`sorry`. It introduces no definitions, instances or axioms. The node is unchanged except
for its `lean` record. No new nodes or dependency modules are needed.

Sources read: Stacks `etale-cohomology.tex`, Tag 0F05,
`lemma-base-change-q-integral-bottom`, especially its two displayed pushforward
identifications and the following sentence identifying the maps; Tag 04C2,
`lemma-what-integral`, especially exactness (4). The upstream
`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/IntegralBaseChange.lean`,
lines 164–213, supplies the precise arrow-level formulation and pasting argument.
The statement is the pushforward identification in that proof, which does not use the
lower-degree BC hypothesis or the torsion hypothesis of the surrounding lemma.

Hypothesis and clause correspondence:

- Schemes `X'`, `S'`, `S''`, `X''`, `T`, `Y` are explicit `Scheme.{u}` binders.
  The maps `f'`, `f''`, `π'`, `g'`, `h'`, `e`, and `π` have exactly the node's domains
  and codomains. All universes and variables are explicitly bound.
- Integral `π` is `[IsIntegralHom π]`. The two assumptions on `g'` are
  `[QuasiCompact g']` and `[QuasiSeparated g']`. Neither is replaced by an assumption
  on another morphism, and there are no finiteness assumptions on the schemes.
- `sqπ : ChosenCartesianSquare π' f'' f' π` and
  `sq : ChosenCartesianSquare h' e f'' g'` give the specified fibre-product
  identifications and projection equations using the recorded square notion.
  Their exchanged commutative squares are composed with `vert_comp`; thus the outer
  square has arrows `e`, `h' ≫ π'`, `g' ≫ π`, `f'`. These are exactly the node's
  `h = π' ∘ h'` and `g = π ∘ g'`. There is no extra Cartesian-square hypothesis.
- `q : ℕ`, coerced to `ℤ` in `homologyFunctor`, covers exactly all `q ≥ 0`.
- The functors have source `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  The final conjunct explicitly binds every sheaf `F` in that category. There is
  no module coefficient choice, torsion restriction, or chosen resolution hypothesis.
- Write `b` for the expression `Functor.whiskerLeft
  (DerivedCategory.Plus.singleFunctor _ 0) (Functor.whiskerRight
  (derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq.flip)
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)))`, and write `B` for the identical
  expression with the vertically composed square. These names are explanatory only;
  the signature contains their full expressions. The existing bounded-below exchange
  is the abelian degreewise presentation of the recorded base-change map. Its
  single-functor input is precisely `F[0]`, and its homology is precisely degree-q BC.
- The first conjunct is `Nonempty (Arrow.mk (Functor.whiskerRight b
  (lowerStar AddCommGrpCat π')) ≅ Arrow.mk B)`. The arrows here are natural
  transformations in the functor category of abelian sheaves. The left component of
  this arrow isomorphism is the natural isomorphism from
  `π'_* (f'')⁻¹ R^q g'_*` to `(f')⁻¹ R^q (g' ≫ π)_*`; its right component is the
  natural isomorphism from `π'_* R^q h'_* e⁻¹` to `R^q (h' ≫ π')_* e⁻¹`.
  The endpoints are written as the homology of the corresponding derived composites,
  canonically the displayed sheaves by exactness of inverse image. The two-sided
  inverse laws for the arrow isomorphism make both component natural transformations
  invertible, and its commuting-square condition is precisely
  `π'_*(BC_inner) ≫ D.hom = C.hom ≫ BC_outer` in Lean composition order.
  Thus naturality in `F` and the arrow identity are included, not only pointwise
  isomorphism of the endpoints.
- The second conjunct says for every such `F` that invertibility of degree-q homology
  of the inner exchange implies invertibility of degree-q homology of the outer
  exchange. This is exactly the last sentence of the node. It does not assert the
  converse or require conservativity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Integral`,
  `AlgebraicGeometry.IsIntegralHom`: the affine-local integral condition.
  The same dependency node's `IsFinite` signature in `Morphisms.Finite` was also read;
  finiteness is not used by this item.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`,
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`, and its imported
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`: chosen Cartesian identifications and
  the canonical inverse-image comparison. Both square modules were read in full.
- `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`, and
  `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`: abelian sheaves on the small etale site.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`;
  and `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`,
  `rightDerivedLowerStarPlus`: these are the recorded direct/inverse-image functors.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMap`: the recorded base-change map;
  `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, is its existing bounded-below
  exchange presentation, as described in the dependency's record. The imported
  `DerivedComparison` identifies this with the bounded derived mate. We do not
  specialize the unbounded monoidal construction directly to `AddCommGrpCat`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention node, not a missing
  declaration; `Scheme`, `QuasiCompact` and `QuasiSeparated` are its existing notions.

All recorded proof-dependency modules are imported without `public`:
`DerivedDirectImageComposition`, `Integral.BaseChange`, `DerivedExchangeTermwise`,
`ExactFunctorDerivedFunctor`, `ExchangeIdentityPasting`, `EtaleInverseImageExact`.
The direct-image and base-change definition modules are already public imports through
those listed above. Proof nodes without recorded modules do not generate invented
imports. The declaration docstring includes each of the five natural-language proof
steps, including the resolution comparison and canonical-arrow identification.

Edge cases checked: `q = 0` is included and gives the underived BC comparison;
zero sheaves and empty schemes are admitted without nonemptiness assumptions;
identity integral morphisms give the same inner and outer maps; integral morphisms
need not be surjective, and the final implication only uses functorial preservation
of inverses. No characteristic, noetherian, smoothness, torsion, or preceding-degree
BC assumption is used. All schemes share the usual site universe, with abelian
coefficient groups in universe `u + 1` as in the dependency records.

Searches actually run:

- `msearch.py leanfinder`, query "Integral pushforward identifies etale higher direct
  image base change arrows for pasted Cartesian squares": eight hits, including
  `Scheme.instHasPullbacksEtale` and etale stability; no integral cohomological arrow
  comparison.
- `msearch.py loogle`, query `CategoryTheory.Arrow, CategoryTheory.Iso`: twelve hits,
  including `Arrow.isoOfNatIso`, `Arrow.isoMk'`, and `Arrow.iso_w`. These provide
  general arrow infrastructure, not the node's statement.
- `msearch.py grep`, query `baseChangeHomologyMap|derivedBaseChangeMap|higherDirectImage`:
  zero Mathlib hits.
- `msearch.py leansearch`, query "Integral direct image of abelian etale sheaves
  naturally identifies the base change arrows of pasted Cartesian squares": service
  unavailable with Internal Server Error; no mathematical conclusion drawn.
- `rg` on upstream, Mathlib, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the declaration name and integral/base-change-arrow names found only the
  upstream `nonempty_arrowIso_baseChangeHomologyMap_comp` and its users. The required
  grep of the upstream tree by this node id gave no hits.
- Upstream `nonempty_arrowIso_baseChangeHomologyMap_comp` was read with its full
  signature and docstring. It gives pointwise arrow isomorphisms for module sheaves,
  not the natural endpoint isomorphisms for abelian sheaves stated here. Its following
  iff theorem is also pointwise and has a stronger conclusion. Neither is redefined.
  The present theorem uses the existing exchange directly and adds no new map notion.

Validation: `scompile.py NS lem-sbc-integral-pushforward-base-change-arrow` compiled the
module on the server in 2.9 seconds with nice 19, two threads, and a 60-second limit.
Its necessary unpublished side imports were compiled by the tool into its private
overlay. There were no errors or warnings. No local Lean or Lake command was run.
No statement correction or STATEMENT-DISPUTED issue was needed.

## Second reading by NS

Independent second reader, 2026-10-15. I opened the node, its sandbox module,
all seven statement-dependency records and their source declarations. I read
Stacks `etale-cohomology.tex`, lemma-base-change-q-integral-bottom (0F05),
including the surrounding hypotheses, lemma-what-integral (04C2), and
`sites-cohomology.tex`, remark-compose-base-change (0E46). I also read the
source theorem `nonempty_arrowIso_baseChangeHomologyMap_comp` and its proof.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Arbitrary schemes X', S', S'', X'', T, Y: the six `Scheme.{u}` binders.
   The maps `f'`, `π`, `π'`, `f''`, `g'`, `h'`, `e` have exactly the indicated
   domains and codomains. Verdict: match; no scheme finiteness hypotheses.
2. Integral π: `[IsIntegralHom π]`. I read the Mathlib class: it extends
   `IsAffineHom` and requires integral section maps on affine opens. The
   dependency records both this and `IsFinite`; the theorem correctly uses
   integrality alone. Verdict: match, not finite or integral-surjective.
3. X'' is the indicated fibre product with its projections:
   `sqπ : ChosenCartesianSquare π' f'' f' π`. I read the whole structure,
   including `isoPullback`, `hom_fst`, `hom_snd` and inherited commutativity,
   and the recorded `baseChangeInverseImageIso` declaration. Verdict: match.
4. Quasi-compact and quasi-separated g': `[QuasiCompact g']` and
   `[QuasiSeparated g']`, with no conditions substituted on f' or T.
   Verdict: match.
5. Y is the second fibre product with projections h', e:
   `sq : ChosenCartesianSquare h' e f'' g'`. Exchanging the two squares
   gives `sq.toCommSq.flip` and `sqπ.toCommSq.flip`; their `vert_comp` has
   arrows e, h' ≫ π', g' ≫ π, f'. These are the prescribed h and g, without
   requiring an additional independent square. Verdict: match.
6. Nonnegative q: `(q : ℕ)` and `(q : ℤ)` in each cohomology functor.
   Every integer degree q ≥ 0 is represented. Verdict: match.
7. Arbitrary abelian etale F on T: the functors in the first conjunct have
   source `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`; the second
   conjunct explicitly quantifies over every such F. I checked Mathlib's
   site definition and sheaf condition. Verdict: match; no torsion or
   coefficient-module restriction.
8. The two natural endpoint isomorphisms: let b and B denote, only for this
   explanation, the single-in-degree-zero / degree-q-homology whiskerings
   of `derivedBaseChangeMapPlus` for the inner and pasted squares.
   The first conjunct is `Nonempty (Arrow.mk (Functor.whiskerRight b
   (lowerStar AddCommGrpCat π')) ≅ Arrow.mk B)` in the arrow category of
   the functor category. Its left endpoint is π'_* H^q(f''⁻¹ Rg'_* F[0])
   versus H^q(f'⁻¹ Rg_* F[0]); its right endpoint is
   π'_* H^q(Rh'_* e⁻¹ F[0]) versus H^q(Rh_* e⁻¹ F[0]). Exactness of inverse
   image identifies these with precisely the two displayed sheaves in the
   node. An isomorphism of arrows gives invertible natural transformations
   at both endpoints. Verdict: both clauses included, naturally in F.
9. Equality of the actual arrows under those isomorphisms: by the defining
   commuting-square condition `Arrow.w`, if C and D are the left and right
   components of that isomorphism, then `C ≫ B = π'_*(b) ≫ D`.
   Thus `B = C⁻¹ ≫ π'_*(b) ≫ D`. This is exactly the requested compatibility;
   merely having isomorphic endpoints would not have sufficed. Verdict: match.
10. If the inner BC map is invertible then the pasted BC map is invertible:
    the explicit `∀ F, IsIso (...) → IsIso (...)` is in the required direction.
    Both maps are the degree-q homology of the same recorded exchanges at
    `singleFunctor.obj F`. Verdict: match; no converse asserted.

For checklist items 8–10 I read `lowerStar`, `upperStar`, their adjunction,
`rightDerivedLowerStarPlus`, and the definition and resolution formula of
`derivedBaseChangeMapPlus`. I also read `derivedBaseChangeMap` and
`baseChange_eq_derivedBaseChangeMapPlus`: the former is the unbounded mate,
whereas the latter identifies the existing bounded-below mate with the exchange
used here. The base-change dependency explicitly permits its bounded-below
presentation for the abelian degreewise clause. The theorem therefore uses the
existing map, rather than a private or newly postulated BC construction. Its
outer square has precisely g = g' ≫ π and h = h' ≫ π'.

The source lemma's surrounding torsion and lower-degree-BC hypotheses concern
its broader reflection argument. In its displayed pushforward identifications,
exactness of integral pushforward and integral exchange suffice. The upstream
arrow theorem confirms that these hypotheses are not needed for the extracted
arrow comparison, even in degree zero. This item keeps the node's qcqs
hypotheses on g'; it does not silently change the node to the more general
upstream theorem.

Edge cases: q = 0 is included and recovers underived BC. Zero sheaves and empty
schemes are admitted; there is no `Nonempty` assumption on a scheme or on F.
The `Nonempty` in the conclusion asserts existence of an isomorphism, not a
geometric nonemptiness assumption. Identity integral maps are included; π may
also be non-surjective. There is no characteristic, n, Noetherian, smoothness,
or field hypothesis. No index set occurs. Universe u is arbitrary; the common
scheme universe and group universe u+1 follow the recorded site conventions,
and do not impose a cardinal bound independent of the schemes. Every variable
and universe in the signature is bound.

Independent duplicate searches (new query wording):

- LeanFinder: "Exact direct image functor along an integral morphism identifies
  cohomology base change natural transformations of composite squares".
  Eight hits, including `Scheme.Modules.pushforwardComp`,
  `SheafOfModules.pullbackComp`, and a Mayer–Vietoris exactness result; none
  states this natural abelian etale arrow comparison.
- Loogle: `CategoryTheory.Arrow, "iso"`. Twelve hits include `Arrow.isoMk`,
  `Arrow.isoMk'`, `Arrow.iso_w`, `Arrow.isIso_left`, and `Arrow.isIso_right`.
  These confirm the arrow encoding but are not the geometric theorem.
- Mathlib grep service: `integralPushforward|arrowIso_baseChange|baseChange.*paste`:
  zero hits.
- Direct `rg` over Mathlib, upstream WeilConjectures, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for integral/arrow names and
  `arrowIso_baseChange` found the upstream module theorem and its users,
  but no matching natural-transformation theorem. I read the full upstream
  `nonempty_arrowIso_baseChangeHomologyMap_comp` signature: it is pointwise
  in F and uses `ModuleCat Λ`; it does not supply this functor-category
  isomorphism for abelian sheaves. Its following iff theorem likewise does
  not state this item. No existing identical declaration replaces the module.

There are no new nodes or sibling dependency modules in this delivery. The
existing chosen-square and inverse-image-comparison modules are real definitions
with projection-compatible pullback data, not hollow constructions. The item
introduces no definitions, instances or axioms. Its sole theorem remains `sorry`.
The module and declaration docstrings name the source and blueprint id, and the
five proof-plan steps cover integral exactness, termwise exchange and resolution
comparison, composition/pasting, cohomology, and compatibility/preservation of
inverses. All recorded proof modules are imported; proof-only imports are not
public. No line exceeds 100 characters and no local notation or private notion
is introduced. I checked that `lean.statement` equals the file's signature
verbatim, and that the node differs from the repository copy only in `lean`.

Mismatches found: none. Changes: appended this independent second reading;
the Lean and mathematical node statement are preserved. No statement correction
or disputed-statement flag is needed.

Validation after this reading: `scompile.py NS
lem-sbc-integral-pushforward-base-change-arrow` compiled the delivered module
on the server in 3.0 seconds, with nice 19, two threads and the 60-second
per-file limit. The tool compiled its side-only imports in the private overlay.
There were no errors or warnings. No local compiler or Lake build was run.
