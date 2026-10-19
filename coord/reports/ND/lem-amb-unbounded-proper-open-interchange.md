## Worker report

The module `Sheaf.Paper.UnboundedProperOpenInterchange` states
`AlgebraicGeometry.Etale.unboundedProperOpenInterchange`, with one postponed proof and no
new definitions, axioms or altered mathematical statements. The two existential families
`θ` and `Γ` are natural isomorphisms whose maps are fixed by the first two conjuncts.
They are not arbitrary identifications. The theorem states all of the node at once, so
the pasting and base-change equations concern the very same normalized `Γ`.

Sources read: Stacks [0F7B](https://stacks.math.columbia.edu/tag/0F7B), case (b),
[0F7C](https://stacks.math.columbia.edu/tag/0F7C),
[0F7D](https://stacks.math.columbia.edu/tag/0F7D), and
[0F7F](https://stacks.math.columbia.edu/tag/0F7F). These were read online because the
literature checkout on this machine contains the citation index but not `more-etale.tex`.
The module/declaration docstrings cite the node and these sources. The theorem docstring
carries the complete nine-step proof from the node, including each step's dependency ids.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`; no nonzero-ring or invertibility hypothesis |
| All schemes Noetherian in the finite-affine-cover sense | `[IsNoetherian U]`, etc., on every scheme quantified in each clause; Mathlib's `IsNoetherian` is locally Noetherian plus compact, with `isNoetherian_iff_of_finite_iSup_eq_top` giving the finite affine-cover characterization |
| Ordinary constant-A module sheaves on the small etale site | `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)`; the recorded six-functor encoding, not condensed coefficients |
| Unbounded derived categories | `DerivedCategoryModule A U`, i.e. the ordinary `DerivedCategory` of that sheaf category; no `Plus`, `Bounded`, constructible, finite-Tor or cohomological-bound predicate |
| Four edges and commutativity pk = ir | `(k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)` and `sq : CommSq k r p i`; `sq.w` is `k ≫ p = r ≫ i` |
| Proper vertical edges | `[IsProper r] [IsProper p]` |
| Open horizontal edges | `[IsOpenImmersion k] [IsOpenImmersion i]` |
| No cartesian assumption for the principal assertion | Both families `θ`, `Γ` and their representative laws take `CommSq`; only the third conjunct takes `IsPullback` |
| Degreewise derived extension by zero | `D((i)_!open[ModuleCat.{u + 1} A])` uses the recorded exact `openImmersionLowerShriek` and `Functor.mapDerivedCategory` |
| Total K-injective right derived direct image | `R((r)_*[ModuleCat.{u + 1} A])` is `Functor.rightDerivedFunctor`; `rightDerivedFunctorObjQIso` supplies its normalized computation on K-injectives |
| Canonical natural isomorphism Γ | Family `Γ` has type `R(r_*) ⋙ D(i_!) ≅ D(k_!) ⋙ R(p_*)` |
| Canonical sheaf support identification | Family `θ` has type `r_* ⋙ i_! ≅ k_! ⋙ p_*`; conjunct 1 equates its composites with `p_*(k_! → k_*)` and `i_! → i_*`, followed by `lowerStarComp`, into the same `(k ≫ p)_*F`. These are the inclusions of the support subsheaves, so this states equality as subsheaves and fixes the underlying sections, exactly as the proper-support-composition dependency specifies |
| Formula on every K-injective J and resolution k_!J → I | Conjunct 2 quantifies `J`, `[J.IsKInjective]`, `I`, `[I.IsKInjective]`, `ρ`, `[QuasiIso ρ]`. The latter two conditions are exactly the recorded `IsKInjectiveResolution` predicate. The left side is the termwise `θ` followed by `Q(p_*ρ)`, with `rightDerivedFunctorObjQIso` and `mapDerivedCategoryFactors` inserted. The right side is `Γ` followed by the canonical resolution identification of its target. This gives precisely the specified representative; naturality transports it from `QJ` to any isomorphic input K |
| Cartesian λ = exchange followed by inverse open unit | Conjunct 3 supplies `lam` as a natural isomorphism. Its hom at every K is explicitly `exactDerivedBaseChangeMap ... sq.toCommSq` at `D(k_!)K`, followed by `R(r_*).map (inv (adj_k.unit.app K))` |
| Γ is the adjunct of λ inverse | The second part of conjunct 3 states `Γ_K = D(i_!).map (lam.inv.app K) ≫ adj_i.counit.app (...)`, with the recorded termwise-derived open adjunction |
| Vertical stacking | Conjunct 4 uses `sq₁.vert_comp sq₂` and the equation `Γ_outer = D(i₂_!)(κ_r⁻¹) ≫ Γ₂ ≫ R(p₂_*)(Γ₁) ≫ κ_p`, with `rightDerivedLowerStarComp` as both canonical pushforward compositors |
| Horizontal stacking | Conjunct 5 uses `sq₁.horiz_comp sq₂`. It first expands `D((i ≫ j)_!)`, then applies `D(j_!)(Γ₁)` and `Γ₂` at `D(k_!)K`, and finally contracts `D(k_!)D(l_!)`. The open compositors are `mapDerivedCategoryNatIso (openImmersionLowerShriekComp ...) ≪≫ mapDerivedCategoryCompIso`, so they use the recorded canonical sheaf compositor, not a new composition map |
| Both proper edges identities | Conjunct 6 states the identity comparison after the canonical `R(id_*) ≅ id` identifications from `rightDerivedFunctorIsoMapDerivedCategory`, `lowerStarId`, and `mapDerivedCategoryIdIso` |
| Both open edges identities | Conjunct 7 states the identity comparison after `D(id_!) ≅ id`, derived from the canonical `Adjunction.leftAdjointIdIso` for the sheaf open adjunction and `upperStarId`. In both identity cases commutativity forces the remaining edges equal, so writing the same edge on both sides includes all cases |
| Any Noetherian base Z₁ → Z and its fibre-product square | Conjunct 8 quantifies an arbitrary cube: both horizontal commutative squares, all projections `a,b,c,d`, and `sp,sr,si,sk : IsPullback` for its four side faces. This expresses any fibre-product base change, including the chosen pullbacks, without requiring the original Q to be cartesian. All new schemes satisfy the stated Noetherian convention; in the chosen base change this follows from properness and open immersion over Noetherian Z₁ |
| e_i and e_k are inverse extension-by-zero base-change maps | Conjunct 8 uses `.inv` of `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` for `si` and `sk`. This construction descends the recorded `openImmersionLowerShriekBaseChangeMap` degreewise and has exactly the source's inverse orientation. It is the open specialization identified in `lem-cbc-extension-zero-base-change`, hence the open specialization of the recorded etale-shriek map |
| Base-change equation | Conjunct 8 is the two three-factor composites in the node, in Lean's left-to-right `≫` convention: `b^*(Γ) ≫ Ex_p ≫ R(p₁_*)(e_k) = e_i ≫ D(i₁_!)(Ex_r) ≫ Γ₁`, at every K. It uses the exact unbounded adjunction-mate exchanges on both proper faces |
| No constructibility, invertibility or dimension restrictions; every unbounded input | All inputs are arbitrary `DerivedCategoryModule`; no such extra binder or condition occurs anywhere |

Dependency declarations read and used (modules below are the node's recorded modules;
existing Mathlib leaves use their `mathlib_match`). The source/docstrings of the recorded
interfaces were inspected. The current server source of
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` was also checked with
`scompile.py --source`; its canonical comparison has the same resolution normalization
as the standard constant-coefficient `Etale.rightDerivedLowerStarComp` used here.

| Dependency | Module and declarations |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` |
| `def-weil-pbc-noetherian-ring` | `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, `isNoetherianRing_iff` |
| `def-weil-pbc-derived-categories` | `Sheaf.AlgebraicGeometry.DerivedCategories`: `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`, `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.Bounded`, `DerivedCategory.homologyFunctor`, `CategoryTheory.Sheaf.IsTorsion` |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed` |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion` |
| `def-weil-pbc-extension-by-zero` | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: `AlgebraicGeometry.Etale.openImmersionLowerShriek`, `AlgebraicGeometry.Etale.openImmersionLowerShriekCompUliftSheafFiberIso`, `AlgebraicGeometry.Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj` |
| `lem-weil-pbc-extension-by-zero-exact` | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` |
| `def-weil-pbc-kinjective-resolutions` | `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: `CochainComplex.IsKInjectiveResolution`, `CochainComplex.IsKInjective`, `QuasiIso` |
| `lem-weil-pbc-kinjective-total-derived` | `Sheaf.CategoryTheory.KInjectiveTotalDerived`: `CategoryTheory.exists_rightDerived_of_enough_isKInjective` |
| `lem-cbc-proper-support-sheaf-composition` | `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`: `AlgebraicGeometry.Etale.properSupportSheafComposition` |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`, `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd` |
| `def-kun-unbounded-exchange` | `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`, `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso` |
| `lem-weil-pbc-extension-by-zero-adjunction` | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`, `AlgebraicGeometry.Etale.openImmersionLowerShriekAdjunction` |
| `lem-weil-pbc-termwise-adjunction-homotopy` | `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`: `CategoryTheory.Adjunction.mapHomotopyCategory` |
| `lem-weil-pbc-localization-universal-property` | Mathlib: `CategoryTheory.Localization.lift` (`Mathlib/CategoryTheory/Localization/Predicate.lean`) |
| `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` | `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: `CategoryTheory.ringedToposDerivedPushforwardComposition` |
| `lem-cbc-extension-zero-composition` | `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`: `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence`, `AlgebraicGeometry.Etale.openImmersionLowerShriekComp` |
| `def-weil-pbc-etale-shriek-base-change-map` | `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`: `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap` |
| `lem-cbc-extension-zero-base-change` | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`: `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`, `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`, `AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app` |

The theorem also imports every already recorded proof-dependency module; proof-only
imports are plain `import`. Additional standard interfaces are
`Functor.rightDerivedFunctorObjQIso`, `Functor.mapDerivedCategoryFactors`,
`Etale.rightDerivedLowerStarComp`, the exact derived open adjunction and its invertible
unit, `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`, and the functoriality
and identity isomorphisms of `Functor.mapDerivedCategory`.

Edge cases checked before writing: the zero ring is allowed (`CommRing` plus `Finite`
does not imply `Nontrivial`); zero complexes and unbounded complexes are allowed; empty
schemes and empty open immersions are allowed. Identity proper/open edges are stated
explicitly, with the canonical unit maps rather than unrelated isomorphisms. Noncartesian
squares occur in the principal assertion and in the base-change law. An identity base
map and an arbitrary pullback model are both covered by the cube clause. No assumption
on the characteristic or on fibre dimensions is included. All universes and variables
are explicit; the coefficient universe is exactly the recorded ordinary-etale size
convention. No file-local notation, instance, abbreviation, private declaration or
arbitrary replacement functor is introduced.

Searches for an existing statement (2026-10-16):

- `msearch.py ... leanfinder` query: "Unbounded derived proper direct image commutes with
  extension by zero for a commutative square of proper maps and open immersions,
  compatibly with composition and base change". Eight hits: ordinary scheme-module
  pushforward/restriction composition and general sheaf-pushforward results; none state
  this theorem.
- `msearch.py ... loogle` query: `openImmersionLowerShriekLowerStarExchange,
  rightDerivedLowerStarComp`. No hits; the former is not a Mathlib identifier.
- `msearch.py ... grep` query: `proper.*open|open.*proper|interchange`, directory
  `AlgebraicGeometry`. Twenty-five hits; no matching interchange theorem.
- `msearch.py ... leansearch` query: "proper pushforward extension by zero unbounded
  derived categories commutative square". Service unavailable, Internal Server Error;
  no mathematical verdict inferred from that unavailable search.
- `rg` on Mathlib and on `WeilConjectures/` for proper/open/interchange and derived
  open-shriek names, and on the project `lean/Sheaf`: found the upstream
  `Etale.openImmersionLowerShriekLowerStarExchange` and its torsion-ring invertibility
  theorem. Read their full source: both require a cartesian square and neither gives
  this noncartesian support-normalized family and its full coherence package. They
  therefore do not state this node.
- `rg` on the upstream declaration index, source and project library for
  `unboundedProperOpenInterchange` and the exact node id: no existing declaration.
  The proper-support, exact-exchange, open-composition and open-base-change notions
  already exist and are reused, so no extra notion node is required.

No statement correction, dependency replacement, new node or disputed statement.
Validation: the final file is compiled with `scompile.py` under the prescribed file-only
60-second limit, then `deliver2.py ... --no-push` checks the exact node record, imports,
docstrings and delivered module. The worker does not deliver or write a second reading.

## Second reading by ND

I independently opened the sandbox node and all 415 lines of its Lean module, the
statement-dependency node records, and the signatures and constructions cited below.
No statement correction or `statement_change` is present. There are no new nodes or
additional dependency modules in this delivery, so H12/H13 do not require an additional
node audit. I found no mismatch to repair and left the Lean and node record unchanged.
Only this second-reading report was added.

Source check: the local literature directory has no Stacks checkout. I read the actual
`more-etale.tex` from the Stacks source repository, saving a reference copy only in the
sandbox scratchpad, as well as the displayed tags:
[0F7B](https://stacks.math.columbia.edu/tag/0F7B),
[0F7C](https://stacks.math.columbia.edu/tag/0F7C),
[0F7D](https://stacks.math.columbia.edu/tag/0F7D), and
[0F7F](https://stacks.math.columbia.edu/tag/0F7F).
The beginning of section `section-prelim` imposes no additional standing hypotheses.
The source allows separated locally quasi-finite horizontal maps and torsion rings;
this node explicitly asks for its open-immersion, finite-commutative-ring specialization
on Noetherian schemes. The Lean retains exactly that specialization. In particular,
0F7B assumes commutativity, not cartesianness. Its representative and subsheaf
identification are the ones specified in this node. The vertical and horizontal
pasting orders and the two paths of the base-change diagram agree with the source.
The cartesian adjunct formula is the normalization explicitly included in the node.

My object/hypothesis/conclusion inventory, made before comparing the clauses, is below.
Here conjunct numbers refer to the eight conjuncts after the existential `θ` and `Γ`.

| Node item | Actual Lean rendering and second-reader verdict |
| --- | --- |
| A finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`. PASS: no field, nonzero-ring, invertibility, or characteristic assumption. |
| All schemes Noetherian in the finite affine-cover sense | `Scheme.{u}` with `[IsNoetherian ...]` on each of the four, six, or eight schemes in the corresponding clause. PASS: Mathlib's class extends `IsLocallyNoetherian` and `CompactSpace`, and its `isNoetherian_iff_of_finite_iSup_eq_top` and `isNoetherian_iff_of_finite_affine_openCover` give the node's meaning. |
| Ordinary small-etale constant-A module sheaves | `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)`, and the same expression on every other scheme. PASS: these are the recorded six-functor sheaf categories; no condensed or scheme-structure-sheaf coefficients. |
| The entire unbounded derived category | `DerivedCategoryModule A U` and `DerivedCategory.Q`, with complexes indexed by `ℤ`. PASS: I opened `DerivedCategories.lean` and upstream `Derived/Coefficients.lean`: this abbreviation is exactly `DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))`. |
| Edges k, r, p, i with pk = ir | Four typed arrows and `(sq : CommSq k r p i)`. PASS: `sq.w` identifies `k ≫ p` with `r ≫ i`; no cartesian hypothesis in the principal families or representative clause. |
| Proper r and p; open k and i | `[IsProper r] [IsProper p] [IsOpenImmersion k] [IsOpenImmersion i]`. PASS: precisely the recorded Mathlib properties, with no extra finite-dimensional or finite-Tor assumption. |
| Degreewise open extension and K-injective total derived direct image | `D((i)_!open[ModuleCat.{u + 1} A])` and `R((r)_*[ModuleCat.{u + 1} A])`. PASS: upstream open shriek is the recorded localization extension by zero; its exactness induces `mapDerivedCategory`. `R` is total `rightDerivedFunctor`, with its K-injective computation iso. |
| One canonical natural isomorphism for each Q | The single existential family `Γ` has source `R(r_*) ⋙ D(i_!)` and target `D(k_!) ⋙ R(p_*)`. PASS: subsequent clauses all use this same family, so coherence is not stated for unrelated witnesses. Functor composition `⋙` reads in the opposite textual order to the node's functional composition. |
| Canonical sheaf support identification | The family `θ` is a natural iso `r_* ⋙ i_! ≅ k_! ⋙ p_*`. Conjunct 1 fixes its hom by composing both sides with `openImmersionLowerShriekToLowerStar` and `lowerStarComp` into `(k ≫ p)_*F`. PASS: this is the identity on the common subsheaf, not an arbitrary iso; the two direct-image identifications have the right commutativity transport. |
| Formula for every K-injective representative and every resolution | Conjunct 2 quantifies every `J` with `[J.IsKInjective]`, every `I` with `[I.IsKInjective]`, every `ρ : k_!J ⟶ I` with `[QuasiIso ρ]`. PASS: these last two conditions are exactly the two factors of the recorded `CochainComplex.IsKInjectiveResolution`; no degreewise injectivity is added. The left side is `Q(θ_J)` then `Q(p_*ρ)`, with the source identifications. The right side is `Γ_(QJ)` followed by the target resolution identifications. |
| Arbitrary derived input K represented by J | The formula is at `DerivedCategory.Q.obj J`, while `Γ` is a natural isomorphism on the whole derived category. PASS: the upstream `DerivedCategory.exists_iso_Q_obj_of_isKInjective` applies to these Grothendieck sheaf categories, so naturality transports the formula to any K and any representative identification. |
| Cartesian lambda and the inverse open unit | Conjunct 3 alone uses `(sq : IsPullback k r p i)`; `lam.hom.app K` is `exactDerivedBaseChangeMap ... sq.toCommSq` at `D(k_!)K` followed by `R(r_*).map (inv (adj_k.unit.app K))`. PASS: both orientation and normalization agree, and the existential `lam` is an iso of the indicated functors. |
| Gamma is the adjunct of lambda inverse | Conjunct 3 continues with `Γ_K = D(i_!).map (lam.inv.app K) ≫ adj_i.counit.app ...`. PASS: this is exactly the adjunct under `Di_! ⊣ i^*`, rather than its inverse or the other adjunction. |
| Vertical pasting | Conjunct 4 quantifies all six schemes and two commutative squares, and uses `sq₁.vert_comp sq₂`. PASS: it expands the left composite proper direct image by `rightDerivedLowerStarComp.inv`, applies `Γ₂` at `Rr₁K`, applies `Rp₂` to `Γ₁`, and contracts by the right compositor hom. This is the node's vertical order. |
| Horizontal pasting | Conjunct 5 uses `sq₁.horiz_comp sq₂`, expands the bottom composite open extension by the derived canonical `openImmersionLowerShriekComp`, then applies `Dj_!(Γ₁)` and `Γ₂_(Dk_!K)`, and contracts the top composite by the inverse compositor. PASS: this is the node's horizontal order and reuses the recorded comparison. |
| Identity proper edges | Conjunct 6 evaluates `Γ k (𝟙 U) (𝟙 V) k` and equates it with the canonical `R(id_*) ≅ id` comparisons obtained from `rightDerivedFunctorIsoMapDerivedCategory`, `lowerStarId`, and `mapDerivedCategoryIdIso`. PASS: this is the identity after the prescribed identifications. |
| Identity open edges | Conjunct 7 evaluates `Γ (𝟙 U) r r (𝟙 W)` and uses `Adjunction.leftAdjointIdIso` of the actual open adjunction, then descends it by `mapDerivedCategoryNatIso`. PASS: this is the identity with the canonical open identity comparisons. Commutativity forces the other two edges equal in each identity case, so no identity square is lost. |
| Any Noetherian base change b, projections a,c,d, and base-changed square Q1 | Conjunct 8 binds both squares, all four projections, and `sp`, `sr`, `si`, `sk` as `IsPullback` on the four side faces. PASS: this is a coherent commutative cube, and pasting `sk` with `sp` identifies U1 as the base change of U over Z. It covers arbitrary models of the fibre products and does not require the original Q cartesian. |
| The new edges' proper/open and Noetherian properties | Explicit instances on all the new edges and schemes. PASS: these are consequences of the pullback data, original proper/open hypotheses, and Noetherian Z1 (finite type over a Noetherian scheme and open subschemes remain Noetherian). They add no mathematical restriction to the requested base changes. |
| ei and ek are inverses of the specified degreewise comparison | Conjunct 8 uses `.inv` of `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso` at `si` and `sk`. PASS: I opened its construction; it is exactly the termwise descended `openImmersionLowerShriekBaseChangeMap`, bracketed by the functor-composition comparison isos. The inverse has the node's orientation. |
| Base-change equation using unbounded mate exchanges | Conjunct 8 starts with `D(b^*).map Γ`, then `exactDerivedBaseChangeMap sp`, then `Rp₁.map ek`; the other side is `ei`, then `Di₁_!.map (exactDerivedBaseChangeMap sr)`, then `Γ₁` at `D(d^*)K`. PASS: the two composites have the same source and target and match every factor of the node. |
| Every unbounded input, without constructibility, invertibility, or dimension bounds | Each object binder is an unrestricted `DerivedCategoryModule`, with no boundedness/constructibility predicate or auxiliary numerical assumption. PASS. |

I checked the dependency interfaces rather than relying on the worker's declaration
names. Besides the modules listed in the worker report, I opened the actual upstream
`OpenImmersionLowerShriek.lean`, `OpenImmersionLowerShriekBaseChange.lean`,
`LowerShriek/OpenImmersion/Defs.lean`, `BaseChangeSquare.lean`,
`RightDerivedFunctor/KInjective.lean`, `HomotopyCategory/Adjunction.lean`, and
`Derived/UpperLowerStar.lean`. I read the recorded `KInjectiveTotalDerived`,
`KInjectiveResolutions`, `ProperSupportSheafComposition`, `ExactUnboundedExchange`,
`EtaleLowerShriekBaseChangeMap`, and `OpenImmersionLowerShriekCoherence` signatures.
I also fetched the current source of `RingedToposDerivedPushforwardComposition` via
`scompile.py --source`, because its local record is lengthy and its normalization matters.
The generic ringed-site theorem is not confused with the ordinary constant-coefficient
functors: the equation uses the existing specialized `rightDerivedLowerStarComp` on
these same etale categories. I read its definition as the conjugate of the canonical
inverse-image compositor. The relevant derived adjunction's extra monoidal and flat
resolution instances are all supplied for `ModuleCat A`; none become assumptions of this
statement. The exact-exchange definition explicitly permits the required coefficient
and site universes.

For the specific shriek base-change map, I compared the existing conjugate construction
with `etaleLowerShriekBaseChangeMap` and read
`unit_map_openImmersionLowerShriekBaseChangeMap_app` and
`openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app`.
They fix the unit/square transpose and its compatibility with the ambient direct-image
comparison. Thus the open specialization used here is the stated degreewise map, not
an unspecified base-change iso. The sheaf `θ` normalization similarly uses the actual
recorded inclusion and canonical direct-image compositor. There is no missing canonical
map or notion requiring a new definition node or dependency repair.

Edge cases: PASS for the zero ring (no `Nontrivial A`), zero and completely unbounded
complexes, the empty scheme, and an empty open immersion. Degrees run over all integers,
including zero. There is no index set whose emptiness needs an additional binder.
Both kinds of identity square have their own explicit laws. The cube accepts identity
base maps and any isomorphic fibre-product models. No characteristic or coefficient-order
invertibility restriction occurs. The universe `u` is explicit and arbitrary; the
`Type (u + 1)` coefficient convention and `ModuleCat.{u + 1}` are the recorded ordinary
small-etale convention, with no equality forced between different site universes and no
extra implicit variable. Finite coefficients admit representatives at this convention.

Independent H4 searches (2026-10-16), using wording different from the worker's:

- `msearch.py ND lem-amb-unbounded-proper-open-interchange leanfinder`:
  "Derived pushforward of an extension by zero commutes with a proper morphism in a
  non-pullback square, with compatibility for rectangles". Eight hits, all ordinary
  sheaf-pushforward composition or natural-transformation lemmas; none is this statement.
- `msearch.py ... loogle 'rightDerivedLowerStarComp'`: zero hits; the Mathlib search
  service does not know this project/upstream identifier. I found and opened it by `rg`.
- `msearch.py ... grep 'shriek.*[Cc]omm|[Cc]omm.*shriek|[Pp]roper.*[Ee]xchange'`:
  zero hits.
- `msearch.py ... leansearch` with "Unbounded direct image of a sheaf extended by zero
  across an open immersion and a proper map": service unavailable (Internal Server
  Error), recorded as unavailable and not treated as evidence of absence.
- Direct `rg` on Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the
  repository's `lean/Sheaf` for `proper.*shriek`, `shriek.*proper`,
  `proper.*interchange`, and `interchange.*proper`, then the exact theorem name and
  `openImmersionLowerShriekLowerStarExchange`. I opened the full upstream exchange
  module and its invertibility theorem. They require `IsPullback`; this node also
  includes noncartesian squares, a support/representative normalization, both pasting
  laws, identity laws, and arbitrary base-change compatibility for the same family.
  They are related usable ingredients, not an existing declaration of this node.
  No duplicate of this statement or private definition was found.

H5/H6/H8/H9: the delivered file has one theorem with proof `by sorry`, no data definition,
no axiom, no extra proved declaration, no private/file-local notation or instance.
The module and theorem docstrings identify the exact Stacks places and blueprint id;
the theorem docstring contains all nine proof steps and their dependency ids. Every
Lean line has at most 100 characters. Imports include the recorded statement interfaces
and the already-stated proof dependencies. The `by simp` terms in the two identity
square arguments only furnish the canonical commutativity proofs, not new lemmas.
The node's `lean.statement` is byte-for-byte the theorem signature before `:= by`.

Validation performed by this second reader: the prescribed `scompile.py ND
lem-amb-unbounded-proper-open-interchange` compiled the only delivered file,
`lean/Sheaf/Paper/UnboundedProperOpenInterchange.lean`, cleanly (33.8 seconds for the
library file; no errors or warnings). No source or signature change was necessary.
The final delivery dry run and delivery are recorded by the prescribed wrapper.
