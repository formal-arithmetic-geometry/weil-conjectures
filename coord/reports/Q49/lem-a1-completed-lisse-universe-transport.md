## Worker report

The delivery states `WeilConjectures.CompletedLisseTransport.exists_completed_lisse_universe_transport`
in `Sheaf.Paper.CompletedLisseUniverseTransport`. Its proof is `sorry`. The supporting
records spell out what a normalized comparison means; they do not assert its existence.
The two proof obligations needed by the generalized completion construction are named
`WeilConjectures.CompletedSite.quotient_compatible` and
`WeilConjectures.CompletedSite.uniformizer_natural`, each with `sorry` and its proof plan.
There is no other postponed theorem and no definition with missing data.

The original node statement is unchanged. No mathematical correction or dispute is needed.
The source was read in Bhatt--Scholze pp. 58--60: Lemma 6.8.2 identifies the completed
coefficient sheaf and localization; Definition 6.8.3 defines lisse by local finite freeness.
The finite-basis and universe arguments are explicitly agent-written, as in the node.
The current blueprint `latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-hc2/lem-a1-affine-hc0.proof.md`
was also read: its first paragraph uses the integral-model input from `p-real-integral`.
This item is not the statement of that blueprint unit.

Hypotheses and objects are rendered as follows.

| Node | Lean |
| --- | --- |
| Scheme X | `X : AlgebraicGeometry.Scheme.{t}` |
| Small representative C of the small pro-etale site | `C : Type c`, `[SmallCategory C]`, `site : C ≌ X.ProEt` |
| Transported covering families | `site.functor.inducedTopology (Scheme.ProEt.topology X)`; equivalences of sites transport this topology |
| Prime l | `l : ℕ`, `[Fact l.Prime]` |
| Finite extension E/Q_l | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| E has its l-adic topology | `coefficientTopology l E`, the actual topology of `spectralNorm.normedField ℚ_[l] E` |
| A and the chosen uniformizer | `Padic.coefficientExtensionIntegers l E`, `Padic.coefficientExtensionUniformizer l E` |
| Independent site, coefficient and enlargement sizes | Independent `t`, `c`, `u`, `w`; no equality between them |
| W0 contains the small site and covers and the small field model | The category and arrows are c-small, the field model is in `Type 0`, and the source coefficients and modules are c-small |
| W enlarges W0 | The model-only comparison has target universe `max c w`; comparison with raw E uses `max u c w` |
| A second small site representative | For every `D : Type c`, `[SmallCategory D]`, `f : D ≌ C`, the topology is induced by `(f.trans site).functor` |

In particular, the second conjunct in the final universal quantifier compares the small
model with itself in `max c w`, with no occurrence of `u` in the target module universe.
Thus a large original carrier for E does not impose a lower bound on the module universe.
The first conjunct compares with the raw E presentation in a common universe containing E.
Together these are the node's independent-coefficient and containing-universe convention.
The identity representative is included by taking D=C and f the reflexive equivalence.
No finite-field, characteristic, normality, nonempty-site or nonzero-rank hypotheses occur.

The conclusion is rendered clause by clause as follows.

| Node clause | Lean |
| --- | --- |
| E0 in the universe of Q_l, with a field and algebra isomorphism | `∃ (E₀ : Type) (_ : Field E₀) (_ : Algebra ℚ_[l] E₀) (e : E₀ ≃ₐ[ℚ_[l]] E)` |
| E0 is finite dimensional | `FiniteDimensional ℚ_[l] E₀` in the conclusion |
| Transported topology and topological algebra isomorphism | `IsHomeomorph e` with domain topology exactly `TopologicalSpace.induced e (coefficientTopology l E)`; algebra compatibility is part of `AlgEquiv` |
| A0 = e^{-1}(A) | `(Padic.coefficientExtensionIntegers l E).comap e.toRingEquiv.toRingHom` |
| e restricts to A0 ≃ A | `integersEquiv l E e`, constructed by `RingEquiv.restrict` |
| p0 = e^{-1}(p) | `(integersEquiv l E e).symm (Padic.coefficientExtensionUniformizer l E)` |
| All power ideals are carried to the original power ideals | The `∀ n : ℕ, Ideal.map ... = Padic.coefficientExtensionIdeal l E n` conjunct, also valid at n=0 |
| Constant finite quotient rings | `CompletedSite.residue A p n = A ⧸ (Ideal.span {p})^(n+1)` and `CompletedSite.constant` |
| Completed sheaves are the inverse limits of the actual finite constant tower | `CompletedSite.tower`, `CompletedSite.ring`, and `limit.π` |
| Constant uniformizer sections | `CompletedSite.uniformizer`, obtained from the actual constant sheafification unit and `CompletedSite.constantMap` |
| Constant coefficient isomorphism | `Coefficients.constant`, normalized by `constant_section` on every constant element |
| Residue isomorphisms | `Coefficients.residue`, normalized by `residue_section` on every quotient representative |
| Completed coefficient isomorphism | `Coefficients.completed` |
| Commutes with constant-to-completion | `Coefficients.constants` |
| Commutes with all projections and transitions | `Coefficients.projections`, `Coefficients.transitions` |
| Carries the uniformizer section | `Coefficients.uniformizer` |
| Localized coefficient isomorphism | `Coefficients.localized`, between the recorded `ringedLocalizationRingOfUniverses` constructions |
| Commutes with localization units | `Coefficients.localization_unit` |
| Integral and rational Loc categories | `Loc R`, the full subcategory for the existing `SheafOfModules.isFiniteLocallyFree` |
| Equivalences of these categories | `Transport.categories.base.integral.equivalence` and `.rational.equivalence` |
| The equivalences are induced by coefficient transport | `LisseComparison.app`, `.naturality`, `.smul`, `.map` specify semilinear section bijections commuting with restrictions and every morphism |
| Every large object and morphism descends | These are category equivalences, including quasi-inverse and unit/counit, rather than objectwise smallness assertions |
| Rationalization stays locally finite free | `RationalComparison.source_finite` and `.target_finite` |
| Commutes naturally with rationalization | `RationalComparison.tensor`, `.tensor_naturality`, `.tensor_section` for the actual `changeOfRingsOfUniverses` and its actual maps |
| Slice equivalences and rationalization | `SlicedRationalComparison.slices` uses the actual `R.over U` and `(J.overPullback ... U).map j`; each slice has the same normalized tensor comparison |
| Commutes with restriction | `SliceCompatibility.restriction` and `.restriction_section`; integral/rational restriction fields identify the slice equivalences with those in `.slices` |
| Abstract integral models transport in both directions | `RationalComparison.models`, together with the equivalences and tensor isomorphisms, transports each pair `(M, θ)` and its morphisms |
| No integral embedding hypothesis | The model clause only uses `Nonempty (changeOfRingsOfUniverses j M.obj ≅ L.obj)`; no monomorphism or inclusion is assumed |

`RingComparison` is a natural family of ring equivalences. This is precisely an isomorphism
of sheaves after passage to a common universe; it permits independent value universes
without artificially identifying them. Naturality of its inverse follows from the stated
naturality and the inverse identities. The completed comparison is uniquely determined by
all residue projections. The localized comparison is determined by its localization-unit
square: a ring map must carry each inverse power to the inverse of its image, and the
sheafification universal property then determines the sheaf map.

For slice restriction, the displayed component of the restriction isomorphism is the
base section bijection conjugated by the slice section bijection. Naturality in module
morphisms follows from the two `LisseComparison.map` equations. The pure-tensor equation
on each slice fixes the rationalization comparison uniquely on the sheafification
unit, so these comparisons commute with restriction too. This expresses the natural
compatibility, rather than an arbitrary family of unnormalized isomorphisms. The same
component formulas force coherence after another restriction.

For an abstract pair `(M, θ)`, first apply the integral equivalence to M and the rational
equivalence to θ, then compose with `.tensor`. Apply the inverse equivalences for the
reverse construction. Full faithfulness transports all morphisms, and the unit/counit
and tensor naturality give the inverse identifications of pairs. The `.models` field
also spells out the resulting equivalence of existence statements for each rational L.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, publicly importing
  `Sheaf.NumberTheory.Padics.CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`.
- `Sheaf.Paper.CompletedIntegralOnSmallSite`: `CompletedSite.ring`, `tower`, `transition`,
  `constant`, `quotient`, `constantMap`, `uniformizer`; these belong to the new
  `def-a1-completed-integral-small-site` node. Its public import retains
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, whose live node record is unchanged.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`:
  `CategoryTheory.ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  recorded transparent `SheafOfModules` interface. The Loc objects are precisely its objects.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  `TensorProductOfUniverses` interface: `SheafOfModules.changeOfRingsOfUniverses`,
  `changeOfRingsHomOfUniverses`, and the existing tensor/sheafification constructions.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.isFiniteLocallyFree`, allowing varying rank and rank zero.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`:
  `scalarExtensionRingIsoTmul`, and the proof tool `exists_scalarExtensionRingIso`.
- `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`:
  the actual sectionwise universe lift, publicly available through the small-site construction module,
  is retained for the proof route; no second universe-lift functor is defined.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over` and `overFunctor`; `Mathlib.CategoryTheory.Sites.Over`:
  `Sheaf.over`, `GrothendieckTopology.overPullback`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `toSheafify`;
  `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`, `limit.lift`.
- Proof imports: `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`,
  `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`, and
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`, including its ring and
  abelian-group underlying-set comparisons. The remaining recorded proof modules are
  public dependencies of these imports and the tensor/completion interfaces.

Edge cases checked before and during statement construction:

1. Empty scheme and empty/singleton trivializations: neither X nor C is assumed nonempty;
   the existing finite-locally-free predicate uses the correct sheaf convention.
2. Rank zero and varying/unbounded chart ranks: no global r or positive-rank binder;
   the upstream varying-rank predicate is used rather than a fixed-rank predicate.
3. n=0: the completion index n represents n+1; the separate power-ideal equality covers
   all n, including the zeroth ideal power. No unintended zero quotient is inserted.
4. Identity enlargement and identity representative: no strict universe inequality,
   nonidentity lift or nonidentity equivalence is required.
5. E larger than the module universe: the small-model self-transport conjunct uses
   `max c w`, independent of `u`, while the E comparison is formed in `max u c w`.
6. A zero divisor in localization, or a noninjective localization unit: none of the
   comparison records assumes injectivity, regularity, or a submodule interpretation.
7. Abstract integral models: only scalar-extension isomorphisms occur; no embeddings.
8. Site size: C and all Hom types live in c, so the covering sieves and matching-family
   data are in the smaller universe. The original pro-etale site still has independent
   object and morphism universes; the equivalence is with a genuinely small representative.

Searches (the msearch results are retained in `searches.jsonl` in the sandbox):

- LeanFinder: `Finite locally free module sheaves are invariant under universe enlargement
  and coefficient field isomorphism` returned 8 hits: the LocalGeneratorsData and finite
  type APIs, `Module.Finite.ulift`, `Condensed.finFree`, `instIsEquivalenceFGModuleCatUlift`,
  and finite-presentation APIs. None states completed/localized sheaf universe transport.
- Loogle: `"SheafOfModules", "ulift"` returned 0 hits.
- msearch grep: `(universe|ulift|small).*(LocallyFree|locallyFree)|(LocallyFree|locallyFree).*(universe|ulift|small)`
  returned 0 hits.
- LeanSearch: `Finite locally free sheaves of modules descend under universe enlargement
  with completed coefficient rings` returned 8 hits: `SheafOfModules.free`, `ιFree`,
  finite-type and finite-presentation APIs, and `FGModuleCat.instFullUlift`. No match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` located the reusable locally free
  predicate and coefficient transport API. `grep -rn` for this item's id in
  `lean/WeilConjectures` returned no match. `CompletedPullbackUniverseTransportData`
  concerns completed pullback presentations, not equivalence of these lisse categories.
- Additional searches for completion declarations found scheme-specific completions,
  derived module completion and condensed completion. They do not provide this arbitrary
  small-site/chosen-uniformizer/value-universe interface. The existing generic building
  blocks (constant sheaves, quotient factor maps, inverse sequences and limits) are reused.

## New nodes

`def-a1-completed-integral-small-site` owns `Sheaf.Paper.CompletedIntegralOnSmallSite`
under §1(A). Its self-contained statement introduces a small category C and topology J,
a commutative ring A in an independent universe, a specified element p, and the containing
value universe `max a c w`. It defines the lifted constant ring sheaves, positive-power
quotients, consecutive quotient factor maps, the inverse sequence, its limit and projections,
the quotient cone's limit lift, and the global section which is the image of p. The two
named theorem obligations in that module are exactly the quotient-cone identity and
section naturality spelled out in the new definition node; both retain their proof plans.

Clause matching for the new node: `constant` uses the existing `constantSheaf` on
`ULift.{max c w} A`; `residue A p n` is `A ⧸ Ideal.span {p} ^ (n+1)`;
`transition` sheafifies `Ideal.Quotient.factor`; `tower` is `Functor.ofOpSequence`;
`ring` is the existing `limit`; `quotient` sheafifies the actual quotient homomorphism;
`quotient_compatible` is the consecutive cone identity; `constantMap` is `limit.lift`
of that cone; `uniformizer_natural` is the section restriction equation; `uniformizer`
is the actual family `constantMap (toSheafify (ULift.up p))` with that equation.
`ringSheafify` supplies sheafification by the existing essentially-small-site theorem.
The historical name `uniformizer` introduces no mathematical hypothesis on p.
The construction therefore also covers p=0, a unit p, the zero ring and the empty site.

The source is Bhatt--Scholze Lemma 6.8.2(1), pp. 58--59, with the explicit general-site
presentation needed in the item's agent-written proof step 3. The definition uses the
recorded constant sheaf and inverse limit notions, and cites the original completed
integral coefficient node as its unchanged scheme-specific interface. It asserts no
unproved existence of arbitrary data: quotient maps, cone lift and section are constructed.

Fresh msearch searches were run for this new node: LeanSearch query
`Inverse limit of constant quotient ring sheaves on a small site with chosen element and independent universes`
returned `Profinite.lim`, `Profinite.asLimit`, constant-sheaf counit and general module-sheaf
limit results (8 hits); LeanFinder query
`Completion of a constant ring sheaf as the inverse limit of power ideal quotients with canonical constant map`
returned `AdicCompletion` evaluation and structure-sheaf results (8 hits); grep query
`(completed|Completed|completion).*(constant|Constant|sheaf|Sheaf)|(constant|Constant).*(completion|Completion)`
returned 0 Mathlib hits. The new node records the actual outputs, and the searches are
retained in `searches.jsonl`. Existing general constant sheafification and limits are reused.

DAG searches with `tools/blueprint_refs.py search 'completed integral small site'`
returned no blueprint nodes; the broader `completion` search was inspected too. Local
`rg` of `dag/nodes`, `lean/Sheaf` and `lean/WeilConjectures` found scheme-specific completed
coefficients, completed derived pullback, derived completion and coefficient-presentation
comparison, but no arbitrary-small-site/specifiable-element construction at independent
value universes. In particular, `def-weil-pbc-intrinsic-completion` defines a derived
Koszul completion of modules, and `def-a1-completed-pullback-universe-transport-data`
defines normalized pullback data; neither owns this construction. The proposed new id
was absent. `blueprint_refs.py ancestor` reports null for this item's broken ancestor
chain; the new node faithfully retains that null and prepends the item to its existing via.

## Returned delivery repaired

H13: `def-weil-completed-integral-coefficients` is no longer rebound. Its sandbox copy
has been removed from the delivery. Its live record continues to name
`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, all five `integralConstant*`
declarations, `fixed_by`, and the stage-3 proof review. The proved module is publicly
imported without modification. Its proved compatibility lemma remains proved; the two
small-site obligations belong solely to the new general-site definition node.

H2: the existing dependency JSON is absent from the delivery diff, so its bytes and
all fields are retained from live main. The item's only changes to the live node are
its `lean` record and the addition of `def-a1-completed-integral-small-site` to `stmt_deps`.
The new definition node owns the construction module and all eleven declarations,
and every blueprint docstring in that module now names its new owner. Neither the
item's natural-language statement nor its Lean theorem signature was altered by this repair.

## Second reading by Q49

A final internal reading compared the node, both modules, their signatures and all
comparison fields. A separate worker was not started: the dispatch explicitly prohibits
other agents and assigns the independent review to the maintainer. This section reports
that internal second pass without claiming an independent review.

The pass found and fixed an important size omission in the first draft: comparing only
against raw E would have put `u` into every large module universe. The additional
small-model self-transport conjunct now handles any `max c w`, independently of `u`.
It also checked that the inverse-image ring and its transported uniformizer are used,
rather than choosing the possibly different upstream uniformizer for E0; that the
coefficient comparisons include constants, all projections, transitions and units; that
the category comparisons include every morphism and are normalized on sections; and
that the tensor and slice comparisons use the actual dependency constructions.

No statement correction, embedding hypothesis, fixed-rank restriction or silent universe
equality is introduced. The additional new definition node gives the small-site construction
its own ownership without changing the proved dependency. The item comparison records remain
helpers of the item's assertion and are listed in its `lean.declarations`.

The repair's second reading checked the eleven declarations of the new node against its
statement, including both named theorem obligations, the positive exponent n+1, limit lift
and chosen section. It checked the saved item signature against the pre-repair signature
and found no difference. It checked the five declarations and `fixed_by` in the live
completed-integral dependency record; no sandbox copy remains to override any of them.
The only additional statement dependency is the new definition node, and each delivered
module now has exactly one node owner. No independent reader was started because this
worker's dispatcher prohibits other agents; the maintainer performs independent review.

Validation of the retained packet before repair: `deliver2.py --no-push` returned
`OK (dry run)` at `0aa0a53cc06`. That automated pass did not resolve the maintainer's
ownership objection. The ownership repair above changes the packet rather than merely
rebasing or re-pushing it. Fresh validation of the repaired packet is recorded below.

Fresh `scompile.py` validation passed for both modules separately, with no errors or
warnings: the small-site library module took 11.6 seconds and the item took 28.3 seconds.
The first repaired dry run requested the current preflight schema field `import_flags`
on the new node; it was supplied as an empty list and the dry run was repeated.

The repaired packet then passed `deliver2.py --no-push`: `OK (dry run)` at
`176b5f728b7`, with the new definition node, both modules and no existing dependency
node in the staged set. Per-file compilation and maintainer preflight both passed.
