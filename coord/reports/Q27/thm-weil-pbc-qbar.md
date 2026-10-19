## Worker report

Module: `Sheaf.Paper.QbarProperBaseChange`. Primary declaration:
`AlgebraicGeometry.Scheme.qbar_properBaseChange`.
All mathematical proofs are postponed: the primary theorem has exactly `by sorry`.
The three accompanying declarations are real presentation data and formulas for the
already recorded canonical descent construction; none chooses unspecified data.
No new DAG nodes, dependency restatements, statement corrections, or disputes.

Read the node, every statement dependency and its complete Lean record, the recorded
source signatures/docstrings, the current blueprint main-20261015 order 1419 statement,
and its `blueprint_update` proof. The older split proof supplies the expanded inverse
and representative-independence argument in the theorem docstring. The current statement
is unchanged. The hypotheses needed to form Dbc are inherited from
`def-weil-pbc-qbar-category`, not new restrictions on g.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. The algebraic closure Qbar_l is
  `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
  Its universe w is independent of the scheme universe u. Existing canonical
  `pbcFiniteField` models finite subfields in u; no equality of universes is imposed.
- The four schemes are `X Y X' Y' : Scheme.{u}`. Their `IsNoetherian`, finite
  Krull dimension `Fact (∃ n : ℕ, ...)`, and stalkwise invertibility of l `Fact`
  instances are exactly the base assumptions in the recorded Qbar category.
  Stalkwise invertibility means l is a unit everywhere. This is equivalent to
  the global-sections unit convention used by the finite-extension theorem.
- Proper f: the primary theorem takes only `[IsProper f]`. There is no properness
  assumption on f' (it follows by base change), no assumption on g, and no supplied
  fiber-dimension bound. A bound needed by the finite-extension proof is derived
  from proper finite type and the noetherian finite-dimensional schemes.
- Base change: `sq : ChosenCartesianSquare g' f' f g`, with the chosen pullback
  identification and its projection equations, uses the recorded declaration.
- K in Dbc(X,Qbar_l): `K : pbcQbarCategory l Ω X`. This is literally the recorded
  finite-stage pair category, with its quotient Homs and no Karoubi envelope.
- The descended exchange of the proposition: the conclusion supplies
  `∃ P : PbcQbarExchangePresentation l Ω sq`. Its preservation fields supply the
  restrictions of the actual operations, rather than assuming them. Its four
  coherent families satisfy the recorded `pbcDescentDirectImage` /
  `pbcDescentPullback` equalities. All four scalar beta families satisfy the
  existing `PbcDirectImageBetaSpec` / `PbcPullbackBetaSpec`, so no arbitrary
  coefficient-comparison isomorphisms are substituted.
- The finite-stage exchange is fixed by `P.exchange_eq`: it is the raw localization
  of `pbcActualCompletedExchange (pbcStageDatum l Ω E) sq` on every integral object.
  Every rational object has such an integral object, so this fixes every component.
  It is precisely the completed ambient ringed-topos mate followed by the canonical
  completion/direct-image comparison, as in the scalar-extension dependency.
  This is the finite-extension arrow after the canonical small-field and valuation
  ring size identifications; no condensed-coefficient realization is silently used.
- Source Lg* Rf* and target Rf'* Lg'*: `P.exchange` has type
  `P.Rf.base.functor ⋙ P.Lg.base.functor ⟶
   P.Lg'.base.functor ⋙ P.Rf'.base.functor`.
  Its data is exactly `functorCompIso.inv ≫ descNatTrans P.Ex ≫ functorCompIso.hom`,
  the construction in `pbcDescentOperations`.
- Isomorphism in Dbc(Y',Qbar_l): the first conjunct says
  `∀ K, IsIso ((P.exchange).app K)`. The endpoints belong to the actual Y' pair
  category. The second conjunct asserts invertibility of the specified finite-stage
  exchange components `IsIso ((P.Ex.τ M).app K)`.
- Pair representative (E,K_E), finite overfield M, scalar extension T_{M/E}:
  a pair K has `K.stage` and `K.obj`. The third conjunct quantifies EVERY finite
  `M : Padic.FiniteCoefficientFields l Ω` and `h : K.stage ≤ M`, and identifies
  the descended component with `atStage l Ω sq P K M h`. Its representative is
  `((P.Rf.base.comp P.Lg.base).β h).hom.app K.obj ≫
   (P.Ex.τ M).app ((pbcScalarSystem ...).T h |>.obj K.obj) ≫
   ((P.Lg'.base.comp P.Rf'.base).β h).inv.app K.obj`.
  This is the M-coefficient exchange at T_{M/E}K_E with precisely the specified
  source/target scalar comparisons, stored as `StageSystem.PairCategory.mkHom`.
- Independence of M: that formula holds for ALL overfields, including M=E;
  thus two displayed classes equal the same descended component. Independence
  of E and pair representative: the final conjunct quantifies all K,L and all
  `h : K ≅ L`, and states `A.map h.hom ≫ c_L = c_K ≫ B.map h.hom`.
  Functors send h to isomorphisms, so this is exactly equality after identifying
  the endpoints. It does not incorrectly identify distinct pairs literally.
  Since A and B act on quotient Homs, changing a representative of h does not
  change this equation; quotient equality is built into the existing category.

Dependency declarations used:

- `Sheaf.Paper.PbcDescentFunctors`: `StageSystem.CoherentExactMorphism`,
  `Scheme.pbcDescentDirectImage`, `Scheme.pbcDescentPullback`,
  `Scheme.PbcDirectImageBetaSpec`, `Scheme.PbcPullbackBetaSpec`,
  `Scheme.pbcDescentFunctors`, `Scheme.pbcDescentOperations`.
- `WeilConjectures.CategoryTheory.StageSystem.Functor` (through the above import):
  `StageSystem.Morphism`, `.Hom`, `.comp`, `.descNatTrans`, `.functorCompIso`.
  Read their concrete object, representative-map, beta and component formulas.
- `Sheaf.Paper.PbcQbarCategory`: `Scheme.pbcQbarCategory`.
- `Sheaf.Paper.FiniteStagePairCategory`: `Scheme.PbcFiniteStagePairCategory`,
  `pbcStageCategory`, `pbcIntegralStage`, `pbcScalarSystem`; the underlying
  `StageSystem.PairCategory.mkHom` is the upstream quotient construction.
- `Sheaf.Paper.PbcScalarExtension`: canonical scalar tensor/associator and
  scalar-operation comparisons, including `pbcCoherentScalarExtension` and the
  exchange compatibility. They are used through the concrete system and BetaSpec.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Sheaf.Paper.FiniteExtensionProperBaseChange` (proof-only import):
  `finiteExtensionRationalExchangeComponent`, `finiteExtension_properBaseChange`.
- `Sheaf.Paper.CommonStageCalculus` (proof-only import): `commonStageCalculus`.
- `def-weil-pbc-scheme-conventions` is a convention-only record with no module;
  its properness notion is the existing Mathlib `AlgebraicGeometry.IsProper`.

Edge cases checked: equal coefficient stages are allowed by reflexive h; no strict
inclusion is assumed. Zero objects and uniformizer-power torsion objects remain in
raw rational categories; no nonzero or nonempty hypothesis appears. Empty schemes
satisfy the same dimension bounds (dimension bottom), and are not excluded. Identity
squares and arbitrary chosen pullback identifications remain allowed. No assumption
on g beyond being a scheme morphism is used. Distinct isomorphic pairs are compared
by naturality, not equality of objects. All universes and variables are explicitly
bound and `autoImplicit` is disabled. Every delivered line has at most 100 characters.

Searches for an existing statement (2026-10-16 UTC):

- `msearch.py ... leanfinder` query: "proper base change isomorphism in algebraic
  closure l-adic coefficient finite stage pair category". Eight hits, including
  `BDeRhamPlus`, Galois projection lemmas and condensed scalar constructions;
  none states proper base change on this pair category.
- `msearch.py ... loogle` query: "CategoryTheory.IsIso,
  CategoryTheory.StageSystem.Morphism.descNatTrans". No hits; service does not
  know the project-specific identifier, so this search is inconclusive.
- `msearch.py ... grep` query: "proper.*base.*change|qbar.*[Bb]ase[Cc]hange"
  in AlgebraicGeometry. Twenty-five hits about geometric stability under base
  change; none is this Qbar coefficient theorem.
- `msearch.py ... leansearch` query: "Proper base change isomorphism for Qbar l
  coefficients by finite stage descent". Eight hits: tensor base-change criteria
  and geometric stability of proper/finite morphisms; no matching theorem.
- `rg` of upstream WeilConjectures, Mathlib, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the new declaration names: no collision.
  Searches for the item id and Qbar proper-base-change names found no exact
  existing statement. The side `CondensedQbarBaseChangeCompatibility` concerns
  the distinct condensed category, not this raw finite-stage pair category.
- Read upstream `StageSystem.Morphism.isIso_descNatTrans`: this is a generic
  lemma conditional on an arbitrary stage family being invertible, not the
  geometric theorem, canonical-operation specifications, stage representation
  and independence clauses of this node. It is reusable in stage 3 but is not
  an exact existing match for this node.

Validation: final file-only `scompile.py Q27 thm-weil-pbc-qbar` compilation
passed on the server with no errors or warnings: sandbox 22.8 s, owning module
32.5 s, each within the unchanged 60-second limit. The canonical descent dependency
overlay also compiled cleanly (23.8 s). The node copy changes only `lean`.
The required `deliver2.py --no-push` dry run is the final verification; the independent
second-reading section is deliberately left for the second reader.

## Second reading by Q27

I independently read the sandbox node and entire module, the original source
paragraph and the current `main-20261015` paragraph (order 1419), Stacks
`proetale.tex` Theorem `theorem-proper-base-change` (Tag 09C9), and the statements
and recorded declarations of all seven statement dependencies. I also read the
proof-only finite-extension and common-stage interfaces and the concrete upstream
`StageSystem/Functor.lean` in the shared side framework. There is no repair note
for this item and no `statement_change` in the delivery.

My object/hypothesis/conclusion inventory, matched against the Lean:

1. Fix a prime ell and an algebraic closure of Q_ell. Lean uses `l : ℕ`,
   `[Fact l.Prime]`, `Ω : Type w`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, and
   `[IsAlgClosure ℚ_[l] Ω]`. Verdict: exact; Ω is an arbitrary algebraic closure,
   with no chosen topological completion or condensed coefficient replacement.
2. The four schemes and their coefficient categories have the ambient assumptions
   of `def-weil-pbc-qbar-category`: Noetherian, finite dimensional, and ell
   invertible. Lean has four `Scheme.{u}` objects, four `IsNoetherian` instances,
   four `Fact (∃ n : ℕ, topologicalKrullDim ... ≤ (n : WithBot ℕ∞))`, and
   four stalkwise `IsUnit` facts. Verdict: exact inherited category assumptions,
   rather than extra restrictions on the base-change morphism. Being invertible
   at every stalk is equivalent to the global-section invertibility convention
   of the finite-extension theorem, by gluing the unique local inverses.
3. Proper f and arbitrary g. Lean binds `f : X ⟶ Y`, `g : Y' ⟶ Y`, and has
   only `[IsProper f]` in the theorem. Verdict: exact. Proper f' follows from
   the Cartesian square; no finiteness, smoothness, properness, or flatness of g
   is assumed. The finite-stage fiber-dimension bound is not an added input.
4. The primed schemes and maps are the chosen base change of f along g. Lean
   uses `sq : ChosenCartesianSquare g' f' f g`. I opened its structure: its
   `isoPullback`, `hom_fst`, and `hom_snd` identify the actual diagram with the
   pullback; its inherited `CommSq` supplies commutativity. Verdict: exact,
   including arbitrary chosen Cartesian identifications.
5. K is any object of Dbc(X,Qbar_ell). Lean quantifies every
   `K : pbcQbarCategory l Ω X`. I followed its abbreviation to
   `PbcFiniteStagePairCategory`, its actual rational stage categories and
   `pbcScalarSystem`. Verdict: the recorded raw pair category with quotient
   Homs, not its Karoubi envelope or another coefficient realization.
6. The map is the descended canonical exchange, with source Lg* Rf* and target
   Rf'* Lg'*. Lean concludes the existence of
   `P : PbcQbarExchangePresentation l Ω sq`. Its `presRf`, `presRf'`, `presLg`,
   and `presLg'` are conclusions supplying preservation, not assumptions.
   `Rf_eq`, `Rf'_eq`, `Lg_eq`, and `Lg'_eq` identify the four stage functors
   with the actual restrictions and raw rationalizations
   `pbcDescentDirectImage` and `pbcDescentPullback`. The four `*_beta` fields
   use the dependency's `PbcDirectImageBetaSpec` and `PbcPullbackBetaSpec`.
   I read these predicates, including their quantification at equal stages:
   they fix the localized canonical scalar mates, conjugated by the specified
   integral/scalar comparisons. They do not allow arbitrary scalar isomorphisms.
   `exchange_eq` fixes every integral-object component of `Ex.τ E` to the
   localization of `pbcActualCompletedExchange`. Raw localization retains the
   integral objects, so this fixes every rational-object component. I opened
   `pbcActualCompletedExchange`: it uses the actual ringed-topos adjunction
   mate, completion, and the canonical direct-image/completion comparison.
   Finally `P.exchange` is exactly `functorCompIso.inv ≫ descNatTrans P.Ex ≫
   functorCompIso.hom`, whose type is the required ordered pair of composite
   descended functors. Verdict: canonical map, correct endpoints, no hollow
   map hypothesis or replacement exchange. The presentation merely packages
   the canonical witnesses of the existing descent proposition.
7. The descended component is an isomorphism in the Y' coefficient category.
   Lean's first conjunct is `∀ K, IsIso ((P.exchange).app K)` in precisely
   that category. Verdict: exact. The second conjunct states that every
   specified finite-stage component `(P.Ex.τ M).app K` is invertible, rendering
   the node's phrase "M-coefficient exchange isomorphism" on all finite stages.
8. For a pair (E,K_E), and any finite overfield M containing E, the map is
   represented by the M-exchange at T_{M/E} K_E. The pair fields are `K.stage`
   and `K.obj`; the third conjunct quantifies every `M` and `h : K.stage ≤ M`.
   `atStage` is `PairCategory.mkHom M h h` of source composite beta, followed
   by `(P.Ex.τ M).app ((pbcScalarSystem ...).T h |>.obj K.obj)`, followed by
   inverse target composite beta. I checked `Morphism.β`, `.comp`, `.Hom.comm`,
   `.descNatTrans`, and `.functorCompIso` in the actual framework source.
   Their orientations give exactly this formula; the latter comparison has
   identity object components. Verdict: correct canonical representative and
   comparisons, with the same quantifier order as the node.
9. Independence of E, M, and representative. The third conjunct equates the
   class at every overfield to the same descended component, proving
   independence of M. The final conjunct quantifies every `K L` and `h : K ≅ L`
   and states `A.map h.hom ≫ c_L = c_K ≫ B.map h.hom`. Verdict: exactly
   independence after identifying the endpoints of two isomorphic pairs.
   It preserves the node's distinction between different pairs and literal
   equality. Since all maps are quotient Homs, replacing a representative of
   h leaves this equation unchanged. The existential P precedes all these
   universal clauses, so the same canonical operations serve every object.

Source and dependency checks: Tag 09C9 assumes proper f, arbitrary g, a
Noetherian coefficient ring with torsion residue quotient, derived completeness,
bounded-below étale-origin reductions, and perfect coefficient quotients. These
are supplied at the finite stages by the recorded integral categories and the
valuation-ring coefficient datum; they are not additional hypotheses to expose
on this Qbar theorem. The node's own category definitions supply the stronger
ambient constructibility/size conventions used here. The finite-extension
theorem's actual signature has proper f and f', a fiber bound, and four
preservation witnesses in its conclusion. The proof docstring explains their
use, the small-field/valuation-ring identifications, scalar compatibility,
inverse equations, common-stage comparison, and naturality, covering both the
current blueprint proof and the node's three expanded proof steps.

Edge cases: the finite-field index is not empty (it contains Q_ell) and reflexive
`h` allows M = E. No strict inclusion or nonzero-object condition occurs.
Zero and uniformizer-power-torsion objects remain in the raw rational category.
Empty schemes are allowed, with Krull dimension bottom and vacuous stalk unit
condition; no `Nonempty` scheme assumption occurs. Identity squares and identity
base-change maps are included. No exponent or cohomological-degree restriction
is introduced; the coefficient dependencies use the positive-exponent n+1 tower.
Every prime ell and every characteristic allowed by invertibility is covered.
The scheme universe u and algebraic-closure universe w are independent. I read
`pbcFiniteFieldSmall` and `pbcFiniteField`: finite-dimensional intermediate fields
are transported by `Shrink.algEquiv` into the scheme universe, and the valuation
ring is lifted into the coefficient universe. Thus no equality w = u, or site
object/morphism universe equality, is imposed by this statement. `autoImplicit`
is false, and inspection finds all variables and universes bound.

Independent H4 searches (2026-10-17):

- `msearch.py ... leanfinder` with "canonical exchange invertibility algebraic
  closure p-adic coefficients descent finite extensions": eight hits about
  `PadicAlgCl`, its field/algebra embeddings, and p-adic completion; no match.
- `msearch.py ... leansearch` with "descent of proper base change from finite
  coefficient fields to algebraic closure": eight hits concerning descent and
  geometric stability of proper/finite morphisms, not this coefficient theorem.
- `msearch.py ... loogle` with `CategoryTheory.IsIso, CategoryTheory.NatTrans`:
  zero hits. `msearch.py ... grep` with
  `descNatTrans|qbar_properBaseChange|PbcQbarExchangePresentation`: zero hits in
  its upstream search scope. The side framework was therefore searched directly.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, using Qbar/padicAlgCl/base-change and descended
  exchange phrases: no existing theorem on this actual pair category and no
  collision with the four delivered names. I opened the side
  `CondensedQbarBaseChangeCompatibility` source: it concerns the distinct
  condensed bounded-constructible categories over a field with finite-type
  hypotheses. I also read the actual generic `isIso_descNatTrans` signature:
  it assumes invertibility of a supplied family and does not supply the
  canonical geometric operations, exchange, or finite-stage identification.
  Neither is an exact existing match.

No mathematical mismatch was found and no Lean or node change was needed.
There are no new nodes or dependency modules to review under H12/H13. The
three helper declarations contain explicit data/formulas and no `sorry`; the
only postponed proof is the named main theorem, with its source and full proof
docstring. All declarations have the blueprint/source docstrings, all lines
are at most 100 characters, and `lean.statement` equals the theorem signature
verbatim. Only the item's `lean` record differs from the repository node.
This second reading changes only this report. Compilation and delivery preflight
results are recorded below after running the required wrappers.

Second-reader validation: `scompile.py Q27 thm-weil-pbc-qbar
lean/Sheaf/Paper/QbarProperBaseChange.lean` passed cleanly: sandbox 20.3 s,
owning module 33.1 s, with the unchanged 60-second per-file limit. There were
no errors or warnings.

`deliver2.py Q27 thm-weil-pbc-qbar --no-push` returned
`OK (dry run): commit df9a34fe31 passes the preflight and compiles; nothing pushed`.
