## Worker report

The module `Sheaf.Paper.QbarCompactSupportBaseChange` states `AlgebraicGeometry.Scheme.qbarCompactSupportBaseChange`. Its only postponed theorem is that theorem, with the six steps of the node's proof in its docstring. `CbcQbarExchangeModel` is a structure packaging the coherent presentation of this same exchange, with real fields and no choice or postponed definition. No node statement is changed.

Clause-by-clause correspondence:

- A prime ell and an algebraic closure of Q_ell: `(l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. The coefficient universe `w` is independent of the scheme universe `u`; the existing small coefficient models `pbcFiniteField.{u}` retain all finite intermediate fields.
- Separated finite-type `f`: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. The arbitrary base change is `{g : Y' ⟶ Y}`; no property of `g` is assumed.
- The finite-level hypotheses at every stage: `c : Compactification f`, `c' : Compactification f'`, `gbar : c'.Z ⟶ c.Z`, `properSquare : ChosenCartesianSquare gbar c'.g c.g g`, and `openSquare : OpenImmersionSquare g' c'.i c.i gbar` retain the chosen base-changed compactification. All four schemes have `IsNoetherian`, a finite `topologicalKrullDim` bound, and stalkwise `IsUnit (l : ...)`. The X and Y' bounds are the named section instances `dX`, `dY'`, `iX`, `iY'`; the Y and X' bounds are explicit theorem arguments. Each stage is an actual finite subextension `Padic.FiniteCoefficientFields l Ω`, not an arbitrary coefficient ring.
- The categories are exactly the recorded raw categories: `pbcStageCategory l Ω X E` and `pbcQbarCategory l Ω X`. In particular no Karoubi envelope or ambient sheaf-category replacement is made.
- The source `Lg* Rf!` and target `Rf'! Lg'*`: model fields `U` and `V` are coherent exact morphisms of the recorded `pbcScalarSystem`s. Fields `source` and `target` identify their composites with integral localization with the actual `cbcCompactSupportSource g c d` and `cbcCompactSupportTarget g' c' d`, restricted by `pbcConditionalIntegral` and then localized. These equations fix every integral map; the raw localization universal property fixes every rational map. These are presentations of the composites used in the node, without introducing a second compact-support or pullback operation.
- The specified exchange: `exchange : StageSystem.Morphism.Hom U.base V.base`, with `normalized` identifying every component on an integral object with localization of `completedCompactSupportExchange`. Its generating tuple, ideal equality, and complete-object witness are universally quantified in this normalization, as in `finiteExtension_compactSupportBaseChange`. `HEq` only accommodates the endpoint equalities in `source` and `target`; it does not identify different coefficient categories or discard endpoint data.
- No additional coefficient-coherence hypothesis: `Nonempty (CbcQbarExchangeModel ...)` is a conclusion from the geometric hypotheses, and the theorem then quantifies over every such model. In particular it applies to the canonical coherent comparisons constructed in the node's proof. The result does not choose an unspecified model as a definition, and does not assume any finite-stage exchange is invertible.
- Isomorphism in the Qbar category: `IsIso (StageSystem.Morphism.descNatTrans D.exchange)` and the explicit `∀ K : pbcQbarCategory ..., IsIso (... .app K)` assert invertibility of the descended exchange and each component. The finite-stage component isomorphy is also explicit, identifying the maps used in the representative formula as isomorphisms from the finite-extension theorem.
- The finite-overfield representative: for every pair `K` and every finite stage `M` with `h : K.stage ≤ M`, the component equals `PairCategory.mkHom M h h ((D.U.base.β h).hom.app K.obj ≫ (D.exchange.τ M).app ((S.T h).obj K.obj) ≫ (D.V.base.β h).inv.app K.obj)`. This is exactly the M-coefficient exchange on T_{M/E}K_E under the prescribed source and target comparisons, with the orientation of the recorded `Morphism.β`. Equal fields are included.
- Independence of M: the same component equals this representative for every M; nonnested choices therefore give the same class. Independence of E and of the representing pair: the last equation compares arbitrary `A`, `B`, and specified isomorphisms `α : A ≅ K`, `β : B ≅ K` by applying `U(α.inv)` and `V(α.hom)`, respectively the analogous beta maps. This states equality at the fixed endpoints belonging to K, rather than comparing arrows with unequal endpoints. Morphism representatives are already quotient classes of the recorded pair category.

Dependencies read and used:

- `thm-cbc-finite-extension`, `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`: `finiteExtension_compactSupportBaseChange`, `cbcCompactSupportSource`, `cbcCompactSupportTarget`, `finiteExtensionCompactSupportExchangeComponent`, and `finiteExtension_cbcComplete`. The theorem's complete signature and docstring were read; its canonical completed exchange supplies the normalization used here. The raw category uses the published lifted small coefficient datum, so the proof docstring records the coefficient-model transport instead of restricting the algebraic closure universe.
- `prop-weil-pbc-descent-functors`, `Sheaf.Paper.PbcDescentFunctors`: `StageSystem.CoherentExactMorphism`, `StageSystem.Morphism.DescentSpec`, `pbcDescentFunctors`, and `pbcConditionalIntegral` (the last is originally in `Sheaf.Paper.PbcScalarExtension`). The general descent statement applies to compact-support composites as well as the displayed direct-image example. Its signature and implementation interfaces were read in full.
- `def-weil-pbc-qbar-category`, `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory`, the actual raw `PbcFiniteStagePairCategory`, whose full definition was read. The finite-stage and scalar-system definitions are from `Sheaf.Paper.FiniteStagePairCategory`: `pbcIntegralStage`, `pbcStageCategory`, `pbcStageLocalization`, and `pbcScalarSystem`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only record with no declaration. Its used notions are Mathlib `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`; there is no module to import for the convention bundle.
- Proof dependencies `Sheaf.Paper.CommonStageCalculus` and `Sheaf.Paper.FiniteStagePairCategory` are imported, along with the public statement dependencies. `lem-cbc-rational-compact-support-coefficient-coherence` currently has no Lean record; it is used in the natural-language proof, but introduces no new notion needed to type this theorem: the coherent stage-family notion and exchange compatibility already are `CoherentExactMorphism` and `Morphism.Hom`. No import is invented for that unstated proof lemma.
- The upstream module `WeilConjectures.CategoryTheory.StageSystem.Functor` was read through `scompile.py --source`. Its `Morphism`, `Hom`, `descNatTrans`, `functor`, and component/representative formulas are used. Its generic `isIso_descNatTrans` is not an exact match to this node: it assumes stagewise invertibility and has neither the geometric hypotheses nor the actual compact-support exchange normalization or representative-independence clauses.

Sources: read the complete current blueprint statement and proof at main-20261015, `sec-six-functors-basics/sk-thm-sf-pf-field/thm-cbc-qbar.md` and `.proof.md`, and the expanded six-step DAG proof. They agree on the statement; no correction or disputed statement is needed.

Edge cases checked: zero K is retained; the empty scheme is not excluded by the finite-dimension or invertibility predicates; g is arbitrary, including identity and non-finite-type base changes within the scheme domains. Equal coefficient stages are permitted by `≤`. Nonnested overfields are handled by the pair-category quotient and finite composita. The normalization permits all finite generating tuples, including an empty tuple when it generates the ideal. Distinct pairs and distinct representing isomorphisms to K are included; no equality between the two pairs is assumed. Both site and coefficient universes remain those of the published interfaces, without adding a universe equality.

Searches made:

- `msearch.py ... leansearch "compact support base change for rational adic sheaves over the algebraic closure of a p-adic field"`: 8 hits for ordinary tensor base change, stability of quasi-compactness and p-adic fields (`IsBaseChange.finsuppPow`, `AlgebraicGeometry.quasiCompact_isStableUnderBaseChange`, `PadicAlgCl.isAlgebraic`, etc.); none gives the rational compact-support exchange or its descent.

- `msearch.py ... leanfinder "Compact support base change over algebraic closure of a p-adic field descends from finite coefficient stages"`: 8 hits, all p-adic fields/algebra/topology, including `PadicComplex.instAlgebraPadic`, `Padic.instProperSpace`, and `PadicInt.algebra`; no compact-support exchange or descent statement.
- `msearch.py ... loogle "CategoryTheory.Functor.mapIso"`: 12 hits for generic functorial preservation of isomorphisms, not this theorem.
- `msearch.py ... grep "compactSupport.*[Qq]bar|[Qq]bar.*compactSupport"`: 0 Mathlib hits.
- `rg` of Mathlib, the upstream `WeilConjectures` source and project `lean/Sheaf` for `thm-cbc-qbar`, `qbarCompactSupportBaseChange`, and `CbcQbarExchangeModel`: no exact declaration. The upstream-name index records only applications at residue-field spectra for this node, which do not state arbitrary compact-support base change. `rg` of the project for compact-support/Qbar combinations found no exact statement. The recorded dependency source was read via the live-source wrapper where absent from the old upstream checkout.

Validation: `scompile.py Q03 thm-cbc-qbar` compiled the final module cleanly, with no warnings or errors, including its library-path check (36.1 seconds, under the 60-second file limit). `deliver2.py Q03 thm-cbc-qbar --no-push` printed `OK (dry run)` for commit `be12e0a07f`: compilation and preflight passed except for the independent second-reading section, which the tool explicitly reserves for the second worker. Nothing was pushed. The independent second reading is left to the second worker, as required by the dispatcher brief.

## Second reading by Q03

I independently opened the sandbox node and Lean file, the repository's item and
all four statement-dependency records, and the declarations below. I also read
both blueprint versions of `thm-cbc-qbar` (master order 1645 and main-20261015
order 1992), the current proof, the expanded six-step DAG proof, and the two
relevant section statements. This theorem has no direct Stacks .tex source:
its source is the blueprint's additional rational coefficient descent. The
compact-support section explicitly restricts the O_E, E and Qbar assertions to
the completed pro-etale categories and their raw rationalizations. There is no
unrecorded smoothness or base-field hypothesis. No repair-note file for this item
is present. No mathematical node statement was corrected, and there are no new
nodes or dependency-module replacements in this delivery.

The list I extracted from the node, with its Lean counterpart and verdict:

1. A prime ell, Q_ell, and a chosen algebraic closure: `l : ℕ`,
   `[Fact l.Prime]`, `Ω : Type w`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
   `[IsAlgClosure ℚ_[l] Ω]`. Exact; the closure universe is independent of the
   scheme universe. Finite stages are `Padic.FiniteCoefficientFields l Ω`, not
   arbitrary coefficient rings.
2. Four schemes, separated finite-type f and arbitrary g with its base change:
   `{X' X Y' Y : Scheme.{u}}`, `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`,
   `{f' : X' ⟶ Y'}`, `{g' : X' ⟶ X}`, `[IsSeparated f]`,
   `[LocallyOfFiniteType f]`, `[QuasiCompact f]`. Exact. No property of g is
   required. The supplied `Compactification`s and the lower
   `ChosenCartesianSquare` and upper `OpenImmersionSquare` are precisely the
   chosen compact-support square required by the cited finite-extension node.
3. The finite-level domain hypotheses at every stage: `IsNoetherian` for all
   four schemes, finite `topologicalKrullDim` bounds for all four, and stalkwise
   `IsUnit (l : ...)` for all four. X and Y' use the section instances `dX`,
   `iX`, `dY'`, `iY'`; Y and X' use `_dimY`, `_dimX'`, `_invY`, `_invX'`
   and their theorem-local Noetherian instances. Exact. The compactifications
   themselves supply properness and the open-immersion properties of their
   factors; no extra finiteness of g is hidden in the model.
4. The coefficient categories: the integral category is `pbcIntegralStage`, the
   finite rational category is `pbcStageCategory`, and the Qbar category is
   `pbcQbarCategory`. Their definitions use `pbcStageDatum`, raw scalar
   localization, and `PbcFiniteStagePairCategory`, respectively. Exact; there
   is no Karoubi envelope, discrete non-torsion etale category, or substitute
   sheaf category. The actual finite fields are retained through `pbcFiniteField`
   and its recorded small-field equivalences.
5. The two composite operations Lg* Rf! and Rf'! Lg'*:
   `CbcQbarExchangeModel.U` and `.V`, with `.source` and `.target`, identify
   their composites with integral localization with `cbcCompactSupportSource`
   and `cbcCompactSupportTarget` restricted by `pbcConditionalIntegral`.
   Those abbreviations are exactly j! then proper push then completed pull,
   and completed pull then j'! then proper push. Exact. Every integral object
   and arrow is fixed, and localization determines rational arrows.
6. The scalar comparisons used in these descents: initially incomplete. The
   first version supplied coherent `.U.base.β` and `.V.base.β` without fixing
   them to the canonical geometric coefficient comparisons. Operation equalities
   alone do not fix beta. Repaired by `.sourceBeta` and `.targetBeta`, each
   using `CbcScalarInverseBetaSpec`. The equation conjugates beta inverse by
   the operation equalities and `pbcScalarIntegralComparison` and identifies it
   with localization of the specified composite inverse comparison. Existential
   `hs` and `ht` are membership proofs in the conclusion, so the specification
   cannot become vacuous from an extra preservation hypothesis. Equal stages
   are included. Exact after repair.
7. The prescribed completed-then-rationalized exchange: `.exchange` is the
   compatible transformation of stage systems, and `.normalized` fixes its
   component to localization of `completedCompactSupportExchange` for every
   integral K and every tuple `a : Fin r → ...` generating the adic ideal.
   Its completeness witness is quantified as in the finite-extension theorem.
   Exact. Naturality and scalar compatibility are the existing `Hom` fields.
   No isomorphism assumption is built into the model.
8. Existence of the geometric descent, with no extra coefficient-coherence
   hypothesis: `Nonempty (CbcQbarExchangeModel ...)` is a conclusion, followed
   by the assertion for every such canonically normalized model D. Exact.
   The repair adds normalization data to this concluded presentation, not
   a new hypothesis on the square. Nothing is defined by choosing from this
   mere existence assertion.
9. Invertibility for each input K: `IsIso (descNatTrans D.exchange)` and
   `∀ K : pbcQbarCategory ..., IsIso (... .app K)`. The explicit finite-stage
   `∀ E K, IsIso ((D.exchange.τ E).app K)` records the finite-stage exchange
   used by the representative formula. Exact; the input K is arbitrary.
10. Representation at every finite overfield M: for every K, M, and
    `h : K.stage ≤ M`, the component equals `PairCategory.mkHom M h h`
    of `β_U.hom ≫ eta_M(T h K.obj) ≫ β_V.inv`. I checked the orientation
    against upstream `Morphism.β`, `mapAt`, `Hom.comm`, and `descNatTrans`.
    Exact. The repaired beta specifications make these precisely the stated
    coefficient identifications, rather than arbitrary coherent comparisons.
11. Independence of M: the preceding equality quantifies over every M above E,
    so it identifies both nested and nonnested choices with the same component.
    The pair category identifies morphisms after enlargement to a finite
    compositum. Exact; equality M=E is permitted.
12. Independence of E and the representing pair: the final equality quantifies
    over arbitrary K, A, B and `α : A ≅ K`, `β : B ≅ K`, comparing the
    components after applying the actual U and V functors to these specified
    isomorphisms. Both arrows have the fixed endpoints for K. Exact. Pair
    morphisms are already quotient classes, so changing a morphism representative
    is also included; no equality between A and B is imposed.

I read the full signature of `finiteExtension_compactSupportBaseChange`, its
component construction, both composite abbreviations, and
`finiteExtension_cbcComplete`. I read `CoherentExactMorphism`, `DescentSpec`,
`pbcDescentFunctors`, both canonical beta predicates and the operation application
in `PbcDescentFunctors`. I read `pbcIntegralStage`, `pbcStageCategory`,
`pbcStageLocalization`, `pbcScalarSystem`, `pbcScalarIntegralComparison`,
`pbcFiniteField`, and `pbcQbarCategory` in their defining modules. The convention
node explicitly defines no new notion and needs no fabricated import. The
upstream stage-system functor module was read through `scompile.py --source`;
its generic `isIso_descNatTrans` assumes finite-stage isomorphy and does not state
this geometric, canonically normalized exchange theorem. The coefficient-coherence
proof dependency currently has no Lean record. Its coherent families were already
expressible by the recorded structures; the missing canonical normalization is
now supplied by the item's helpers, without restating that separate theorem.

The repair's helper declarations are presentations and compositions of existing
canonical constructions, belonging to the item's own exchange, not new independent
notions. `cbcScalarOrdinaryIso` uses the existing
`cbcDatumOrdinaryTransport` universal-counit comparisons around
`pbcScalarOrdinaryPullIso`. `cbcScalarOpenInverse` is its actual inverse mate
under the existing `cbcDerivedOpenAdjunction`s. The proper factor of
`cbcScalarSourceInverse` and `cbcScalarTargetInverse` is the inverse of the
published `pbcScalarDirectImageIso`. Their completed pullback factor comes from
`CbcCompletedScalarComparison.map`, whose `.unit` equation fixes it uniquely
through the actual `ordinaryToCompleted` quotient augmentation. Completion is
reflection after ordinary pullback, and finite coefficient tensor preserves
complete objects, so that equation gives the canonical comparison, also on
ambient inputs before restricting to the integral categories. I opened
`PbcScalarExtension`, `CompletedOpenExchangeTransport`,
`CompleteCompactSupportProetale`, `PbcActualStrictPullback`, and
`PbcCompletedPullbackActual` to check these normalizations. The existing actual
pullback and the datum's pullback are different presentations: the repair
retains their universal transport, instead of assuming definitional equality.
All helpers have real data; no helper theorem or new `sorry` is introduced.
The node's `lean.declarations` now lists all eight declarations.

Edge cases: zero objects and empty schemes are retained; a finite dimension bound
may be zero; ell=2 and every prime are allowed, while invertibility excludes exactly
the prohibited residue characteristics. The coefficient-stage index cannot be empty
because it includes Q_ell, but no extraneous nonempty-index hypothesis is added.
Identity coefficient extensions and identity geometric base changes remain covered.
Nonnested M use a finite compositum. All generating tuples are allowed, including
r=0 whenever its ideal equation holds. Arbitrary pair identifications and every
rational morphism are included. Site and coefficient universes remain independent;
small coefficient models change presentation, not the class of finite extensions.

Independent searches, using different wording from the first worker:

- LeanFinder via `msearch.py`: "Proper pushforward with extension by zero base
  change for algebraically closed l-adic coefficients". Eight hits for stable
  properness, O_X-module pushforward/pullback and condensed functors; none is
  the completed rational compact-support exchange.
- LeanSearch via `msearch.py`: "a natural transformation on a filtered colimit
  of coefficient categories whose finite level components are isomorphisms is
  an isomorphism". Eight general colimit/isomorphism hits; no geometric theorem.
- Loogle via `msearch.py`: `CategoryTheory.NatTrans.isIso_iff_isIso_app`.
  This is only the general equivalence between natural-transformation and
  componentwise invertibility, not a match for the item.
- Mathlib grep via `msearch.py`: `shriek.*baseChange|baseChange.*shriek`:
  no hits. Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf
  for the item's names and new helper names found no duplicate. Searches for
  scalar/open comparisons found existing ordinary, completion and direct-image
  comparisons, which the helpers reuse. The upstream-name index's thm-cbc-qbar
  entries are applications at residue-field spectra, not this arbitrary square.
  `QbarProperBaseChange` was also opened: it imposes properness and concerns
  Rf*, so it is not this theorem and is not reused as an exact match.

Mismatches repaired: canonical scalar comparisons were not characterized; the
repair supplies the proper/open/unit-normalized component equations described
above. The proof docstring originally grouped the six DAG steps into five;
it now follows all six steps explicitly, including construction of the model
and the normalization transports. I also corrected the prose comparison from
`beta.inv ≫ alpha.hom` to `alpha.hom ≫ beta.inv`, which is the typed
arrow A → K → B in Lean composition order. The mathematical node statement, geometric
hypotheses, exchange normalization, and all existing conclusion formulas stay
as read. No `statement_change` or citer audit is needed. The worker report above
is retained as the record of the first version; this section records the repair.

Validation after the repair: `scompile.py Q03 thm-cbc-qbar
lean/Sheaf/Paper/QbarCompactSupportBaseChange.lean` passed both sandbox and
library-path compilation with no warnings or errors (16.7 s and 42.3 s).
`autoImplicit false` is set; every universe and variable is bound. The file has
one postponed proof, the item theorem, and no lines over 100 characters. The
node's `lean.statement` equals the source signature verbatim. Comparing the
sandbox node against the read-only base shows only `lean` changed.

The required `deliver2.py Q03 thm-cbc-qbar --no-push` completed successfully:
`OK (dry run): commit 592b3d828d passes the preflight and compiles; nothing pushed`.
