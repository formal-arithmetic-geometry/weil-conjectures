## Worker report

Repair of L's return for immutable head `8bd1b06c9256`, dated 2026-10-16.
The delivery states `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`
in `Sheaf.Paper.StrictTowerExchangeMateNormalization`. All theorem proofs remain
`sorry`. Definitions use actual functors, adjunctions, or uniquely characterized
comparisons. The DAG statement is unchanged; this repair corrects its Lean rendering.

The repaired primary theorem has three conjuncts, in node order:

1. The actual strict arrow is `H.inv ≫ R.map e ≫ HPrime.hom`.
2. At every positive level, common corner identifications carry the four strict
   arrows to `fourArrows sq K hK W n`, retaining the witness data `W n`.
3. `Res.map v' ≫ d.hom = b.hom ≫ E.app barK` in the derived category of the
   whole strict tower category.

This is a substantive change to the signature. Previously the lift formula and
its finite-level identifications appeared only in dependency definitions and the
proof explanation. They are now explicit conclusions. The definitions of H and
H-prime now display B and D as their actual targets and use `towerProjection`
directly. Their source and target types spell out R(M), R(N), B and D.

### Hypotheses and objects

| Node hypothesis or object | Lean rendering |
|---|---|
| Four schemes and edges | Explicit `X' X Y' Y : Scheme.{t}` and `g' f' f g` binders. |
| Chosen cartesian square | `sq : ChosenCartesianSquare g' f' f g`, including the chosen pullback iso and projection equations. |
| Proper f | `[IsProper f]`, with no properness hypothesis on g. |
| Noetherian adic A, I, finite perfect positive quotients | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`, whose inherited datum retains these hypotheses. |
| Actual finite and completed coefficient sheaves | `d.finiteRing T n`, `d.completedRing T`, `d.projection T n`, from the published datum. |
| Arbitrary unbounded completed-coefficient K | `K : d.derived X`. |
| Canonical quotient-tower completeness | `hK : d.TowerComplete X K`, invertibility of the specified completion unit. |
| Fixed etale L_n and alpha_n for each positive level | `W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1)) ((d.reduction X n).obj K)`. The structure retains `complex : DerivedCategory.Plus ...` and `iso`; it is not a mere existence proposition. |
| J and positive indexing | `ℕᵒᵖ`, where index n denotes exponent n+1; n=0 is A/I. |
| Strict reduction K-bullet | `(completedReductionTower X d).obj K`. |
| Constant ring sheaf | `exchangeConstantRing T A = adicLisseConstantRing T A`. |
| Constant-to-completed map | `exchangeScalar d T = adicDatumScalar T ... ≫ (pbcCompletedComparison T d).hom`; it sends a to its compatible residue sections. |
| Strict constant module tower category T_T | `exchangeTowers T (exchangeConstantRing T A) = ℕᵒᵖ ⥤ proEtaleRingModules T ...`. |
| Res and bar K | Termwise `exchangeTowerModuleRes`, exact descent `exchangeTowerRes`, then its object map on the strict reduction tower. |
| G_u and R_u^T | `exchangeConstantPull` and `exchangeConstantPush`, obtained from the termwise ordinary module functors. |
| Derived adjunction | `exchangeTowerAdjunction`, deriving `proEtaleRingModuleAdjunction ... |>.whiskerRight ℕᵒᵖ`. |
| D(T_T) | Mathlib `DerivedCategory (exchangeTowers T ...)`; localization is after formation of strict diagrams. |
| Canonical theta | `(exchangeConstantSquare sq).exchangeTowerSquare`, ordinary composition transported around the scheme/coefficient square, whiskered to strict towers, then descended. |
| Canonical E^T | `(exchangeConstantSquare sq).exchangeTowerMate`, Mathlib `mateEquiv` of precisely those adjunctions and theta. |

### Strict realization and conclusions

The ringed diagram-site presentation is represented by its strict module-diagram
category, as in `exists_diagramSite_realization`. Delta is the constant-diagram
functor; Q is the actual quotient diagram. The existing `completedReductionTower`
is the total left derived functor of `completedReductionModuleTowerFunctor`.
Its ordinary value at n is quotient tensor with the specified quotient-transition
map. `IsCompletedReductionTowerPair` retains the universal derived counit and its
isomorphism on every K-flat representative. Thus it is exactly
Delta F tensor-derived-over Delta A with Q, computed as one diagram, rather than
a family of unrelated derived objects. No additional tensor or reduction notion
is introduced in this repair.

The completed termwise functors are the published `d.towerPull` and `d.towerPush`.
Their normalized adjunction is `d.towerAdjunction`. The ambient objects are
E=`(d.pull g').obj K`, M=`(d.pull g).obj ((d.push f).obj K)` and
N=`(d.push f').obj E`. The map e is `(d.integralExchange sq).app K`.

`exchangeRealizationH` has source R(M) and target
`(d.towerPull g).obj ((d.towerPush f).obj (R_X.obj K))`, exactly B.
It is inverse reduction/pullback chi followed by `towerPull g` of the
canonical `towerProjection f K`. This projection is not a supplied arbitrary map:
its published definition is `towerAdjunction.homEquiv` of chi followed by
reduction of the actual ambient counit. This is the diagram-site
counit-tensor-identity adjunct prescribed in the node.

`exchangeRealizationHPrime` has source R(N) and target
`(d.towerPush f').obj ((d.towerPull g').obj (R_X.obj K))`, exactly D.
It is `towerProjection f' E` followed by tower direct image of inverse chi.
Both definitions are isomorphisms, using `towerProjection_isIso` and the specified
pullback/reduction isomorphism. Perfectness and levelwise tower cohomology supply
that invertibility in the published dependency.

B and D are also the existing `d.fourTowerCorners ... K 1` and `... K 3`.
The strict v-prime is the existing `d.towerV' sq K` used by
`completedBaseChangeMap`. The first conjunct now explicitly identifies that very
map with `H.inv ≫ (completedReductionTower Y' d).map e ≫ HPrime.hom`.
This equation is in the derived category of strict completed-coefficient towers.

The second conjunct quantifies over every `n : ℕ` and retains common isomorphisms
`α i` from the four evaluated strict corners to the scalar-restricted finite
corners. Its four equations identify `towerH`, `towerH'`, `towerV`, and `towerV'`
with the actual `h`, `h'`, `v`, and `v'` of `d.fourArrows sq K hK W n`.
Here `towerH` is H after the source chi, exactly the alternative transported-source
presentation allowed in the node; H-prime is `towerH'`. The witnesses are therefore
used in the conclusion, with their finite coefficient action and no uniform bound.

The specified b and d are components of `exchangeCornerB` and `exchangeCornerD`.
Their definitions compose `exchangeResPull`, `exchangeResPush`, and associators.
The former descends the ordinary tensor-balancing restriction/pullback iso;
the latter is uniquely normalized by `ExchangeResPushNormalized`, its equation
with the universal right-derived units on every strict tower complex. This fixes
the comparison before any evaluation. It agrees with the published finite scalar
and K-injective direct-image evaluation comparisons.

The last conjunct explicitly states the requested equality with these b, d,
v-prime and E^T. Lean writes composition in execution order, hence
`Res.map v' ≫ d.hom = b.hom ≫ E.app barK` is the displayed node equation.
`exchangeStrict_naturality` quantifies over every input morphism K → L;
`exchangeStrictNatTrans` packages this specific strict v-prime. The corner isos
and E^T are natural transformations, so the equation is natural in input morphisms.
No statement infers equality of derived tower maps from equality of evaluations.

### Dependencies read and used

The current server sources were read through `scompile.py --source`, including
the full signatures and normalization docstrings. Module names below have prefix
`Sheaf.` unless a Mathlib module is named explicitly.

| Dependency | Module and declarations |
|---|---|
| Chosen square | `AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`. |
| Scheme conventions | Mathlib `Scheme`, morphisms and `IsProper`; the node is a convention collection. |
| Adic datum, strict quotient tensor | `Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, `completedReductionTower`, `IsCompletedReductionTowerPair`, `completedReductionEvaluation`. |
| Derived inverse limit and completeness | `Paper.CompletedDerivedInverseLimit`, `Paper.CompletedRlimFunctor`, `Paper.CompletedPullback`: `CompletedDerivedInverseLimit`, `completedRlim`, `TowerComplete`. |
| Fixed finite witnesses | `Paper.RingedEtaleOriginWitness`: `FiniteEtaleOriginWitness`, `finiteOriginConstantIso`. |
| Completed map | `Paper.CompletedBaseChangeMap`: `AdicCoefficientDatum.completedBaseChangeMap`, using the same `towerV'`. |
| Constant sheaf | Mathlib `CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`. |
| Small site | `AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`, `Scheme.ProEt`, `ProEt.topology`. |
| Module category | `CategoryTheory.RingedSiteModules`: `ringedSiteModules`, Mathlib `SheafOfModules`. |
| Inverse systems | Mathlib `CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`. |
| Scalar restriction | Mathlib `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`. |
| Constant/completion | `Paper.ConstantCompletionEquivalence`: `ConstantCompletion.equivalence`, and the scalar map/comparison imported through the adic coefficient modules. |
| Ordinary operations | `AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations` and its arbitrary-ring operations imports: `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`, `proEtaleRingModuleAdjunction`. |
| Derived adjunction | `CategoryTheory.PreDerivedAdjointFunctorsGeneral`: `preDerivedAdjunctionGeneral`; actual `mapDerivedCategoryRightDerivedAdjunction` construction. |
| Derived category | Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`. |
| Canonical composition | `AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`: `proEtaleCanonicalPullbackComposition`, with ordinary sectionwise normalization. |
| Mate | Mathlib `CategoryTheory.Adjunction.Mates`: `mateEquiv`. |
| Tower direct image and projection | `Paper.CompletedDirectImageLimits`: `towerAdjunction`, `towerPushEvaluation`, `towerProjection`, `reductionTowerPullbackIso`. |
| Diagram-site presentation | `CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`. |
| Ambient exchange | `AlgebraicGeometry.ProEtaleAmbientRingedExchange`: `proEtaleAmbientRingedExchange`. |
| Finite corners | `Paper.FourCorners`: `fourCorners`, `integralExchange`, `integralRingIso`. |
| Projection definition | `Paper.ProjectionFormulaBaseChangeNaturality`: `proEtaleProjectionFormulaMate`. |
| Finite arrows | `Paper.FourArrows`: `fourArrows`, `finiteProjection`, `finiteExchangeIso`. |
| Perfect projection | `Paper.PerfectProjectionFormula`: `PerfectProjection.perfect_projection_formula`. |
| Levelwise abelianity | Mathlib `CategoryTheory.Abelian.FunctorCategory`: `Abelian.functorCategoryAbelian`, exact evaluation. |
| Specified strict towers | `Paper.CompletedTowerCompatibility`: `fourTowerCorners`, `towerH`, `towerH'`, `towerV`, `towerV'`, `fourTowers_compatibility`. |
| New strict operations | `Paper.StrictTowerOperations`: termwise operations and `StrictTowerRingedSquare.exchangeTowerMate`. |

Sources read: the blueprint completed-exchange-coherence module's proof and source
note, and Stacks `sites-cohomology.tex` at `remark-base-change` (07A7),
`equation-projection-formula-map` (0B56), `remark-compatible-with-diagram` (0E48),
plus `proetale.tex`, `theorem-proper-base-change` (09C9). The local read-only
literature mirror is `/home/ubuntu/work-bp/sheaf/literature`. The strict-tower
normalization is the DAG's explicit supplement; 09C9 omits map construction.

Edge cases checked: zero K; empty schemes; identity squares and edges; n=0
represents exponent one; zero/unit ideals and the zero ring when admitted by the
adic datum; unbounded K; independently bounded-below witnesses with unrelated
bounds. There is no common bound or cross-level compatibility on W, no assumption
that a scheme is nonempty, and no extra characteristic restriction. The site's
object universe t+1 and morphism universe t are retained. Module values and
coefficient A use t+1; no additional equality between site universes is imposed.

Searches for this repair: `msearch.py leanfinder` with “Strict reduction tower
exchange is conjugated by projection formula isomorphisms and agrees with the
constant coefficient tower adjunction mate” returned eight generic algebra/scalar
comparison hits, none the theorem. Loogle `CategoryTheory.mateEquiv` returned
12 generic mate declarations, reused here. Mathlib grep
`towerV|exchangeRealization|strictTowerExchange` returned zero hits. Direct `rg`
of upstream WeilConjectures and shared `lean/Sheaf` for the proposed theorem and
realization names found no declaration. Earlier LeanSearch, Loogle, LeanFinder,
Mathlib/upstream/side grep and DAG/blueprint searches are retained verbatim in the
new node's `mathlib_searches` and `searches.jsonl`. Those searches found the
published prerequisites, which are reused. No statement dispute remains.

## New nodes

`def-weil-pbc-strict-tower-operations` supplies the missing construction from
paragraph two: termwise module towers, their exact pullback and derived direct
image, the derived ordinary adjunction, canonical composition square and mate,
including constant-section normalization for arbitrary commutative A. Its module
is `Sheaf.Paper.StrictTowerOperations`. It reuses the existing ordinary module
operations and Mathlib mates. Sources are the blueprint's strict normalization
supplement and Stacks 07A7/0D6D. The recorded searches found generic adjunction
operations but no DAG or library declaration for this specified ringed tower
construction. Its previously delivered module and node are unchanged.

## Repair verification

The returned omissions are addressed as follows: H/H-prime and B/D have explicit
types and canonical adjunct constructions; the primary theorem asserts the
strict v-prime formula; b/d are the specified constructed natural isomorphisms;
the last equality is in `DerivedCategory (exchangeTowers Y' ...)`; the retained
level witnesses occur in every finite-arrow comparison; this root `report.md`
contains the complete hypothesis/clause inventory.

Validation: `scompile.py Q13 lem-weil-pbc-strict-tower-exchange-mate-normalization`
compiled both delivered modules separately, with no errors or warnings and the
unchanged 60-second limits. Library passes took 16.1 seconds for operations and
20.7 seconds for normalization. `deliver2.py ... --no-push` printed
`OK (dry run): commit db4257d46b passes the preflight and compiles; nothing pushed`.
The delivery has exactly the two Lean files, two node records and this report.
Only the item's `lean` and its previously authorized new-definition dependency
addition differ from the shared node; its mathematical statement is unchanged.

## Earlier second reading (a previous round; superseded)

The previous second-reading text is archived in
`scratchpad/report-before-return-repair.md`. It predates this substantive repair
and does not certify the new signature. The dispatcher-designated second reader
must read the repaired module and this inventory before actual delivery.

## Second reading by Q13

This is the independent reading of the repaired delivery, not the superseded
reading archived in scratchpad. I opened the item node, its six proof steps,
both delivered modules, the new definition node, the blueprint source and the
Stacks source, and the dependency declarations described below. I found no
remaining mathematical mismatch. I leave the correct Lean and node records
unchanged and add this fresh second-reading certificate.

Source check: the blueprint `lemma-weil-pbc-completed-exchange-coherence.md`
first forms compatible finite-level equations, then applies Rlim and the same
reconstruction, projection and direct-image comparisons. Its source note
expressly adds coherence beyond Stacks 09C9. In `sites-cohomology.tex`,
`remark-base-change` (07A7) constructs the unbounded ringed-topos exchange as
pullback composition followed by the counit, transposed under the other
adjunction. `equation-projection-formula-map` (0B56) constructs projection by
the counit tensored with identity. `remark-compatible-with-diagram` (0E48)
is the tensor/exchange diagram with these arrows. The surrounding paragraphs
assume ringed topoi and arbitrary derived objects, not bounded complexes or
Noetherian schemes. In `proetale.tex`, `theorem-proper-base-change` (09C9)
assumes proper f, a Noetherian coefficient ring, torsion A/I, derived
completeness, bounded-below etale-origin finite reductions and perfect positive
quotients; its proof explicitly omits construction of the map. The item's
strict-diagram construction is its recorded agent supplement. I did not
attribute that supplement to a stronger statement of 09C9.

My inventory, in node order, is as follows. Each verdict includes inspection
of the referenced definitions rather than inference from their names.

| Object, hypothesis or conclusion in the node | Lean rendering and verdict |
|---|---|
| Four schemes and the four directed edges | Section variables `X' X Y' Y : Scheme.{t}` and `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y`. Exact. |
| Chosen cartesian square | `sq : ChosenCartesianSquare g' f' f g`. The dependency extends `CommSq` with `isoPullback`, `hom_fst` and `hom_snd`, so it supplies the chosen Cartesian identification as well as commutativity. Exact. |
| Properness of f | `[IsProper f]` on the main theorem. No properness of g or Noetherianity of the schemes is assumed. Exact. |
| Commutative Noetherian A and adic ideal with the stated positive quotients | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`. `CompleteCoefficientDatum` supplies `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion` and `quotientPerfect`; the extension supplies `quotientFinite`. Exact. |
| Actual finite function coefficient sheaves, their quotient maps, and completed ring | `d.finiteRing`, `d.projection`, `d.completedRing` unfold to `reductionCoefficient`, the actual quotient-system limit projections, and `completedReductionCoefficient`. The system is sheafified postcomposition on continuous component functions, not a replacement of the completed ring by constant A. Exact. |
| Arbitrary unbounded K over the completed coefficient ring | `K : d.derived X`, namely `DerivedCategory (reductionModules X (d.completedRing X))`. Exact. |
| Derived completeness via the specified strict reduction tower | `hK : d.TowerComplete X K` is `IsIso (d.completionUnit X K)`; that unit uses the actual quotient augmentation and constant-tower/Rlim adjunction. Exact. |
| Separate retained etale-origin witnesses for every positive level | `W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1)) ((d.reduction X n).obj K)`. Its `complex` is in the etale `DerivedCategory.Plus`, and `iso` retains the comparison after the canonical constant/function transport. Exact; there is no uniform bound or compatibility assumption on W. |
| Positive-index category and strict reduction tower | `ℕᵒᵖ`, reindexed by n ↦ n+1, and `(completedReductionTower X d).obj K`. The dependency derives the whole ordinary tensor diagram and keeps the quotient transitions. Exact. |
| B, D and the specified strict v-prime of completed base change | `d.fourTowerCorners ... K 1`, `... K 3` and `d.towerV' sq K`. I opened `CompletedBaseChangeMap`: its ordered composite uses this very `towerV'`. Exact. |
| Constant sheaf and specified constant-to-completed scalar map | `exchangeConstantRing T A` abbreviates `adicLisseConstantRing`; `exchangeScalar d T` is `adicDatumScalar` followed by `pbcCompletedComparison`. Its map is the compatible-residue map; `exchangeScalar_comm` states its coefficient square. Exact. |
| The constant-coefficient strict module-tower category and its derived category | `exchangeTowers T R = ℕᵒᵖ ⥤ proEtaleRingModules T R`; its localization is `DerivedCategory (exchangeTowers T R)`. The ordinary module category is the dependency's `ringedSiteModules`, hence Mathlib `SheafOfModules`. Exact. |
| Termwise Res and bar K | `exchangeTowerModuleRes` is whiskered `proEtaleRingRestrictScalars`; `exchangeTowerRes` is its exact derived descent. The mate is evaluated at `(exchangeTowerRes d X).obj ((completedReductionTower X d).obj K)`. Exact. |
| G, total right-derived termwise direct image, and their specified derived adjunction | `exchangeConstantPull`, `exchangeConstantPush`, `exchangeTowerAdjunction`. The ordinary adjunction is exactly `proEtaleRingModuleAdjunction ... |>.whiskerRight ℕᵒᵖ`; its derived adjunction is `mapDerivedCategoryRightDerivedAdjunction`. The imported operations module reexports the arbitrary-ring interface, so A is not accidentally assumed finite. Exact. |
| Canonical theta around the square | `exchangeModuleComposition` is uniquely fixed by the sectionwise direct-image conjugate, with the already normalized ordinary module adjunctions. `exchangeModuleSquare` transports along the scheme/coefficient equality; `exchangeTowerSquare` applies it to strict diagrams before descent. I compared its normalization with `proEtaleCanonicalPullbackComposition_existsUnique`. Exact. |
| Canonical constant-coefficient exchange mate | `(exchangeConstantSquare (A := A) sq).exchangeTowerMate`, defined by Mathlib `mateEquiv` for those two derived adjunctions and `exchangeTowerSquare.hom`. `Mates.lean` has the required unit-square-counit direction. Exact. |
| Ringed diagram-site realization, Delta and quotient diagram, and R(F) | The reused `completedReductionTower` is the total left derived functor of the ordinary quotient-tensor tower functor, with `coherenceReductionTowerCounit` invertible on K-flat models. Thus one resolution supplies Delta F tensor Q with all quotient arrows. `exists_diagramSite_realization` is the exact diagram-site presentation used in the proof, not a competing definition. Exact. |
| E, M, N and ambient e | `d.pull g'`, `d.pull g` after `d.push f`, `d.push f'` after `d.pull g'`, and `(d.integralExchange sq).app K`. `FourCorners` uses the canonical profinite coefficient identifications and normalized ambient ringed exchange. Exact. |
| H from R(M) to B | `exchangeRealizationH` explicitly has this source and target. Its factors are inverse `reductionTowerPullbackIso` and tower pullback of `towerProjection f K`. The latter is defined as `towerAdjunction.homEquiv` of chi followed by reduction of the ambient counit. Exact projection adjunct, not an arbitrary arrow. |
| H-prime from R(N) to D | `exchangeRealizationHPrime` explicitly has this source and target. It is `towerProjection f' E` followed by tower pushforward of inverse chi. Exact. |
| H and H-prime are isomorphisms | They are `Iso` values; `towerProjection_isIso` and the normalized reduction/pullback iso supply their inverses. The dependency uses perfect finite coefficients and levelwise cohomology, not faithfulness of derived evaluation. Exact. |
| The specified strict conjugate lift | The first main conjunct is exactly `d.towerV' sq K = H.inv ≫ R.map e ≫ HPrime.hom`. This is equality in the completed-coefficient derived strict-tower category. Exact. |
| Evaluations are the specified finite arrows with retained witnesses | The second main conjunct quantifies over every `n`, with common corner isomorphisms `α : ∀ i : Fin 4, ...`. Its four equations identify evaluated `towerH`, `towerH'`, `towerV`, `towerV'` with scalar restrictions of the four fields of `d.fourArrows sq K hK W n`. The first source is transported by chi, as explicitly allowed in the node. Exact. |
| Specified natural corner isomorphisms b and d | `exchangeCornerB` and `exchangeCornerD` compose the ordinary-normalized `exchangeResPull`, the derived-unit-normalized `exchangeResPush`, and associators. `ExchangeResPushNormalized` is an equation on every strict tower complex with the universal right-derived units and the actual termwise ordinary comparison, not just its evaluations. `exchangeResPush_existsUnique` fixes its choice uniquely. Exact. |
| d composed with Res(v-prime) equals the constant mate composed with b | The last conjunct is `Res.map towerV' ≫ cornerD.hom.app R(K) = cornerB.hom.app R(K) ≫ constantMate.app barK`. Lean's composition order gives exactly the node's displayed equation in `D(𝒯_Y')`. Exact. |
| Naturality in input morphisms | `exchangeStrict_naturality` quantifies over all `a : K ⟶ L`, and `exchangeStrictNatTrans` packages the specified v-prime. b, d and the mate are natural transformations. This gives the requested natural equality, including morphisms between different inputs. Exact. |
| No evaluation-faithfulness claim | The main equality is a strict derived-diagram morphism equality. The six-step proof uses tensor/exchange coherence on that category; evaluation identifies arrows and detects isomorphisms only. Exact. |

Dependency checks: I read the signatures and relevant definitions in
`ChosenCartesianSquare`, `AdicCoefficientDatum`, `CompletedAdicCoefficientDatum`,
`CompleteCoefficientDatum`, `CompletedDerivedInverseLimit`, `CompletedRlimFunctor`,
`CompletedPullback`, `RingedEtaleOriginWitness`, `FourCorners`, `FourArrows`,
`CompletedBaseChangeMap`, `CompletedTowerCompatibility`, `CompletedDirectImageLimits`,
`ProEtaleOperations`, `ProEtaleOperationsCanonicalAdjunction`,
`ProEtaleIntrinsicFiniteOperations`, `ProEtaleRingSheafChangeAdjunction`,
`ProEtaleAmbientRingedExchange`, `ProEtaleCanonicalPullbackComposition`,
`ProEtaleDerivedCategory`, `RingedSiteModules`, `DiagramSiteRealization`, and
`PreDerivedAdjointFunctorsGeneral`. I also opened the actual upstream derived
adjunction constructor and Mathlib's mates and whiskering constructors. The
recorded general operations, rather than the finite-only primary entry, are
what the delivery uses. The retained module and site universes are those of
these declarations. There is no dependency module in the delivered packet.

New definition node reading (H12/H13):
`def-weil-pbc-strict-tower-operations` defines precisely the ringed strict-tower
operations and canonical composition mate of paragraph two. Its ring sheaves,
edge isomorphisms and `coherent` field match `StrictTowerRingedSquare`. Termwise
functors, exact descent, total right derivation, the chosen ordinary adjunction,
and its mate have actual data. The helper existence statements fix their chosen
comparisons by uniqueness; no bare Nonempty choice supplies a canonical map.
The new node is in the item's chapter and unit, has kind definition, status split,
empty proof and proof_deps, null mathlib_match, complete created metadata and
blueprint ancestry via this item, and none/none lean_audit. Its statement citations
match stmt_deps and the item cites it. Its searches include successful LeanSearch,
LeanFinder, Loogle and Mathlib/upstream/project/DAG grep, not only an unavailable
search. None gives this specified ringed strict-tower construction. Existing
ordinary functors, derived adjunctions, tensor comparisons and Mathlib mates are
reused; no alternative coefficient sheaf or module category is defined.

Edge cases: the indexing category is fixed positive integers, so an empty
index set is not a case of this node. Lean n=0 means exponent one and includes
A/I; no level is lost. Zero K, empty schemes, identity edges/squares, the zero
ring, and zero/unit ideals whenever they satisfy the datum remain allowed.
Only the witnesses are individually bounded below; K itself is unbounded and
the witnesses' bounds may vary arbitrarily. No characteristic or nonemptiness
assumption is added. Schemes use t, the small site's objects t+1 and morphisms t,
and coefficients/module values t+1. No equality identifies the two site
universes, and no test-object quantifier is confined to a smaller universe.

Fresh searches, using different wording from the worker:

- `msearch.py leanfinder` with “Whiskering a module inverse image adjunction by a
  diagram category and deriving its base change mate commutes with restriction
  of coefficient rings” returned eight generic ModuleCat extension/restriction
  adjunction declarations, none the strict normalization.
- `msearch.py loogle 'CategoryTheory.Adjunction.whiskerRight'` returned the
  generic termwise adjunction, which is reused by the delivery.
- `msearch.py grep 'Functor.*(rightDerivedFunctor|mapDerivedCategory)|mateEquiv'
  CategoryTheory/Adjunction` returned the generic mate constructor and equations,
  not this theorem.
- Direct `rg` on Mathlib, upstream WeilConjectures and shared `lean/Sheaf` for
  strict/tower mate and exchange, restriction/direct-image and the declaration
  names found generic tools and the published prerequisites. No exact theorem
  or existing complete ringed strict-tower square was found. DAG searches found
  this item's broader prerequisites and its citers, not a replacement notion.
  I distinguished the published completed tower operations (reused) from the
  arbitrary-ring constant specialization newly packaged here.

H5/H6/H8/H9 check: all ten postponed theorems have named statements, source and
owner blueprint docstrings; the main statement carries all six DAG proof steps.
Every theorem proof remains `sorry`. Definitions either use actual functor,
module, adjunction and mate data or uniquely characterized comparison data.
There is no data-valued sorry, axiom, private definition, file-local notation or
local instance. Both node lean.statement strings occur verbatim as their file's
signature, and no Lean line exceeds 100 characters. Explicit section variables
and `autoImplicit false` bind all objects and the universe. No statement_change
is present or needed, so no citer correction audit is triggered.

Mismatches found and changes: none in the repaired Lean statements or definitions.
This second reading changes only this report; the first worker's explicit strict
lift, finite witness comparisons and strict mate equality are preserved.

Fresh verification: the prescribed `scompile.py Q13
lem-weil-pbc-strict-tower-exchange-mate-normalization` compiled both delivered
siblings separately against its current overlay. It exited 0 with no errors or
warnings. Library passes were 16.6 seconds for StrictTowerOperations and
20.3 seconds for StrictTowerExchangeMateNormalization, within the unchanged
60-second per-file limit. The extra wrapper sandbox passes also succeeded.
