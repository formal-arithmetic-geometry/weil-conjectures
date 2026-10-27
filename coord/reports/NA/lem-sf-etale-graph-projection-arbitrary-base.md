## Worker report

Item: lem-sf-etale-graph-projection-arbitrary-base. Group: NA. Stage 2 only.

The delivery states `AlgebraicGeometry.Etale.sfEtaleGraphProjectionArbitraryBase` in
`Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase`. Its sole new theorem
has proof `sorry`. Three helper definitions contain actual composites of existing
canonical isomorphisms or an existing adjunction's inverse Hom equivalence. No new
object, arbitrary comparison map, axiom, or existence choice is introduced. The item
changes only in `lean`; there are no new nodes or dependency repairs.

Source read: current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`, particularly paragraph 3; local Stacks
`more-etale.tex`, Tag 0GKF, `lemma-f-shriek-projection`, lines 1807 onward. The graph
construction was read in upstream `EtaleLowerShriekCompactification.lean`, lines
58–166, and its invertibility theorem/docstring in
`EtaleLowerShriekCompactificationIso.lean`, lines 268–277. The Stacks lemma supplies
the ordinary canonical tensor map; the unbounded graph square is the additional
agent-formulated assertion of the accepted DAG, not falsely attached to that lemma
or to the upstream invertibility theorem alone.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite commutative ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`. No nontriviality assumption. |
| Arbitrary schemes V and W | `{V W : Scheme.{u}}`, with explicitly declared universe `u`. |
| Separated etale morphism e | `(e : V ⟶ W) [Etale e] [IsSeparated e]`. |
| Specified factorization V → Z → W with j open, r proper, rj=e | `(c : Compactification e)`. Read `Compactification/Defs.lean:69`: fields `Z`, `i`, `g`, `comm : e = i ≫ g`, `isProper`, `isOpenImmersion`, and no quasi-compactness field. Set j=c.i and r=c.g. |
| Ordinary unbounded small-etale derived categories | `DerivedCategoryModule A V` and `DerivedCategoryModule A W`, the existing ordinary unbounded categories of ModuleCat-valued sheaves; no constructible or bounded subcategory. |
| F=Rr_*Dj_! | Existing `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`, used by the upstream graph comparison and projection. |
| Specified proper-counit/open-tensor projection P | `sfEtaleExactProjectionIso A c M K`: `asIso` of the exact existing `projectionMapOfCompactification` component, followed by F of tensoring M with the canonical `Le* ≅ D(e*)` comparison. Its inverse, not an arbitrary inverse between endpoints, occurs in the theorem. The existing ambient theorem supplies the `IsIso` proof used by `asIso`. |
| S=D(e_Σ!) | `D(etaleLowerShriek (ModuleCat A) e inferInstance)`, the existing sum extension descended termwise. |
| E=D(e*) and termwise sum/evaluation adjunction, unit v | `D((e)^*[ModuleCat A])` and `derivedEtaleLowerShriekMapAdjunction (ModuleCat A) e`; its actual `.unit.app M` is used in kappa. |
| Canonical strong monoidal E, transported from Le* | `sfEtaleExactPullbackTensorIso A e B K`: E(B tensor K) → L(B tensor K) → LB tensor LK → EB tensor LK → EB tensor EK, built from the existing exact/left-derived comparison and `leftDerivedUpperStarTensorIso`. This is precisely the inverse tensor comparison mu in the node. |
| Canonical unit comparison u_e | The unchanged imported `etaleSumPullbackUnitIso A e`, whose source was read: inverse exact/left-derived comparison at A_W followed by `leftDerivedUpperStarUnitIso`. No unit appears in the claimed square; no additional unit assertion is added. |
| kappa is the unique adjunct of mu^{-1}(v_M tensor 1) | `sfEtaleSumExactTensorMap A e M K`: the inverse `.homEquiv` of the termwise derived sum adjunction applied to `(derivedTensor.map v_M).app EK ≫ (sfEtaleExactPullbackTensorIso ...).inv`. The identity on EK is the unchanged second argument of the bifunctor. |
| B=Z×_W V, q_Z, q and sigma=(j,1) | Existing `c.selfGraph : V ⟶ pullback c.g e` with `pullback.fst` and `pullback.snd`, its upstream identities `selfGraph_fst` and `selfGraph_snd`, and the upstream open/closed-immersion instances. These are reused inside the comparison. |
| t_M is clopen unit, middle identifications, clopen counit | Existing `compactificationEtaleGraphMap`, whose component is `clopenTransfer` of `compactificationEtaleGraphIso`. That iso uses the q-sigma identity, the open adjunction unit, and q_Z-sigma=j. It is the specified transfer. |
| u_M is ordinary adjunction unit, Rq_*t_M, inverse proper exchange | Existing `compactificationEtaleUnit`, read at lines 148–155. The canonical exact/left-derived comparisons identify its derived pullback model with the exact model in the node. No arbitrary map u is assumed. |
| a_M is the sum/evaluation adjunct of u_M | Existing `compactificationEtaleComparison A e c`. The source expands it as S(u), then the counit, with functor unitors/associator. Its adjunction is the termwise sum adjunction transported along the exact/left-derived comparison, hence gives the specified a in either model. |
| a is a natural isomorphism | `IsIso (compactificationEtaleComparison A e c)`. It is already a natural transformation by construction; `IsIso` makes it a natural isomorphism. |
| For every unbounded M,K, P^{-1} ∘ a_{M tensor EK} = (a_M tensor 1) ∘ kappa | The universal quantifiers in the second conjunct; Lean composition is left-to-right: `a.app (M tensor EK) ≫ (sfEtaleExactProjectionIso A c M K).inv = sfEtaleSumExactTensorMap A e M K ≫ ((derivedTensor ... W).map (a.app M)).app K`. Both sides have source S(M tensor EK) and target FM tensor K. |
| No Noetherian, quasi-compactness, constructibility, boundedness hypotheses | The entire theorem binder list is exactly A, its ring/finite instances, V,W,e, its etale/separated instances, and c. There is no implicit free variable (`set_option autoImplicit false`). |

Dependency declarations used or imported, with the recorded interfaces read:

| Statement dependency | Module and declaration |
| --- | --- |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`. |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`; separatedness is `AlgebraicGeometry.IsSeparated` from the imported Separated module. |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`. |
| lem-sf-etale-ambient-adjoint-projection | `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`: `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection`; its second conjunct supplies projection invertibility. |
| def-weil-pbc-etale-sum-extension | `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `AlgebraicGeometry.Etale.etaleLowerShriek`. |
| lem-weil-pbc-etale-restriction-injectives | Same module: `etaleLowerShriekUpperStarAdjunction`, `preservesFiniteLimits_etaleLowerShriek`, `injective_upperStar_obj_of_etale`; the transported derived interface is `derivedEtaleLowerShriekMapAdjunction` in `EtaleLowerShriekBaseChange`. |
| prop-weil-pbc-inverse-image-modules-exact | `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: `AlgebraicGeometry.etaleInverseImageModulesExact`; existing `upperStar` and `leftDerivedUpperStarIsoMapDerivedCategory` supply the specialized exact functor. |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`; specialized existing tensor map is `leftDerivedUpperStarTensorIso` in upstream `UpperStarMonoidal.Comparison`. |
| lem-pur-unit-adjunct-tensor-action | `Sheaf.CategoryTheory.UnitAdjunctTensorAction`: `CategoryTheory.Adjunction.unitAdjunctTensorAction`. The helper uses the very inverse Hom transpose defining that action, without replacing the existing notion. |
| def-kun-unbounded-exchange | `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap` and `exactDerivedSquareUpperStarIso`; upstream graph uses its canonically transported left-derived mate `derivedBaseChangeMap`. |
| lem-kun-proper-base-change-torsion-ring | `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`: the recorded proper torsion exchange interface. The upstream graph module already provides the needed `IsIso` instance for its chosen square. |
| lem-sfb-ringed-derived-monoidal-comparisons | `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`. No arbitrary monoidal structure is assumed in our helpers. |
| def-pur-etale-exact-pullback-unit-composition-comparisons | `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence`: `AlgebraicGeometry.Etale.etaleSumPullbackUnitIso`; `unboundedEtaleUpperStarCompIso` is publicly re-exported from `UnboundedEtaleCompactSupportComparisons`. |

The module also imports every recorded proof-dependency module (Mathlib leaf files
included), with proof-only imports non-public. The theorem docstring carries all
eleven accepted proof steps, including each step's dependency names: graph geometry,
clopen product descent, transfer calculations, open tensor normalization, adjunction
triangle calculation, exchange/projection coherence, transposition of the square,
base-change compatibility, finite geometric fibres, normalized finite-sum evaluation,
and derived conservativity. Nothing in that proof is proved in this delivery.

Edge cases checked before drafting: empty V (both sum extension and compact support
are zero); empty W (then V is empty); zero coefficient ring (no `Nontrivial A`);
identity e and arbitrary open e with r=id, including non-quasi-compact open immersions
(the definition of Compactification explicitly permits these); zero M or K; complexes
unbounded in both directions (no boundedness or Tor-amplitude binder). In the geometric
fibre argument the empty finite index set gives zero on both sides, exactly as in the
node's proof. Scheme and coefficient universes follow the established size convention,
without imposing a further equality or quantifying over too-small test schemes.

Searches actually run using `batch2/msearch.py NA <item>`:

- LeanFinder: `The canonical comparison from etale sum extension to compactification lower shriek is an isomorphism and commutes with the projection formula`. Eight unrelated finite-coproduct/scheme-comparison hits, no match.
- Loogle: `compactificationEtaleComparison`. Zero hits, unknown identifier (the upstream declaration is outside Mathlib's service index).
- Mathlib grep: `compactificationEtaleComparison|etale.*projection` in `AlgebraicGeometry`. Zero hits.
- LeanSearch: `etale compactification graph comparison projection formula tensor compatibility`. Eight unrelated scheme tensor-pullback and ring-etale hits, no graph/projection square.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for `compactificationEtaleComparison|lem-sf-etale-graph-projection-arbitrary-base|ambientAdjointProjection|etaleGraph`: found the upstream construction and invertibility theorem, plus the downstream `SfEtaleUnitTensorArbitraryBase` consumer, which uses this node as a proof input. No existing theorem states both requested clauses.
- Local `rg` for exact tensor transport, sum projection, and tensor-map names located `mapDerivedCategoryUpperStarDerivedTensorIso` in `OpenImmersionLowerShriekProjection`. Its signature requires `[IsOpenImmersion j]` and leaves its second input left-derived, so it is not the general exact tensor comparison for arbitrary etale e. The helper here spells out only canonical transports of the existing tensor iso, with no new independent notion.
- Local name search for `sfEtaleSumExactTensorMap`, `sfEtaleExactProjectionIso`, and `sfEtaleGraphProjectionArbitraryBase` found no declaration in either source tree.

Validation: the initial complete file compiled through the prescribed `scompile.py`
in both sandbox and library contexts, in 3.7 and 3.6 seconds, with no errors or
unexpected warnings. The final import visibility and report/node packet are checked
again by the required delivery dry run.

No STATEMENT-DISPUTED flag, source error, or statement correction is needed.

## Second reading by NA

I reread the finished node and Lean statement, including each helper body. This is a
same-worker second pass; no separate reviewer or sub-agent was started, as the
assignment explicitly forbids starting agents. Independent mathematical review is
performed by the maintainer after delivery.

The coefficient finiteness, commutativity, separatedness and etaleness are explicit;
Compactification carries exactly the supplied open/proper factorization. Its open
factor has no quasi-compactness field. The comparison a is the upstream graph map,
not a chosen iso. Both sides of the equation use exact EK. On the left P is transported
by F(M tensor d_K) before inversion. On the right kappa uses the *exact* sum unit and
the inverse of the canonically transported mu, so its variance agrees with the node's
transpose formula. The map `(derivedTensor.map a_M).app K` is a_M tensor the identity
on K. The upstream use of the left-derived adjunction introduces only its prescribed
canonical transport; it adds no mathematical hypothesis. The first conjunct is
natural-transformation invertibility, not merely existence of some endpoint iso.
The universal second conjunct is precisely the displayed square in the node, with
no added clauses. No mismatch required a statement change. During this pass I made
the direct geometry and sum-extension statement imports public; proof-only imports
remain plain. Definitions have no `sorry`; only the matching theorem is postponed.
