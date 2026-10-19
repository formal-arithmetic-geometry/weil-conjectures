## Worker report

Repaired the returned head c6fd9b4cbd19, retaining the item's module and its
published pro-etale constructions. The saved packet first failed deliver2.py
--no-push because ProEtaleOpenRestrictionData.lean had no owning node. Its helpers
now belong to the item's single module; the duplicate test module is excluded.
Compared the saved node with current main: only lean differed. The delivered node
is current main with lean updated; statement, dependencies and proof are unchanged.

The module states the node, with one postponed theorem and real helper data, in
namespace AlgebraicGeometry.Scheme.ProEtaleOpenRestriction. The hypotheses and
clauses match as follows.

- Schemes and arrows: {X Y W : Scheme.{u}}, f : X ⟶ Y, h : W ⟶ Y.
  [IsOpenImmersion h] is precisely the open-immersion hypothesis. The fibre
  product and projections are pullback f h, pullback.fst f h and pullback.snd f h.
- Arbitrary commutative ring sheaf: R : Sheaf (ProEt.topology Y)
  CommRingCat.{u + 1}. RX f R, RW h R and RXW f h R are actual sheaf inverse
  images, not independent ring parameters or constant rings. The original
  ProEt sites retain object universe u+1 and Hom universe u.
- Coefficient identification: coefficientIso f h R is a constructed isomorphism
  f_W^{-1} R_W ≅ g^{-1} R_X. squareSiteIso uses Over.pullbackComp and the
  cartesian-square equation, so preserves the projections. ringSquareIso is its
  adjunction mate using the actual ring-sheaf adjunctions; coefficientIso is its
  inverse at R. Thus no coefficient comparison is supplied arbitrarily.
- Module sheaves and adjunctions: ModX, Left, Right, AlphaL, AlphaR, PFst, PSnd,
  PH, AdjF and AdjSnd abbreviate the existing proEtaleRingModules,
  proEtaleRingModulePullback, proEtaleRingModuleDirectImage and tensor-unit-
  normalized proEtaleRingModuleAdjunction. Their coefficient maps are identities
  except the specified coefficientIso for f_W. No new module category is defined.
- Canonical natural isomorphism for every M: beta has type Left f h R ≅
  Right f h R (coefficientIso f h R); it is an isomorphism of functors on the
  whole module category, including naturality and module linearity.
- Sectionwise characterization: objectComposition h composes E→W with h.
  objectCoprojection h R M E is the module adjunction unit at E→Y followed by
  restriction along the distinguished index arrow (id,str). Sectionwise asserts
  that these fixed maps are bijective for h and g, for all module sheaves and all
  objects. Its final equation, for every M, E and input section s, says that
  beta_E of the h coprojection of s equals the g coprojection of
  M.val.map (sectionArrow f h E).op s. sectionArrow is the pullback.map with
  identity on E and the first projection X_W→X. Its source is E×_W X_W over X
  and target E×_Y X over X. Hence, under the specified open identifications,
  beta is exactly the fibre-product restriction map. No section equivalence is
  existentially chosen to fit beta.
- Canonical inverse-image comparison alpha: the existential alpha has type
  AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R). AlphaNormalization
  requires the two iterated adjunction units to agree under alpha and
  squareSiteIso, for every module F, test object V and section m. This is the
  unit-compatible comparison of the node's composition dependency, which
  uniquely specifies alpha, rather than allowing an arbitrary automorphism.
- Counit equation: CounitEquation is equality of actual module morphisms on
  X_W for every M. Its left side is PFst.map (AdjF.counit.app M). Its right side
  is alpha at f_*M, followed by PSnd.map (beta.hom.app M), followed by the
  AdjSnd counit at PFst.obj M. This is exactly the displayed node equation,
  in Lean's left-to-right composition order. The erroneous extra PH.map in
  the saved right composite has been removed.
- No Noetherian, quasi-compact, proper, closed-immersion, constant-coefficient,
  finiteness or nonempty assumption is introduced.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, its two
  projections and pullback.map; Mathlib.AlgebraicGeometry.Sites.Proetale:
  Scheme.ProEt and ProEt.topology.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  exactly Mathlib's SheafOfModules on a general ringed site.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: proEtaleBaseChange,
  proEtaleSheafInverseImage, proEtaleSheafDirectImage, proEtaleSheafAdjunction
  and proEtaleModuleInverseImage. The source spells out the original sites and
  their AsSmall transport; the actual inverse image is Kan extension followed
  by sheafification. Its constant-module direct image is the proof dependency's
  recorded declaration; the arbitrary-ring direct image used here is the
  already published proEtaleRingModuleDirectImage in ProEtaleOperations.
- Sheaf.AlgebraicGeometry.ProEtaleOperations and
  Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction: the actual
  module categories, tensor pullbacks, direct images and uniquely normalized
  adjunction listed above. The adjunction is chosen from its unique normalized
  Hom equivalence, not from a bare Nonempty assertion.
- Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction:
  proEtaleObjectInverseImageRestriction and its distinguished coprojection
  description. Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison:
  proEtale_ringed_open_comparison. Read the latter through scompile.py --source
  because its recorded file was absent in the shared checkout.
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction:
  SheafOfModules.module_pullback_pushforward_adjunction (general adjunction);
  Sheaf.CategoryTheory.SiteMorphismComposition: siteMorphism_composition,
  whose unique unit-compatible composition is rendered by AlphaNormalization.
  Both are proof imports, using the published specialized module constructions
  for the actual small sites rather than imposing equal object/Hom universes.
- Mathlib.CategoryTheory.Sites.Pullback:
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous;
  Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf;
  Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion: stability under base change.
  These are the remaining proof dependencies, also imported explicitly.

Source reading: Stacks proetale.tex, section-morphism (09A5); sites.tex,
localization and composition; sites-modules.tex,
lemma-localize-morphism-ringed-sites (04J0). That lemma fixes the localized
coefficient map using inverse-image composition, and states
f'_* j_U^{-1} = j_V^{-1} f_*. The theorem docstring gives all three DAG proof
steps: site/coefficient setup and unit normalization; sectionwise construction;
then the counit computation on generating coprojections of the sheafified Kan
extension. Every helper has its source and blueprint docstring (H8).

Searches: msearch.py Q18 lem-sfb-proetale-open-restriction-counit leanfinder
"pro-etale open restriction and direct-image counit" returned eight generic
Zariski restriction results, including Modules.restrictAdjunction_counit_app_app.
The loogle query "SheafOfModules.pushforward, SheafOfModules.pullback" returned
12 generic module pullback, composition and adjunction results. The grep query
"open restriction|proEtale.*InverseImage|counit" in
Algebra/Category/ModuleCat/Sheaf returned eight generic counit/adjunction hits.
Read these APIs; none is this arbitrary-ring pro-etale square statement. rg of
"proEtale.*[Oo]pen|open.*[Cc]ounit" in WeilConjectures and lean/Sheaf located
constant/finite-coefficient, etale, derived and Zariski variants; none supplied
this declaration. grep of the exact node id in upstream WeilConjectures found
no declaration. No notion is duplicated: the helper abbreviations merely name
composites and the proposition definitions spell out this node's clauses.

Edge checks: f=id, h=id (the full open), W empty, and W disjoint from the image
of f. The fibre-product maps and unit normalizations remain canonical in all
four cases; no inverse or division of a section, nonempty indexing hypothesis,
or omitted identity case occurs. Zero modules and the zero ring sheaf are also
allowed; the section coprojections then have their usual singleton behavior.

## Second reading by Q18

Self-check with the current DAG statement and the final Lean file open (the
maintainer supplies the independent review). H3 is repaired beyond the saved
packet: the coefficient comparison is a fixed constructed mate; the section map
is fixed by pullback.map, not an existential component; alpha is constrained by
both iterated units; the counit equation is the full morphism equality. The old
Sectionwise merely reasserted bijectivity of beta's own components and therefore
failed to express the node's fibre-product formula. The repaired definition
instead has the explicit equation on s in M(E×_Y X), under fixed coprojections.
The right counit term must apply PSnd directly to beta, since beta is already a
map on W; the saved additional PH was ill-typed and is corrected.

Read the binders again against the node: the only hypotheses are f, the open h,
and arbitrary R. g and f_W are the specified projections; the coefficient ring
on X_W is g^{-1}f^{-1}R, transported to the other route by the fixed comparison.
Read each conclusion again: beta is natural in M; Sectionwise covers every E→W
and every s; AlphaNormalization covers every F,V,m and fixes canonical alpha;
CounitEquation covers every M and composes the three arrows in the stated order.
All data definitions contain actual terms. There is precisely one postponed
statement, proEtaleOpenRestrictionCounit, whose proof is sorry with its complete
three-step source proof docstring. No statement correction or new node is needed.

The final docstring reading also corrected the saved proof's claimed isomorphism
X_W ×_W (W ×_Y V) ≅ X ×_Y V: generally it is only over the open W. The proof now
uses X_W ×_W E ≅ X ×_Y E followed by the projection to X ×_Y V, exactly as the
DAG proof does; equality is checked on generators on X_W, not at objects of W.
The required dry run passed preflight and compilation (17e21e5fdf). The delivery
wrapper recompiles this final packet before pushing, including the documentation
and report refinements made during the self-check.
