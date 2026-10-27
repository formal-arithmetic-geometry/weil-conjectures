## Worker report

Item: lem-sp-semilinear-compactified-graph-evaluation. The module is
Sheaf.Paper.SemilinearCompactifiedGraphEvaluation. Its final theorem asserts
Nonempty (CompactifiedGraphEvaluation C τ e c). The structure records the
specified graph maps, their section formulas, their localized transformations,
and equality after evaluation. sumExtension_exact records the exactness clause.
All postponed proofs are named theorems with source and proof docstrings; no
construction has sorry as data. Helper declarations are listed in lean.declarations
and belong to this graph construction, rather than introducing a second library
notion of semilinear systems or derived categories.

Hypotheses and clauses, in the order of the node:

* Schemes U,T are Scheme.{u}. The morphism e has Etale, IsSeparated,
  LocallyOfFiniteType and QuasiCompact instances; the last two express finite
  type in the recorded interface. c : Compactification e supplies c.i, c.g,
  their composition equation, an open immersion and properness. The open is
  quasi-compact: it is a morphism over T between quasi-compact U/T and separated
  c.Z/T. This is a consequence of the hypotheses, not an additional assumption.
* C : ℕ → CommRingCat.{u+1} and τ : ∀ n, C (n+1) ⟶ C n are arbitrary.
  Index zero denotes the paper's first ring. No Flat, tensor-exactness,
  finiteness, nonzero-ring or bounded-complex hypothesis occurs.
* SemilinearProperOpen.Modules C τ X is the dependency's actual Systems
  category over the vertical sequence site with its constant coefficient
  sheaves. Thus its morphisms already commute with horizontal semilinear
  transitions. Its derived category is the ordinary DerivedCategory, and
  CochainComplex ... ℤ is unbounded.
* inclusion and restriction express composition from U.ProEt into T.ProEt
  at every index. restrictionRing is uniquely normalized on constant sections.
  sumExtension is the left adjoint of this specific restriction, with its
  actual adjunction unit sumAdjunction. Weakly-etale slice localization and
  localizedSystemExtension identify this universal construction with the
  dependency's sheafified direct sum over lifts, including its summand
  insertions. This uses the adjoint universal property determining the
  functor with unit up to unique isomorphism, not an unspecified existence
  choice. sumExtension_exact supplies additivity and preservation of finite
  limits and finite colimits, i.e. exactness in the abelian module categories.
* IsGraphMap quantifies n and b : U.ProEt. Such b is exactly a pro-etale
  test object V/T together with a lift V→U: cancellation of weak etaleness
  gives V/U in the reverse direction. Its γ has both pullback projection
  equations, so it is the specified graph, not any clopen embedding.
  IsOpenImmersion γ.left and IsClosedImmersion γ.left express clopenness.
* GraphValue says the restriction of the section along γ is the image of m
  under the actual open-extension unit (transported to literal restriction),
  and its restriction to every open representing the complementary range is
  zero. IsGraphMap requires ∃! such section, and requires G on each lift-unit
  generator to have this value. Thus uniqueness is uniqueness among all zero
  extensions, not merely uniqueness of a section already equal to G(m).
* CompactifiedGraphEvaluation.graph is a natural transformation
  sumExtension → extension ⋙ push. Its components are morphisms of module
  sheaves on the sequence site. Linearity, pro-etale restriction compatibility,
  transition compatibility and naturality in M are therefore part of its type.
  The generator normalization specifies the sum followed by sheafification.
* theta is a natural transformation from the exact localized sum to J ⋙ R.
  theta_complex specifies its value on QK as Q(G) followed by the canonical
  right-derived comparison, with the exact-localization factor isomorphisms.
  semilinearGraphDerivedComparison is defined from rightDerivedFunctorUnit
  and quotientCompQhIso, with actual data; it is not an arbitrary map.
* levelGraph and level_value repeat the same construction with the individual
  ring C n on StrictTower.Modules. sumEvaluation and openEvaluation are
  uniquely normalized on the actual lift and open-unit generators;
  pushEvaluation is identity on every direct-image section.
  graph_evaluation is equality of natural transformations under these maps.
* levelTheta and level_theta_complex specify precisely gamma_n Q(G_n).
  derivedSumEvaluation and derivedOpenEvaluation localize the ordinary
  comparisons with mapDerivedCategoryCompIso. pushEvaluationDerived is the
  simultaneous-operation comparison; comparison_normalization forces its
  compatibility with the canonical right-derived unit on every complex.
  theta_evaluation is equality of natural transformations on the ordinary
  derived category of the actual systems, with these explicit isomorphisms.
  It is not a statement solely on cohomology or individual objects, and does
  not assume faithfulness of derived evaluation.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom;
  Morphisms.Proper: IsProper, IsSeparated; OpenImmersion: IsOpenImmersion;
  Morphisms.Etale: Etale; Morphisms.FiniteType: LocallyOfFiniteType;
  Morphisms.QuasiCompact: QuasiCompact; Limits.Shapes.Pullback.HasPullback:
  pullback, pullback.fst, pullback.snd. Compactification.Defs supplies the
  recorded compactification's existing open/proper factorization data.
* Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology;
  CategoryTheory.Sites.ConstantSheaf: constantSheaf, toSheafify;
  Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: SheafOfModules.restrictScalars;
  Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules (the existing
  SheafOfModules category, no new carrier).
* WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf:
  SheafOfModules.extensionByZeroPresheaf; Sheaf.CategoryTheory.
  LocalizedModuleExactForSystems: localizedSystemExtension,
  localizedSystemRestriction, localizedSystemExact, localizedSystemAdjunction.
* Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization:
  Scheme.ProEt.weaklyEtale_localization and sliceEquiv, including constant-ring
  normalization. This gives the direct-sum interpretation of the adjoint.
* Sheaf.Paper.SemilinearDerivedSections: SemilinearSections.
  semilinearDerivedSections, Systems, evaluation, evaluationAdditive,
  evaluationLimits, evaluationColimits. The small site has object universe u+1
  and morphism universe u; these are retained separately.
* Sheaf.SixFunctors.SemilinearProperOpenMatePasting:
  SemilinearProperOpen.coefficients, transition, ringSystem, Modules, push,
  pull, ordinaryAdj, extension, ordinaryOpenAdj, J, R and their existing
  exactness and derived-category instances. No theorem asserting proper-open
  pasting is used to define this graph map.
* Sheaf.AlgebraicGeometry.StrictConstantTowerOperations and
  StrictTowerOpenExtension: StrictTower.Modules, coefficients,
  constantRingIso, modulePullback, moduleDirectImage, moduleJ, moduleJAdj
  and their exactness instances. These provide the actual single-ring
  categories and operations; the finite-coefficient ModuleCat-valued graph
  interface is not substituted for them.
* Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, DerivedCategory.Q; HomologicalComplex: CochainComplex;
  exact functor localization mapDerivedCategory and mapDerivedCategoryFactors;
  upstream rightDerivedFunctor, rightDerivedFunctorUnit.
* Proof imports include UnramifiedMorphism, ProEtaleIntrinsicOpenUnit,
  ProEtaleClopenRingedModuleGluing (clopen_ringed_module_gluing),
  RightDerivedFunctorOfQuasiIsoResolutions, ExactSquareDerivedCounit
  (exactSquare_derived_counit), and upstream KInjectiveResolution. The proof
  uses the general clopen gluing and unit normalization; it does not infer
  an arbitrary-coefficient claim from a finite-coefficient specialization.

Sources checked: Stacks etale-cohomology.tex, Tag 0F4L,
lemma-shriek-into-star-separated-etale, including its graph section proof;
current literature/blueprint/latest, det-sp-tower-gluing, Local pairs and
Levels, both statement and proof. The module's eight-step proof docstring
follows these sources, especially the derived-counit transpose argument.

Edge cases checked mathematically before finalizing: empty U and empty V;
no lifts (empty direct sum is zero); several intersecting lifts (no disjointness
of different graphs is assumed); zero rings and zero sections; identity open,
identity proper and identity e; arbitrary nonflat transitions, for example
ℤ/4→ℤ/2; arbitrary negative and positive complex degrees. Complementary opens
are handled by clopen gluing, and γ's projections determine the graph even
in the empty case. There is no flatness or finite-fibre assumption.

Searches for existing statements (2026-10-24):

* msearch.py leanfinder, query "Compactified clopen graph extension of sections
  induces a natural map on semilinear proetale module systems compatible with
  derived evaluation": eight generic smooth-sheaf/module/profinite/completion
  results, none matching this statement.
* msearch.py loogle, query "SheafOfModules.extensionByZeroPresheaf, NatTrans":
  no results (the custom upstream identifier is not indexed by Loogle).
* msearch.py grep, query "semilinear.*graph|graph.*extensionByZero|compactifiedGraph":
  no Mathlib matches.
* msearch.py leansearch, query "Graph extension by zero along a compactification
  gives a natural map on derived semilinear module systems": eight generic
  extension-by-zero results, none matching the graph and evaluation statement.
* rg searches in lean/WeilConjectures and lean/Sheaf for semilinear/graph,
  compactifiedGraph and extensionByZero; node-id search in WeilConjectures;
  DAG/upstream-name search. EtaleProEtaleGraphSheafSquare was read: it is a
  single-ring interface requiring Finite A in a ModuleCat-valued presentation.
  It does not state the arbitrary-ring semilinear derived equality here.
  The existing operations and direct-sum dependencies are reused as above.

No statement correction, disputed assertion, new DAG node or dependency-record
repair is proposed. Helpers are normalizations and specifications of this
node's maps, all carrying this node's blueprint identifier.

## Second reading by Q118

The dispatcher explicitly forbids starting other agents. This is a second
pass by the same worker, not a claim of an independent second worker; the
maintainer performs the independent delivery review.

Read the node and source against the full signature again. Corrected an early
normalization that would have asserted equality of carriers for a chosen
inverse-image adjoint: the final openRestriction_existsUnique and its level
version instead normalize the actual adjunction unit by the pullback projection.
Corrected uniqueness of the level graph section to ∃! over all sections
satisfying LevelGraphValue, separately asserting that G has that value.
Checked all functor directions: Lean's extension ⋙ push is p_*j_!, J ⋙ R is
Rp_*j_!, and every final equation has source the ordinary derived systems.
Checked that evaluation uses SemilinearSections.evaluation on the recorded
constant-ring Systems, not an auxiliary derived tower category. The comparison
normalization uses the right-derived unit itself; no faithfulness or flatness
shortcut occurs. Definitions choose only universal adjoints or uniquely
normalized isomorphisms. No target or existing node statement is changed.
