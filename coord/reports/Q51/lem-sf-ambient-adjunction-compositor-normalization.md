## Worker report

The module Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization states
WeilConjectures.AmbientCompositor.ambientAdjunctionCompositorNormalization.
Its only postponed proof is this theorem. All definitions have real data. The
Operations record packages existing functors, categories and adjunctions; the theorem
is about its two concrete published realizations, not an arbitrary supplied calculus.
The natural-language statement, proof and proof dependencies are unchanged.

Source reading: sites-cohomology.tex, lemma-derived-pushforward-composition (0D6E),
lines 4010–4030, derives composition from inverse-image composition and uniqueness
of adjoints. derived.tex, lemma-derived-adjoint-functors (09T5), lines 9594 onward,
provides the specified derived adjunction. The following definition-K-injective and
lemma-K-injective give the null-homotopy and resolution interpretation. The node's
seven proof steps are reproduced in the theorem docstring, including its extra
normalization and coherence requirements. This is a new statement, not a proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed algebraic closure of a finite field is F : FiniteFieldDatum; l is prime
  through Fact l.Prime, and _hl : l ≠ F.p supplies the different-characteristic
  convention. E, Field E, Algebra (Padic l) E and FiniteDimensional (Padic l) E
  give the finite coefficient extension. coefficientExtensionRing uses the existing
  valuation ring and chosen uniformizer, not a new DVR or quotient convention.
- FiniteTypeOver F X unfolds to a structure morphism X → Spec F.k with
  LocallyOfFiniteType and QuasiCompact. Every scheme occurring in Laws,
  FiniteSections and SystemSections has this explicit hypothesis. No separatedness
  of a structure morphism is imposed; the constructions themselves work more widely.
- The finite clause quantifies over n : ℕ and uses A_(n+1), covering exactly all
  positive levels. Its Finite instance is finite_coefficientExtensionRing at n+1.
  The system clause uses coefficientTower and coefficientTransition, consisting of
  the same positive quotient rings (with their standard ULift) and quotient maps.
- finite.M is proEtaleRingModules on Scheme.ProEt with its topology and actual
  proEtaleConstantRing. systems.M is SemilinearProperOpen.Modules, definitionally
  the published SemilinearSections.Systems over systemRing on the vertical sequence
  site. Its module structure includes semilinear transitions and compatible module
  morphisms; it is not a diagram of derived objects.
- Operations.D is DerivedCategory, the ordinary unbounded localization. Operations.P
  is exact mapDerivedCategory of the recorded inverse image. Operations.S is the
  total rightDerivedFunctor of the actual ordinary push. Operations.J is exact
  mapDerivedCategory of the actual extension by zero. Operations.adjunction is
  mapDerivedCategoryRightDerivedAdjunction of the specified ordinary adjunction;
  openAdjunction is exactDerivedAdjunction of the specified ordinary open adjunction.
- finite uses sfIntrinsicPullback and sfIntrinsicConstantModuleAdjunction from the
  published realization. The finite ordinary compositor is sfIntrinsicPullbackComp,
  and its localization defines d. The unused finiteTensorIdentification abbreviation
  is removed in this repair, as the return requests; no conclusion referenced it.
- The inverse tensor compositor d is localization of pullComp.symm with the canonical
  mapDerivedCategoryCompIso inserted. For finite coefficients pullComp is the
  published sfIntrinsicPullbackComp; for systems it is the published pullComp,
  conjugate to the unique fibre-product section restriction. The tensor/unit theorem
  and constant-ring composition theorem identify these with the node's tensor formula.
- c is literally the inverse of conjugateIsoEquiv applied to d under the specified
  composite and single-map adjunctions. e is literally leftAdjointCompIso for the
  two specified open adjunctions with right comparison d. These definitions supply
  natural isomorphisms, so naturality is part of their types, on all derived arrows.
- Laws.direct and Laws.openExtension are Normalized records. Normalized.unit states
  η_comp followed by the left and right comparisons equals η_single;
  Normalized.counit states the transported single counit equals ε_comp;
  Normalized.hom states the same comparison on every specified Hom bijection.
- Laws.kinjective states K-injectivity of f_*I and g_*f_*I, and the actual equation
  between Q of the ordinary comparison followed by the single right-derived unit,
  and the successive right-derived units followed by c. The homotopy functor
  composition comparison is retained explicitly. This expresses agreement on
  K-injective resolutions, not a free isomorphism of cohomology objects.
- FiniteSections specifies ordinaryC on every section by restriction along
  MorphismProperty.Over.pullbackComp.hom. SystemSections equates ordinaryC with
  the already published unique section-normalized SemilinearProperOpen.pushComp
  on the whole ringed sequence site. These clauses fix the ordinary comparison
  appearing in Laws.kinjective.
- Laws.localizedOpen identifies e with mapDerivedCategoryNatIso of ordinaryE, after
  the exact derived composition comparison. ordinaryE is the unique open left-adjoint
  comparison corresponding to pullComp.symm under the actual ordinary adjunctions.
- Laws.s_assoc and Laws.j_assoc are the two displayed threefold compositor equations.
  Congruence isomorphisms for Category.assoc remain in the equations. Components
  express whiskering and functor associators without assuming equality of functors.
- Laws.s_unit and Laws.j_unit each assert both identity equations. sId and jId are
  obtained from pId using the specified adjunctions; pId is exact localization of
  the actual unit-normalized ordinary identity comparison.
- Laws.threefold and Laws.threefoldRight explicitly express the single-map Hom
  bijection as the three successive specified pull/direct Hom bijections, with the
  two parenthesized comparison composites. Laws.threefoldOpen and
  Laws.threefoldOpenRight do the same for the open adjunctions. Associativity fields
  identify the transports, so both parenthesizations agree.
- The entire Laws and SystemSections assertions hold for systems itself. No finite
  evaluation, scalar restriction or total limit occurs in their construction or
  conclusion, and no evaluated K-injectivity assertion is made.

Dependencies inspected and used:

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing, coefficientExtensionRing and
  coefficientExtensionTransition (positive coefficient rings and transitions).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
  The morphism-properties dependency is a convention with no declaration; the
  relevant Mathlib properties are LocallyOfFiniteType, QuasiCompact, IsOpenImmersion.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently used by proEtaleRingModules and the system modules.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory and HasDerivedCategory.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
  proEtaleConstantRingDerivedPullback and ordinary constant-ring operations; the
  canonical tensor-module adjunction and derived adjunction are publicly exported.
- Sheaf.Paper.SemilinearDerivedSections: SemilinearDerivedSectionsData and its
  geometric and localization interfaces; the actual Systems and ringed sequence
  realization and published exact derived adjunction are used by systems.
- Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit:
  proEtale_tensor_composition_unit (full local generator, inverse-generator, section
  comparison, composite-unit and uniqueness clauses read).
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition:
  proEtaleCoefficientInverseImageMap_comp (canonical coefficient composition).
- Mathlib.CategoryTheory.Adjunction.Mates: conjugateEquiv, conjugateIsoEquiv and their
  actual orientations; Mathlib.CategoryTheory.Adjunction.Basic: Adjunction.comp,
  comp_unit_app, comp_counit_app and comp_homEquiv.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: restrictScalars, the
  section-preserving scalar restriction used in the recorded semilinear module model.
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems:
  localizedSystemExtension, localizedSystemRestriction, localizedSystemExact and
  localizedSystemAdjunction (the direct-sum/sheafification construction and its
  independent universe exactness and normalization).
-def-sp-semilinear-constant-ring-operations, recorded in
  Sheaf.SixFunctors.SemilinearProperOpenMatePasting, owns Modules, pull, push,
  extension, ordinaryAdj and ordinaryOpenAdj. The already-landed existing:true
 def-sf-semilinear-proper-open-comparisons owns pushComp_existsUnique, pushComp,
  pullComp and pushId_existsUnique in that same module. These definition owners
  replace the theorem lem-sf-semilinear-proper-open-mate-pasting in stmt_deps.
  The unused open-square identification, its import and lem-trf-open-square-exchange
  stmt_dep are removed. def-weil-proetale-inverse-image owns the intrinsic finite
  realization; def-weil-finite-field-fiber owns FiniteFieldDatum. The ordinary
  system functors and the four comparison declarations were reread with their
  full signatures and docstrings. No theorem conclusion is used as definition data.
- All currently stated proof dependencies are imported privately, including diagram
  site realization, general pre-derived adjunction, K-injective total derivation,
  resolving normalization, ringed-topos composition, and open site localization.
  Mathlib imports exposed through these modules provide exact-functor localization,
  conjugate unit equations, natural Hom bijection recovery and mate-pasting.

Edge cases checked: n=0 indexes A₁ and never asks for finiteness of A₀; all positive
levels are retained. Empty schemes and the empty open are allowed. Identity scheme
maps are allowed, and both sides of each identity law are typed with the same
canonical transports. Non-separated finite-type structure maps are retained. There
is no boundedness, constructibility, normalized-system or cartesian-system condition
on the input complex. The system quotient transitions are not assumed flat. The
pro-etale site retains objects in u+1 and morphisms in u; module coefficients are in
u+1 and derived localization in u+2. No universe equality is imposed.

Searches actually run (recorded by msearch.py):

- LeanFinder: "Derived direct image composition is the inverse adjunction conjugate
  of inverse image composition, preserving units counits and associativity" returned
  eight generic derived-adjunction results, including Adjunction.derived and unit
  factorization lemmas; none states the geometric and system normalization package.
- Loogle: "CategoryTheory.conjugateIsoEquiv, CategoryTheory.Adjunction.comp" returned
  no hits for that combined query. Direct Mathlib reading found both generic tools.
- grep: "conjugateIsoEquiv|comp_homEquiv|rightAdjointCompIso" in
  CategoryTheory/Adjunction returned 15 hits including Mates.lean:425,
  Basic.lean:584 and CompositionIso.lean. They supply generic constructions only.
- LeanSearch: "The conjugate composition isomorphism of right derived functors equals
  the composition comparison on K injective complexes" returned eight generic
  right-derived-functor and injective-resolution results, no exact complete match.
- rg and grep of WeilConjectures and Sheaf by item id, ambient/compositor,
  composition, adjunction and intrinsic-operation names found no exact statement.
  AmbientProperOpenPasting gives composition laws with extra pasting claims but
  does not assert this item's resolution formula and all specified Hom normalizations.
  CompositionAdjunctionNormalization gives the generic binary normalization but
  not the open/system realization and full threefold coherence. The final module
  reuses their underlying published operations and the dependency proof route.

No statement dispute, correction, new DAG definition node, dependency repair, or
change to the accepted split is needed. The helper records and predicates only package
this node's comparisons and equations, as permitted by the launcher helper rule.

## Second reading by Q51

This is a direct clause-by-clause self-check with the node and Lean file open, not
an independent worker reading; the dispatcher prohibits starting another agent.
The maintainer supplies the independent reading. I checked the following clauses:

- Base and coefficients: the node fixes an algebraic closure of a finite field and
  a different prime, rendered by FiniteFieldDatum, Fact l.Prime and l ≠ F.p.
  Field E, Algebra (Padic l) E and FiniteDimensional (Padic l) E give exactly the
  stated finite extension. coefficientTower starts at n+1, hence includes A₁ and
  every positive level; coefficientTransition uses the actual quotient maps.
- Scheme convention: FiniteTypeOver is existence of a locally finite type,
  quasi-compact structure map to Spec F.k. All scheme binders in Laws,
  FiniteSections and SystemSections have this hypothesis, with no separatedness.
- Categories: finite.M is modules over the actual constant ring sheaf on the small
  pro-etale site; systems.M is Modules C τ, the simultaneous semilinear module
  category. Operations.D is the ordinary unbounded DerivedCategory in both cases.
  No Cartesian-system, normalization, flat-transition or boundedness hypothesis occurs.
- Functors and specified adjunctions: P and J are exact localizations of the
  published ordinary inverse image and open extension. S is ordinary push's total
  right derived functor. adjunction and openAdjunction localize the given ordinary
  adjunctions; they do not choose new adjunctions on abstract functors.
- Tensor compositor and inverse conjugates: d localizes pullComp.symm, with the
  canonical localization composition comparison. finite.pullComp is
  sfIntrinsicPullbackComp; systems.pullComp is the existing ordinary adjoint
  comparison of section-normalized pushComp. c is the inverse conjugate of d;
  e is its open left-adjoint comparison. Their source/target orientations match
  the node's P_u P_v, S_v S_u and J_b J_j.
- Both units and counits: Laws.direct and Laws.openExtension each assert Normalized;
  its unit, counit and hom fields give the corresponding equations for every object
  and every Hom arrow. Naturality comes from the natural-isomorphism types of c,e.
- Resolution normalization: Laws.kinjective retains K-injectivity of f_*I and
  g_*f_*I and the equation involving the two derived-functor units, Qh of ordinaryC,
  the homotopy composition comparison and c. FiniteSections pins ordinaryC on each
  test section; SystemSections pins it to the unique section-normalized pushComp.
  These use the full diagram category, without evaluating derived resolutions.
- Open localization: Laws.localizedOpen equates e with localization of ordinaryE
  after the canonical exact-composition isomorphism, in both realizations.
- Associativity: Laws.s_assoc and Laws.j_assoc render each displayed equation,
  retaining equality transports for Category.assoc. Their order agrees with
  postcomposition and the stated whiskerings.
- Units: Laws.s_unit and Laws.j_unit each include both identity composites, with
  identity/comp equality transports. sId and jId come from pId and the specified
  adjunctions. systems.pullId uses pushId_existsUnique.choose, where uniqueness
  pins all sections; this is not a choice from unspecified mere existence.
- Threefold Hom: Laws.threefold and Laws.threefoldRight retain both direct-image
  parenthesizations; Laws.threefoldOpen and Laws.threefoldOpenRight retain both
  open-extension parenthesizations. Each uses three actual specified Hom bijections,
  with d,c,e in the needed source and target transports. The associativity clauses
  identify the two transports.
- Scope: the final theorem asserts Laws and the section pin separately for every
  positive finite coefficient level and for systems on the ringed diagram category.
  No finite evaluation, scalar restriction or total limit is used to infer them.

The H2 mismatch found is ownership of definitions by theorem stmt_deps. The repair
cites the existing definition owners and deletes the unused finite tensor comparison.
All mathematical clauses above and the sole postponed theorem proof are unchanged.
The sole sorry remains ambientAdjunctionCompositorNormalization with its seven-step
docstring. Empty schemes/opens, identities, n=0 → A₁, non-separated finite-type
schemes, unbounded complexes and independent site object/morphism universes remain
admitted. No other mismatch was found in this self-check.

## Returned delivery repair

Returned immutable head: 7fcd97076f08. The saved packet initially passed a fresh
--no-push run (32a3236f0a5), but still contained the ownership fault identified by L.

H2: removed lem-sf-semilinear-proper-open-mate-pasting and
lem-trf-open-square-exchange from the added stmt_deps. Added
def-sp-semilinear-constant-ring-operations for the ordinary system operations and
def-sf-semilinear-proper-open-comparisons for pushComp_existsUnique, pushComp,
pullComp and pushId_existsUnique. The latter is already landed as existing:true in
sec-six-functors and lists all four declarations, so creating another node would
violate one definition per notion. Neither theorem conclusion is needed here, so
neither is added to proof_deps. Removed finiteTensorIdentification, its declaration
record and the ProEtaleConstantOpenSquareExchange import. No dependency module,
new node or statement correction is needed. The base node's statement, proof and
proof_deps are preserved verbatim. The current definition ownership records and
published declarations were checked against the saved packet before editing.

H11 advisory: replaced the previous historical self-check paragraph with the explicit
hypothesis/clause comparison above; it remains honestly labelled a self-check.

The first repaired compile exposed a transitive-import dependency:
sfIntrinsicOpenAdjunction and the finite open-extension exactness instances were
previously visible through ProEtaleConstantOpenSquareExchange. Replaced that broad
import with Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange, which defines the
actual ordinary open adjunction and publicly imports the exactness instances.
Cited the already-landed existing:true def-sp-finite-intrinsic-open-square, whose
lean.declarations owns sfIntrinsicOpenAdjunction. Its transported ordinary adjunction
signature and docstring were read, together with sfIntrinsicExtensionByZero_exact.
This introduces no comparison abbreviation or theorem stmt_dep and changes no law.

Validation of the repaired packet: scompile.py succeeded for the sandbox module
(39.8 seconds) and the library module (6.1 seconds), with no diagnostic. The recorded
main signature is verbatim, the module has one sorry and no line over 100 columns.
Only stmt_deps and lean differ from the live item node; the mathematical statement,
proof and proof_deps are unchanged. All three added definition owners have existing:true
records and their combined statement/proof dependency closures do not reach this item.
