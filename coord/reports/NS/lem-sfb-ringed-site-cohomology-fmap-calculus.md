## Worker report

Stage 2, direct delivery by NS, repairing the H13 return of immutable head 581b11104b4e. The accepted stage-1 statement and proof remain verbatim. No agents were started.

Files: the item node and RingedSiteCohomologyFmapCalculus.lean, plus the existing dependency lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and its owning module ModuleAbelianEvaluationComparison.lean. There are no new DAG nodes. All newly stated theorems have proof sorry. Every published proof in the dependency module is byte-identical to live; the original primary lean binding is retained field for field, with only declarations and note added. The general comparison statement is appended in the same module as the existing proof, so each delivered module has exactly one owning node. All definitions contain actual data or choose from a uniquely characterizing theorem.

The main namespace is CategoryTheory.RingedSiteCohomology. Site bundles a Type u small category, a GrothendieckTopology, a CommRingCat-valued ring sheaf, HasTerminal, and EnoughInjectives for the existing module category. The input does not assume a pretopology, site pullbacks, a morphism of presented sites, flatness, or preservation of module injectives. base forgets commutativity only; Mod is exactly SheafOfModules; sections evaluates its underlying abelian sheaf at the terminal object. H is the rightDerived of this functor, computed in all module sheaves. These are helpers of this node's calculus, not replacement categories or a new cohomology theory.

The adjunction-normalized section identity is sectionsIso. Its characterizing SectionNormalized formula uses the given RingedToposMorphism.underlying and adj.homEquiv on maps from the terminal sheaf. element is the existing Gamma-to-terminal-evaluation and Gamma-to-Hom equivalence. The existential terminal comparison in SectionNormalized is unique because both objects are terminal. Thus an arbitrary automorphism of section cohomology cannot enter this normalization. sections_existsUnique states exactly this uniqueness before sectionsIso selects the comparison.

Clause correspondence:

* Injective-resolution construction, invertibility and independence: RoofNormalized quantifies over every I,J,P,lambda,beta and homotopy-compatible augmentation; QuasiIso of sections(lambda) is a conclusion. map_existsUnique both asserts existence and fixes the map uniquely by all these formulas. map is its unique choice. map_roof states that formula for the selected map. map_roof_int covers an arbitrary integer-indexed bounded-below injective replacement, including replacements not supported in nonnegative degrees. resolutionIso uses the established InjectiveResolution.cochainComplex, mapExtendIso, extendHomologyIso and isoRightDerivedObj, without a freely chosen cohomology identification.
* Additivity and the zero map: map_add_zero gives both equations. Each resulting map already has type Hom in AddCommGrpCat, so is additive on cohomology elements as well.
* Global-scalar linearity: scalar is actual sectionwise multiplication by the restriction of the scalar at the terminal object; map_scalar equates the two derived scalar endomorphisms. Its ringElement equation defines the target scalar by inverse image and the given structural ringMap. It does not assume scalar-linearity of the desired cohomology map. This endomorphism formulation is equivalent to B(global)-linearity, while avoiding extra choices of Module structures on the underlying abelian derived objects.
* Degree zero: map_zero states the commuting equation with the canonical toRightDerivedZero augmentations, i.e. Gamma(phi) under the canonical degree-zero identifications.
* Composition: map_comp quantifies over a third ringed-topos morphism h and its natural direct-image comparison c with f.modules followed by g.modules. The hypothesis pins c to the canonical section identification, as in the node. Its coefficient map uses c.inv and the equation has order map(g) then map(f), which is T_f composed with T_g in ordinary notation.
* Geometric two-isomorphisms: map_twoIso states invariance for every section-preserving direct-image isomorphism, in particular those induced by geometric two-isomorphisms. map_identity applies to a section-preserving presentation of the identity direct image and returns the ordinary derived map. map_natural gives each of the two coefficient naturality equations separately.
* Acyclic resolutions: map_acyclic quantifies over nonnegative K,L, their quasi-isomorphic augmentations and an augmentation-preserving chain map v. Only K and L themselves are required termwise acyclic for their respective section functors. There is no acyclicity or exactness assumption on f_*L. The equation uses precisely rightDerivedObjIsoOfResolution. map_edge specializes to the identity coefficient map when f_*I is a resolution; its comparison orientation is forward to section homology, followed by the section identity, then the inverse target resolution comparison.
* Localization: slice is Over U with J.over U and R.over U, with the enough-injectives assumption already implicit in this clause retained explicitly. restriction is exactly SheafOfModules.overFunctor. restrictSections is the literal presheaf restriction from the global terminal object to the underlying object of the slice's terminal object. map_restriction identifies the unit map with the homology of that chain restriction. restriction_resolution asserts that every restricted injective resolution can itself be taken as the slice injective resolution; hence the comparison c required by the formula always exists and does not restrict its scope to unusually isomorphic resolutions. sliceSectionsIso maps the chosen terminal object in Over U to Over.mk(id U), pinning evaluation to U.
* Ordinary abelian restriction: evaluationComparison selects the unique normalized comparison in the repaired dependency. abRestriction is literal abelian restriction from terminal evaluation to U. restrictionComparison is the concrete comparison through I, L and c, not an unconstrained isomorphism. map_restriction_abelian states the square with evaluationComparison at the terminal object and at U and NatTrans.rightDerived abRestriction. Thus the final compatibility is an actual equality, not a prose promise.

Every theorem docstring records its Stacks source, blueprint id and full local proof argument from the accepted split. The module imports all already stated proof dependencies (and the repaired statement dependency). The global-acyclicity prerequisite currently has no Lean module, so there is no import for it. Nothing is asserted Lean-closed here.

Searches for an existing interface: searched the node's blueprint tag and coefficient-map terminology in lean/WeilConjectures and lean/Sheaf, and read the scheme-only WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap. Its module categories and morphism argument are schemes, so it cannot state this general ringed-topos result. Mathlib search command leansearch, query "Functorial cohomology maps for morphisms of ringed topoi and linear coefficient maps computed by injective resolution roofs", returned injectiveResolutions, Functor.rightDerived_map_eq, InjectiveResolution.desc, sectionsFunctor and ordinary resolution naturality. Loogle query "Functor.rightDerived, NatTrans" returned an unknown-identifier diagnostic, not evidence of mathematical absence. The independent leanfinder query "Higher cohomology functorial maps for ringed topoi with coefficient morphisms and functorial injective resolution comparison" returned ordinary resolution comparison declarations, including InjectiveResolution.rightDerived_app_eq and Hom.ι'_comp_hom'. The command grep query "cohomologyMap|rightDerived.*[Cc]omp|[Cc]omp.*rightDerived" in CategoryTheory returned general right-derived transformations and comparison constructions. These were read and reused for the formulas; none states every clause of the item. The actual commands and results are recorded in searches.jsonl.

Edge cases: q=0 is retained and normalized explicitly; zero coefficient maps and zero modules are allowed; identity and arbitrary comparison presentations are included; U need not be subterminal; no support/exactness of f_*I is imposed except in map_edge, where the node explicitly assumes it resolves f_*N. In particular a point-topos ring map Z to F_2 is allowed, with no flatness restriction. Integer replacements may begin below zero. Site objects and arrows are both small in the common coefficient universe exactly as this node specifies; no universe equality is imposed on a larger essentially-small site without first using the node's small presentation convention.

Compilation: both modules passed the required server scompile wrapper, separately in dependency order, in module mode and as their library module names, without warnings. No local compiler, Lake, or global build was run.

## Dependency modules

lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison: its recorded theorem demands a Precoverage J with HasIsos, IsStableUnderComposition, IsStableUnderBaseChange and HasPullbacks. The natural-language statement and Stacks 03FD allow any small Grothendieck site, and the item uses precisely that scope. The original theorem, declaration binding, helpers and all proofs are retained. The owning module additionally states CategoryTheory.module_abelian_evaluation_comparison_general, accepting GrothendieckTopology directly and giving the same natural comparison, degree-zero normalization and arbitrary compatible resolution-lift formula. Its unique-existence clause determines every component by the formula on a chosen pair of injective resolutions; hence evaluationComparison is a canonical construction, rather than an arbitrary choice. Only this new theorem has proof sorry. Its source and complete proof docstring are retained verbatim. The consumer imports the original owning module and uses this appended declaration, which is listed in the dependency lean.declarations. No new definition or parallel module is introduced.

## Review by NS

I reread Stacks cohomology.tex lemma-functoriality (01F8) and remark-explain-arrow (01FB), including the actual beta/lambda roof and its orientation; sites-cohomology.tex lemma-derived-pushforward-composition (0D6E), whose statement permits arbitrary ringed topoi; and lemma-cohomology-modules-abelian-agree (03FD), whose second equality is evaluation over an arbitrary site object. I read the accepted 13-step proof, the recorded dependency signatures, RingedToposMorphism's generalized-element and induced module-action fields, and the old module/abelian comparison module before repairing its scope. I did not replace the proof route or change the mathematical statement.

For steps 1--4 I checked the exact source and target of the single-complex augmentation comparison, reversed it to its correct direction, and made the section identity an adjunction-normalized unique comparison. I checked that both roof equations have source H(Y,M), target the homology of sections(P), and invert the target comparison only on the intended side. For steps 5--6 I checked zero degree uses the actual derived augmentations, that scalar restriction is the structural map on generalized elements, and that the identity theorem gives H(phi), not the bare identity on an unrelated coefficient map. For steps 7--9 I checked the direct-image comparison c is used in the correct inverse direction in the composite coefficient map and that the displayed composition order agrees with the node. For steps 10--11 I checked the Leray comparison's orientation and that no extra hypothesis about f_*L was introduced. For steps 12--13 I corrected the chosen slice-terminal evaluation comparison's opposite direction, supplied the already published additive restriction instance, and made ordinary abelian restriction an explicit right-derived natural transformation. I also added restriction_resolution so the slice formulas are available for every source injective resolution, rather than silently demanding an arbitrary pair of resolutions be isomorphic.

The dependency repair was compiled before the consumer. Its uniqueness is forced by the same arbitrary-lift formula already present in its old interface; it does not choose arbitrary data from bare existence. I checked each new theorem's docstring against its role in the accepted proof and each helper definition for an actual construction. The final module has no diagnostic commands or file-local notation/private aliases. All lines satisfy the 100-character limit. This is the delivering worker's rereading; the maintainer supplies the independent review, as the direct-delivery brief requires.

## Second reading by NS

No second worker was started. The worker delivers directly; the maintainer's independent review is the independent reading.

## Returned delivery repair (H13)

The return requires retaining NJ's stage-3-proved comparison instead of rebinding its node
to an unproved general statement. This repair restores every existing key and value of the
live dependency lean record, including module, declaration, statement, author and date.
Only declarations (adding CategoryTheory.module_abelian_evaluation_comparison_general) and
the required explanatory note are added. No other field of the dependency node changes.

Every byte of the live ModuleAbelianEvaluationComparison.lean before its closing namespace
command is preserved, so its original theorem, categorical helpers and all proof bodies
remain unchanged. The general theorem is appended before that closing command with proof
sorry. The item imports the original module and continues to use the exact same general
theorem signature. The separate general module is removed from the packet. This packages
the review's additive-interface repair directly in its owning node's module, in accordance
with the one-module-per-node rule, instead of adding a public import of a separately owned
module. There is no import cycle or dependency rebinding, and no published theorem is unproved.
The item's Lean signatures and its natural-language statement are unchanged.

The return's advisories remain: map_edge hK follows automatically for the nonnegative model;
slice EnoughInjectives is explicit; the second-reading section honestly records direct delivery.
No independent reading is claimed.

## Validation

The initial required dry run of the saved packet still rejected the alternative repair's
new complete proof under the stage-2 sorry-only rule. The additive repair above removes that
conflict: stage-3-published proofs stay intact, while the appended stage-2 theorem is sorry.
No launcher or repository tool was edited, copied, patched, or bypassed.

Self-check: compared both node copies with current live records; only lean differs. Compared
the dependency module with current live source; its original prefix is byte-identical, with
only the new general theorem appended. Verified the restored primary lean record field by
field. Checked that the consumer's only source change from the retained packet is its import
of the original module, and that the general theorem signature and docstring are unchanged.
There are no new DAG nodes and no statement corrections.

The repaired pair passed scompile.py in dependency order, both as sandbox modules and under
their library module names: the dependency compiled in 14.0 seconds and the item in 11.5
seconds, with no compiler diagnostic. The required deliver2.py --no-push then reported
"OK (dry run): commit 79a7b585946 passes the preflight and compiles; nothing pushed".

Final repair reading: Stacks 03FD, sites-cohomology.tex lines 1861--1919, says the comparison
holds for a site and a ring sheaf, at every object U, with no presentation or flatness
hypothesis. The appended theorem binds C : Type u with SmallCategory C, arbitrary
GrothendieckTopology C, R : Sheaf J RingCat, EnoughInjectives for the module category, and
U : C. Its natural-isomorphism family quantifies over every q : Nat, including zero. The
left functor derives module evaluation; the right functor forgets and then derives abelian
evaluation. The first conjunct normalizes their zero augmentations. The second quantifies
over every module M, module resolution I, abelian resolution K, compatible lift phi and
degree q, so its formula determines the chosen comparison uniquely. This is the exact
signature the consumer uses in evaluationComparison; its call and all item signatures are
unchanged. The old Precoverage theorem remains the primary declaration with its old proof.
The only newly postponed theorem in the dependency module is the appended general theorem.


Validation date (UTC): 2026-10-23.
