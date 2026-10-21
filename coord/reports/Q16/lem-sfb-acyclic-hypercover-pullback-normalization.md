## Worker report

Item: lem-sfb-acyclic-hypercover-pullback-normalization. Group Q16, stage 2.
Module: `Sheaf.Paper.AcyclicHypercoverPullbackNormalization`.
Main declaration: `AlgebraicGeometry.Scheme.AcyclicHypercover.pullback_normalization`.
All declarations in the module, including the other clauses of the statement, are
listed in `lean.declarations`. Every theorem has `sorry`; all constructions have
real data. The original mathematical statement, proof, and proof dependencies are
unchanged. The already-landed inverse-image and operations definition nodes remain in
`stmt_deps`. Three definition nodes now own matching arrows, composite coefficients
and the ordinary comparison. The two theorem-only dependencies flagged by L are
removed from `stmt_deps`; neither theorem is used to state the consumer.

Source read: `literature/stacks-project/proetale.tex`, Tag 09A2,
`lemma-compute-cohomology`, its injective-resolution proof. The functoriality and
normalization are the eight steps of the item's recorded proof, using the actual
adjunction and derived-composition constructions; the module docstrings give those
steps and their dependencies. This is not merely an unnormalized cohomology iso.

Hypotheses and clauses, with the namespace prefix
`AlgebraicGeometry.Scheme.AcyclicHypercover` understood below:

| Node text | Lean rendering |
| --- | --- |
| Schemes and a morphism h:X'→X | Explicit section binders `{X Y : Scheme.{u}} (h : Y ⟶ X)`. |
| Small pro-etale sites, compatible sizes | The published `X.ProEt`, `Y.ProEt`, `ProEt.topology`; object universe u+1 and morphism universe u are retained. Coefficients are `CommRingCat.{u+1}` and modules have that compatible value universe. No equality of site object and morphism universes is imposed. The published AsSmall model only transports module constructions. |
| Ring sheaves R,R' and the specified inverse-image identification | `R : Sheaf (ProEt.topology X) CommRingCat.{u+1}`, similarly `S`, and `c : (proEtaleSheafInverseImage h CommRingCat.{u+1}).obj R ≅ S`. These are arbitrary ring sheaves, not constant or finite coefficients. |
| Resulting exact inverse image, right adjoint | The actual `proEtaleRingModulePullback h R S c`, `proEtaleRingModuleDirectImage`, and `proEtaleRingModuleAdjunction`; published exactness/additivity instances are used. This is the specialized actual ringed-topos action of h, not an extra independently chosen ringed-topos morphism. |
| Augmented simplicial objects over the bases | `U : SimplicialObject (Over (⊤_ X.ProEt))`, similarly `V` over Y. The slice structure supplies all augmentation maps and their compatibility. |
| Every finite matching arrow is a cover, including degree zero | `hU`, `hV` quantify over n, target T, and arrow μ; `SimplicialObject.IsProperFaceMatchingArrow ...` implies membership of `Sieve.generate (Presieve.singleton μ.left)` in the topology. The existing predicate is terminal in degree zero, binary-product matching in degree one, and the finite proper-face boundary limit thereafter. Finite limits exist on the site, so this universal presentation does not drop matching-object existence. Quantifying over all choices is equivalent to the canonical choice by invariance under isomorphisms. |
| Weak contractibility of every term | `wU`, `wV` use exactly `GrothendieckTopology.IsWeaklyContractible.{u+1}` for every natural degree; its published definition is surjectivity of section maps for locally surjective morphisms of set sheaves, equivalently epis. No affine assumption is used. |
| g_n over h, compatible with faces, degeneracies and augmentation | `g : V ⋙ Over.forget _ ⟶ U ⋙ Over.forget _ ⋙ proEtaleBaseChange h`. Naturality covers every simplex operator. A map over h is equivalently a map to this fibre product; it need not be the fibre-product projection or an isomorphism. Compatibility with the terminal augmentations is automatic. |
| M an R-module sheaf | `M : proEtaleRingModules X R`, the published abbreviation of the recorded ringed-site module category. |
| Nonnegative alternating section complexes, as abelian groups | `rows` is the recorded `ProEt.hypercoverSectionRows` followed by coefficient forgetting. Its Nat-to-Int extension is zero in negative degrees; the original alternating-coface functor supplies the signed face sum. |
| Canonical section map c_g | `sectionRestriction` is the actual normalized ordinary module unit on sections followed by sheaf restriction along g. `restrictionComponent` uses the canonical extension isomorphisms and is zero in negative degrees. `restrictionComponent_comm` states the differential equation, and `restriction` has these specified components. It is not an arbitrary chain map. |
| Chosen bounded-below injective resolutions | `descent` and `IsNormalized` quantify over every bound `N : ℤ`, complex I, `[I.IsStrictlyGE N]`, `[∀ n, Injective (I.X n)]`, and map `i : M[0] ⟶ I` with `[QuasiIso i]`. Apply on X,M and on Y,h*M separately to obtain the two independently chosen resolutions. |
| Signed totals T_U,T_V | `total` is exactly recorded `ProEt.hypercoverTotal`, then coefficient forgetting. Thus its differential is δ+(-1)^p d, not a different total convention. |
| C_U(M)=T_U(M[0]), C_V(h*M)=T_V(h*M[0]) | `rowResolution_single_isIso` and `rowSingleTotalIso` expose the canonical isomorphism whose forward arrow is the actual (n,0) total injection. `rowResolution_eq_total_map` explicitly identifies the resolution map with T(i) after that iso. |
| Specified restriction augmentations α_I,α_J | `augmentation` is the recorded `ProEt.hypercoverAugmentation` whiskered by scalar forgetting. No existential replacement augmentation is introduced. |
| Four chain maps are quasi-isomorphisms | `descent` first conjunct asserts both `QuasiIso (rowResolution ... i)` and `QuasiIso ((augmentation ...).app I)` for every chosen resolution. Instantiate twice, on U and V, to obtain precisely all four arrows. |
| Comparisons in D(Ab) from these zigzags | `derivedSectionsZero` is single-degree-zero, localization Q, and the published right derived functor of evaluation to `AddCommGrpCat`. The other side is `rows ⋙ DerivedCategory.Q`. `resolutionSectionsIso` is the published canonical computation on a bounded-below K-injective resolution. |
| Augmentation normalization and resolution independence | `IsNormalized` states, for every resolution, `A.hom.app M ≫ Q.map(rowResolution i) = resolutionSectionsIso.hom ≫ Q.map(augmentation.app I)`. This is the exact zigzag equation. `descent` gives a unique natural iso satisfying it, and `comparison` selects this uniquely specified iso. No data is chosen from a bare existence theorem. |
| Identification with the actual derived adjunction unit | `derivedSectionPullback` first applies derived Γ to `(proEtaleRingDerivedAdjunction h R S c).unit`, then uses `Functor.rightDerivedFunctorCompIso'` with the actual terminal-object `directSectionsIso`, then the canonical exact-pullback/single-complex identifications. `pullback_normalization` equates its square with `Q.map(restriction ... g M)` under `comparison` on each site. |
| Natural in M | `comparison` is a natural iso, and `restriction_naturality` gives the strict chain-map coefficient square for every coefficient morphism. The canonical unit and composition comparison in `derivedSectionPullback` are natural. |
| Refinements on both sites | `refinement` is actual restriction of sections. `comparison_refinement` states the normalized comparison equation for any site and any refinement, so applies on either side. `restriction_refinement` gives the strict square for simultaneous compatible refinements r,s. |
| Composition of diagrams | `proEtaleRingCompositeCoefficients` is the already published canonical composite coefficient identification. The definition module `ProEtaleOrdinaryPullbackComparison` supplies `existsUnique_composition`, fixing the ordinary comparison by its conjugate direct-image section equation (fibre-product pasting), and `compositionIso`, selecting that uniquely fixed map. `restriction_comp` states equality of composite section maps under it. `derivedSectionPullback_comp` states the corresponding equation for the actual derived-unit maps with exactly the same coefficient identification. These together with `pullback_normalization` give composition of the normalized squares. |
| No cartesian requirement; no assertion c_g is a quasi-isomorphism | The only g datum is the above natural transformation. Neither the main theorem nor any helper assumes cartesian squares, or asserts `QuasiIso (restriction ...)`. Only the four coefficient-resolution and augmentation maps are inverted. |

The generic recorded `RingedToposMorphism` is publicly imported. Its abstract data
need not be postulated a second time: the published pro-etale operations construct
the action, adjunction and derived operations for these actual sites and c. In
particular the smaller-Hom universe of ProEt is not collapsed to apply a specialized
abstract-site interface. The actual derived composition API already permits the
independent site universes.

Dependency declarations used (the full recorded signatures and docstrings were
read, including the Mathlib matches):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `SimplicialObject`, faces and degeneracies.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`: `GrothendieckTopology.IsWeaklyContractible`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` (used through the published `proEtaleRingModules`).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal`: `Scheme.ProEt.hypercoverSections`, `hypercoverSectionRows`, `hypercoverTotal`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation`: `Scheme.ProEt.hypercoverAugmentation`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`: the actual arbitrary-ring-sheaf module/derived adjunctions, derived pullback, and factorization; its public dependencies supply the module pullback and direct image. The current `def-weil-pbc-proetale-operations` module `ProEtaleConstantRingOperations` publicly reexports this general interface; no constant-ring specialization is used here.
- `Sheaf.CategoryTheory.SiteHypercoverDisjointUnion`: `SimplicialObject.IsProperFaceMatchingArrow`, owned by the new definition node `def-sfb-proper-face-matching-arrow`, using the unchanged existing finite boundary diagram.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`: `proEtaleRingCompositeCoefficients`, now owned directly by `def-sfb-proetale-composite-coefficients` with `existing: true`. The derived-composition theorem node is no longer a statement dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison`: `AlgebraicGeometry.Scheme.AcyclicHypercover.compositionIso` and its unique section-normalized mate characterization, owned by `def-sfb-proetale-ordinary-pullback-comparison`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`: `Adjunction.preservesKInjectiveComplexes` and `Functor.rightDerivedFunctorCompIso'`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`: `rightDerivedFunctor`, `rightDerivedFunctorObjQIso`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.isKInjective_of_injective`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`: the imported `HasDerivedCategory.ofIsGrothendieckAbelian` instance supplies the derived category of abelian groups. `Mathlib.Algebra.Category.Grp.AB` supplies `IsGrothendieckAbelian` for abelian groups. The packet no longer declares its own competing standard instance.

Every recorded proof dependency's module is imported (ordinary imports unless
already publicly needed in the statement). The proof plan remains the node's eight
steps, as given in the theorem docstrings. The additional statement dependencies are definition nodes owning construction
interfaces, not hypotheses or theorem dependencies.

Edge cases checked by reading the actual formulas:

- Degree-zero matching object is the base, degree-one matching is the binary fibre product.
- Negative degrees of section rows are zero, and the -1 to 0 differential is zero.
- Any integer lower bound N is accepted, including resolutions with negative terms.
- M=0 and the empty scheme are not excluded; no nonemptiness or nonzero-ring assumption.
- Nonaffine weakly contractible terms are allowed; exactness uses the set-sheaf definition.
- No quasi-compactness, separatedness, finite/torsion/constant coefficient or bounded-M condition.
- The identity and constant hypercover cases use actual units/restrictions, not arbitrary choices.
- Two points over one point can give a noninvertible section map; this is allowed because c_g is never inverted.
- Refinement maps need only be simplicial over the augmentation. Composition uses the actual coefficient/pasting identifications; the two hypercover maps need not be cartesian.

Searches made before construction:

- `msearch.py ... leanfinder "acyclic hypercover comparison natural derived global sections pullback adjunction unit"`: eight site/one-hypercover results, no normalized full hypercover comparison.
- `msearch.py ... loogle "hypercoverTotal, hypercoverAugmentation, derivedUnit"`: no match (hypercoverTotal is a project name).
- `msearch.py ... grep "hypercover|Hypercover" CategoryTheory/Sites`: one-/zero-hypercover infrastructure only; no statement of this derived-unit identification.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `acyclic.*[Hh]ypercover|hypercover.*[Pp]ullback|hypercover.*[Nn]ormaliz|lem-sfb-acyclic-hypercover-pullback-normalization`: older unnormalized single-site or etale/Grothendieck hypercover comparisons, not the four-arrow augmentation-normalized actual-unit theorem here.
- Direct node-id search in `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no declaration for this node.
- Existing total, augmentation, matching-arrow, inverse-image and canonical composition constructions were reused rather than copied. The helpers express the maps and equations of this item's statement. The repair records three independent notions as definition nodes, rather than citing theorem nodes solely to obtain their helper definitions.

No mathematical statement dispute or correction. The review found and this repair
fixes a dependency-ownership fault; the mathematical statement remains unchanged.
Validation: prescribed `scompile.py` compiles each delivery file in sandbox and
library namespaces; only expected theorem sorry warnings are permitted.
The dry run and actual delivery are run after this report is written.

## Second reading by Q16

A separate second pass by the same worker checked the node and every declaration
clause by clause, especially the direction of the normalization equation, arbitrary
(noncartesian) g, signs, all four quasi-isomorphisms, every-resolution quantification,
and the actual derived unit rather than a newly named map. This pass added the
explicit single-total identification and its T(i) equation, and the derived-unit
composition equation, so these clauses are exposed for later proof work.

This is not claimed as an independent-worker reading: the dispatcher explicitly
prohibits starting other agents and says the maintainer performs the independent
review. That review remains with the maintainer. No independent review is fabricated.


## Repair of independent review at a0d47048ff73

H2/H13 is repaired by replacing
`lem-weil-pbc-site-hypercover-disjoint-union` and
`lem-weil-pbc-proetale-derived-pullback-composition` in the item's `stmt_deps`
with definition nodes for the actual objects used. The original theorem statements,
proof plan, and proof dependencies are unchanged. Compared with the saved returned
packet, this is a substantive node-ownership and module repair. The prescribed
initial dry run rebased that saved packet onto current main and passed mechanically;
that did not discharge the independent review's mathematical/interface finding.

Both advisories are addressed as well. The duplicate public
`abelianGroups_hasDerivedCategory` instance is removed: all D(Ab) occurrences use
`HasDerivedCategory.ofIsGrothendieckAbelian` from the imported module. The ordinary
`compositionIso` and its exact uniqueness/section equation have moved unchanged
into their owning definition module. The consumer imports that module; it does not
redefine the ordinary comparison or cite the derived-comparison theorem as a
statement dependency. The namespace of the moved declarations is preserved, so
the composition clauses have exactly their previous signatures.

## New nodes

`def-sfb-proper-face-matching-arrow` owns the unchanged existing declaration
`CategoryTheory.SimplicialObject.IsProperFaceMatchingArrow` in
`Sheaf.CategoryTheory.SiteHypercoverDisjointUnion` (`existing: true`, no new module).
Its statement renders the three branches exactly: n=0 is `Nonempty (IsTerminal M)`;
n=1 is a limiting binary fan with `μ ≫ p i = K.δ i`; n≥2 is a limiting finite
boundary cone, an isomorphism from M to its vertex, and all face equations.
The source is Stacks 0186 (finite face diagram) and 0DB1/0DB2 (augmented slice
matching). Arbitrary categories and independent object/morphism universes remain
allowed. No finite-limit existence hypothesis is imposed: if no limiting cone
exists the predicate is false. Degree-zero μ is canonical by terminal uniqueness.
The theorem node that used to list this helper does not own its definition.

`def-sfb-proetale-composite-coefficients` owns the unchanged existing declaration
`AlgebraicGeometry.Scheme.proEtaleRingCompositeCoefficients` in
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition` (`existing: true`,
no new module). Its hypotheses are arbitrary composable scheme morphisms, three
commutative-ring sheaves and two coefficient isomorphisms. Its three arrows are
`(proEtaleRingInverseImageComp h k).app R_V`, inverse image applied to `c_k`, and
`c_h`, composed by `≪≫`. Thus it fixes the composite coefficient identification
without independent choices. The source is the ringed-topos composition of Stacks
03D8 and the coefficient convention in 0D6D. It retains the small-site universe
levels and handles identity maps, empty schemes and the zero ring. No previous
definition node records this declaration; the former theorem dependency had a
different recorded module and is now removed from `stmt_deps`.

`def-sfb-proetale-ordinary-pullback-comparison` owns the new module
`Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison`. Its declarations are
the unchanged `AcyclicHypercover.existsUnique_composition` and `compositionIso`
moved from the returned consumer. The schemes, coefficient sheaves and
identifications are explicit binders; the composite coefficients are the published
definition owned above. The unique isomorphism is from pullback along the composite
to the composite of module pullbacks. Its conjugate is fixed for every module,
site object and section by `N.val.map ((MorphismProperty.Over.pullbackComp k h).hom.app W).op`.
`compositionIso` selects this uniquely specified isomorphism; its data is never
`sorry`. The existence/uniqueness theorem has the complete original proof docstring
and its proof is `sorry`. It is the canonical ordinary comparison underlying
Stacks 03D8/0D6D, not a second derived comparison. No new hypothesis or equation
is added to the consumer. All three new nodes cite exactly their bracketed
notions and have the item's chapter, unit and inherited null blueprint ancestor.

Searches for all new nodes were actually run in this repair and are recorded in
`mathlib_searches`, including their actual result names:

- `leansearch`: "Proper face matching arrow of a simplicial object is characterized by a boundary limit": eight face/naturality/Segal results, no matching-arrow predicate.
- `leansearch`: "Composition of inverse images of ring sheaves induces a canonical comparison of module pullbacks": eight general module pullback and mate results, including `SheafOfModules.pullbackComp` and `conjugateEquiv_pullbackComp_inv`; these do not name the chosen pro-etale module functors with their coefficient transport.
- `leanfinder`: "Composite coefficient identification and canonical ordinary module pullback comparison for morphisms of ringed sites": eight general module/free-section results, no exact project interface.
- `loogle`: `"SimplicialObject", "matching"`: zero hits.
- `msearch.py grep`: `IsProperFaceMatchingArrow|proEtaleRingCompositeCoefficients|proEtaleCanonicalPullbackComposition`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`: found the exact matching predicate at SiteHypercoverDisjointUnion.lean:42 and coefficient identification at ProEtaleDerivedPullbackComposition.lean:36. These are reused, never copied. ProEtaleCanonicalPullbackComposition selects a derived comparison, not an ordinary module comparison.
- Definition-node `lean` records searched over `dag/nodes`: no node owns either exact definition or the ordinary comparison. Broader matching/coefficient text searches find theorem nodes and distinct matching-object notions, not this predicate/composite identification.
- `blueprint_refs.py search` for "matching", "composite coefficient", and "pullback comparison": respectively six, zero, and nineteen imported nodes; none states one of the three notions. `ancestor` returns None, as already recorded on the item.

## Second reading of the repair by Q16

The same worker re-opened all three new node records, their existing declarations
or new module, and the consumer. Matching-arrow degree zero, binary-product degree
one and higher boundary equations agree exactly. The composite coefficient formula
has the same three factors and orientation. The moved comparison has exactly the
same unique mate equation and arguments. The consumer's coefficient, refinement,
composition and derived-unit equations have not changed; removing the D(Ab)
instance makes all of them use the one imported localization. The removed theorem
nodes are absent from `stmt_deps`; all three new definition nodes are present.
Only `lean` and the authorized `stmt_deps` additions differ from current main for
the item. No independent-worker review is claimed; L supplies that independent
review as the dispatch brief requires.
