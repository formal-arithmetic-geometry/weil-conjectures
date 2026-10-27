## Worker report

Delivered module: `Sheaf.CategoryTheory.Sites.DerivedSectionsUnitPasting`.
Namespace: `CategoryTheory.SiteDerivedSections`.
The node's TeX statement and proof are unchanged. Its statement dependencies gain the already
landed definition `def-pur-constant-module-inverse-image-lift`, whose recorded declaration
`ConstantLeftModuleInverseImageLift` is the normalized induced constant-ring module adjunction
that the node explicitly asks to use. There are no new nodes and no dependency repairs.

The declaration list records all parts of this multi-clause node. `geometric_pasting` is the
primary declaration. `existsUnique_comparison`, `composition_pasting`,
`resolution_formula`, `cohomology_resolution_formula`, and `negative_cohomology` are the
other postponed theorems; every proof is exactly `by sorry`. All helper definitions have
actual data. In particular `comparison` selects from unique existence of `Comparison`:
its ordinary-terminal and derived-unit normalization equations determine both isomorphisms
uniquely. It does not select an unspecified isomorphism or an arbitrary functor.

Hypothesis and clause correspondence:

| Node text | Lean representation |
| --- | --- |
| Small sites C, D, E | `C D E : Type u`, their `SmallCategory` instances, and `J K H : GrothendieckTopology ...`. These are the generated-topology/sheaf encoding retained by the recorded site dependency. No finite-limit, subcanonical, point, connectedness or nonempty-cover hypothesis is imposed on the sites. |
| Terminal objects | Explicit `TC TD TE` and `hC hD hE : IsTerminal ...`; each can be any terminal site object. |
| Commutative coefficient ring R | `R : Type u` and `[CommRing R]`; there is no `Nontrivial R`. |
| Modules over the constant ring sheaf | The recorded `ConstantLeftModuleInverseImage.Modules J R`, transparently `ringedSiteModules ((constantSheaf J RingCat).obj (RingCat.of R))`, and similarly on the other sites. This is the recorded module category, not a new category. |
| Bounded-below derived categories | The actual `DerivedCategory.Plus` with explicit `[HasDerivedCategory.{w} ...]` localization-size instances for the module categories and `ModuleCat R`. These bind a model of the derived category, not an additional mathematical property. |
| Geometric morphisms f, g, h | The recorded `GeometricMorphism` on the actual set-sheaf categories, with its specified `inverse`, `direct`, `adj` and `leftExact`. `g.comp f` is the recorded composition. |
| Induced exact module inverse image and right adjoint, normalized on constant sections | `d`, `dg`, `dh`, `dfg : ConstantLeftModuleInverseImageLift ...`. This existing definition specifies transported ring addition/multiplication, every constant scalar, underlying set and abelian sheaf identifications, and compatibility of the module and set adjunction units. It includes the exact `moduleFunctor`, `moduleDirect`, and `moduleAdj`. Their use is representation of the node's induced functors, not a new exactness assumption. |
| Ordinary sections at the terminal site object, valued in R-modules | `sections J R TC` is Mathlib `SheafOfModules.evaluation` followed by `ModuleCat.restrictScalars` along the genuine constant-section sheafification unit `R -> R_J(TC)`. |
| Canonical ordinary comparison Gamma_C f_* = Gamma_D | `Comparison.ordinary` is a natural isomorphism, and `ordinary_normalization` identifies its value on every section with the set adjunction bijection from the terminal sheaf. `sectionHom` uses Mathlib's `constantSheafAdj`; `directSets` composes the lift's already specified underlying comparisons. |
| Natural canonical Leray isomorphism lambda_f | `Comparison.leray : moduleDirect.rightDerivedFunctorPlus ⋙ sections_C.rightDerivedFunctorPlus ≅ sections_D.rightDerivedFunctorPlus`. `leray_normalization` is exactly the derived-unit equation of proof step 4: the composite derived unit followed by lambda equals the localized ordinary section comparison followed by the section-derived unit. `existsUnique_comparison` asserts existence and uniqueness of these normalized data. |
| eta_f is the canonical derived-adjunction unit | `d.moduleAdj.derivedPlus.unit` from the recorded upstream bounded-below derived-adjunction interface. |
| T_f = lambda at f-inverse K composed with RGamma(eta_f) | `pullback` is exactly the whiskered derived unit followed by the whiskered normalized `leray.hom`, with only the necessary functor unitors and associator. Its natural-transformation type includes naturality in every derived morphism. `ordinaryPullback` is the analogous actual ordinary unit/sections composite. |
| Composition via canonical c | `composition_pasting` produces the unique ordinary module natural isomorphism `c : d.moduleFunctor ⋙ dg.moduleFunctor ≅ dfg.moduleFunctor` satisfying the underlying-set compositor equation. The equation for every derived `M` is `T_fg = T_f ≫ T_g ≫ RGamma(c_D)`. Here `c_D` is the actual exact descent `mapDerivedCategoryPlusCompIso.inv ≫ mapDerivedCategoryPlusNatIso c`. Thus the equation lives in D-plus before applying cohomology. |
| Geometric 2-isomorphism h = fg and its induced alpha | `geometric_pasting` takes `t : h.direct ≅ (g.comp f).direct` ON SET SHEAVES, and produces the unique module `α` whose underlying map is the mate `GeometricMorphism.inverseIso t`. It gives precisely `T_h = T_f ≫ T_g ≫ RGamma(alpha_D)`. There is no arbitrary module-automorphism parameter. |
| Sheaf M in degree zero and injective resolutions | `cohomology_resolution_formula` takes `M`, the actual single complex `HomologicalComplex.single ... (.up ℤ) 0`, a quasi-isomorphism `a` to the termwise injective, nonnegative complex `I`, and a quasi-isomorphism `a'` from inverse image of the same single complex to the termwise injective, nonnegative complex `L`. Exact inverse image canonically identifies this second single complex with the single sheaf inverse image. |
| Any comparison over the pulled-back sheaf | `b : moduleFunctor.mapCochainComplexPlus.obj I ⟶ L` and `hb : map a ≫ b.hom = a'`. There is no monomorphism or quasi-isomorphism assumption on b in this degree-zero theorem: quasi-isomorphism follows from the two augmentations and exactness. Hence every comparison allowed by the node is included. |
| Ordinary pullback into inverse image of the resolution, followed by sections of b | `sectionChainMap` is the actual map of complexes obtained from `NatTrans.mapHomologicalComplex ordinaryPullback` followed by `sections.mapHomologicalComplex.map b.hom`. The differential maps and their compatibility are those of Mathlib's mapped complexes. |
| H^q(T) is the usual cohomology pullback for every integer q | `resolution_formula` first identifies the derived arrow in its injective-resolution coordinates with the localization of `sectionChainMap`. `resolvedPullback` writes those coordinates explicitly using the two section-derived units and `resolutionIdentification`; the source and target units are invertible on these injective complexes. `cohomology_resolution_formula`, for `q : ℤ`, states that applying derived homology and the canonical `homologyFunctorFactors` gives the actual `HomologicalComplex.homologyMap` of this same chain map. The augmentation `a` identifies its input with M[0], and the commuting augmentation equation identifies its output with inverse image of M[0]. |
| Zero groups for q < 0 | `negative_cohomology` uses `q : ℤ`, `hq : q < 0`, and asserts `IsZero` for both the source and target homology objects of the degree-zero pullback, including the actual derived inverse image in the target. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` and its documented generated Grothendieck-topology encoding; the theorem works directly with those sheaf categories and terminal objects.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `constantSheafAdj`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent specialization of Mathlib `SheafOfModules` with its inherited abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`; `...TStructure`: `DerivedCategory.Plus`.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`, `.comp`, `.inverseIso` and their full set-level adjunction signatures.
- `Sheaf.CategoryTheory.ConstantLeftModuleTransport`: `ConstantLeftModuleInverseImageLift` and its recorded helpers `Modules`, `V`, `U`, `W`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`: `Adjunction.derivedPlus`, `derivedPlus_unit_app_fac`, `derivedPlus_counit_app_fac`.
- `...PlusComp`: `Functor.rightDerivedFunctorPlusCompUnit` and its canonical composition interpretation; `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: the exact derived factorization, `mapDerivedCategoryPlusCompIso` and `mapDerivedCategoryPlusNatIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`: `rightDerivedFunctorPlus`, its unit and injective-computation instance; `...KInjective`: `CochainComplex.IsKInjective.Qh_map_bijective`; `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `isKInjective_of_injective`.
- Proof imports also retain `SheafOfModules.grothendieckAbelian_with_localized_generator`, `IsGrothendieckAbelian.enoughInjectives`, `CochainComplex.exists_mono_quasiIso_injective_boundedBelow`, the bounded-below injective model lifting instance, `CochainComplex.homotopy_of_comp_quasiIso_of_injective`, and `Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits` from their recorded modules. The module-category Grothendieck instance itself uses the upstream general-ring theorem `SheafOfModules.isGrothendieckAbelian`.

Source checks: read the complete node and its eight proof steps; every statement-dependency
statement and Lean record, and the declarations and docstrings used. Read local Stacks
`derived.tex`, `lemma-compose-derived-functors` (015M), `sites-cohomology.tex`,
`section-derived-functors` (071J), and `sites.tex`, `definition-2-morphism-topoi` (04IA).
Read the current blueprint `latest/.../sk-prop-a1-kummer/lem-pur-a1-direct-image.proof.md`,
particularly Step 4. The assigned node is an auxiliary result, not the unit's statement.
No source-based statement correction or disputed statement was needed.

Edge cases checked before and after elaboration: identity geometric morphisms use the
identity mate/compositor and give the identity normalized pullback. Zero coefficient rings
and zero module sheaves are admitted. Disconnected sites and topoi require no changes.
A terminal object excludes the empty site category as the node itself does, while sheaf
categories with an empty covering or degenerate topos are allowed. Degree zero uses the
ordinary section map; all negative integers remain in the homology formula and their
objects vanish by the final theorem. Comparisons b need not be monomorphisms. Twisting a
module comparison by a unit different from 1 violates the displayed underlying-set mate
normalization. No noncommutative ring generalization or finite-coefficient restriction was
introduced. One common set universe for the three small sites and coefficient modules and
an arbitrary explicit localization universe w are used throughout; no equality w = u is
imposed.

Searches for a pre-existing complete statement (all used the prescribed `msearch.py`):

- LeanFinder: “Derived global sections pullback via the adjunction unit and Leray isomorphism respects composition and geometric natural isomorphisms”. Eight hits, primarily `SheafOfModules.pullbackComp`, `pullbackObjUnitToUnit` and underived adjunction results; no complete match.
- Loogle: `"rightDerived", "comp"`. Twelve hits including `rightDerivedNatTrans_comp` and abstract localizer right-derived comparisons; none states the terminal-section unit/Leray pasting and geometric-2-isomorphism/resolution assertions.
- Mathlib grep: `rightDerivedFunctorCompIso|globalSectionsUpperStarMap|rightDerived.*[Uu]nit`, under `CategoryTheory`. Eight hits in abstract derived/localizer machinery; no complete match.
- LeanSearch: “The pullback on derived global sections induced by the adjunction unit and Leray comparison is compatible with composition of geometric morphisms and geometric 2-isomorphisms”. Eight mostly underived pullback/compositor hits; no match.
- `rg` in both project library roots for geometric morphisms, section pasting, constant modules, and the item id; the item id had no existing declaration. Opened the nearby `ObjectDerivedSectionsPullback`, `UnboundedLeraySections`, `RingedSiteScalarGlobalSections`, `ConstantScalarGeometricAdjunctions` and module-transport sources. The first concerns continuous/cocontinuous site functors and objectwise evaluation, the second unbounded objectwise Leray for site functors, and scalar-global-sections concerns a specified global scalar action and unbounded sections. None gives this result. Existing geometric morphisms, constant-module lifts, exact descent, derived adjunction and derived composition are reused.
- DAG/upstream-name searches located `def-pur-constant-module-inverse-image-lift` as the existing owner of the required normalized lift. Its record is used without editing that dependency or re-declaring the lift. No missing independent notion was found.

Validation: every compiler invocation used the prescribed `scompile.py`, with module-mode
headers and all universe and variable binders explicit. The final compile and delivery
preflight results are recorded below after those checks complete.

Final direct `scompile.py` validation passed both the sandbox compile (47.7 seconds)
and the real module-name compile (50.8 seconds), each under the unchanged 60-second
limit, without warnings. A profiling-only scratch file was kept outside `lean/` and
is not delivered. Profiling identified costly generation of unused structure machinery;
the delivered module disables `genInjectivity`, `genSizeOf` and `genSizeOfSpec` for its
comparison structure and preserves every field and theorem signature. Local irreducibility
of the uniquely selected comparison and of the pullback definition prevents unnecessary
elaboration unfolding; all public definitions remain available to downstream proofs.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
