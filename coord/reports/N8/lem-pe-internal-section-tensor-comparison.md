## Worker report

The module `Sheaf.CategoryTheory.InternalSectionTensorComparison` states
`CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`.
Every theorem has proof `sorry`. The two pure-tensor definitions contain actual
canonical maps, with no chosen unspecified data. The item statement, its hypotheses,
and both dependency lists are unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A site C, objects and arrows in the coefficient universe | `{C : Type v} [Category.{w} C]`, `J : GrothendieckTopology C`, `[UnivLE.{max v w, u}]`; the three universes remain independent. |
| Abelian sheafification exists | `[HasSheafify J AddCommGrpCat.{u}]`, including left exactness. |
| Its local equivalences are monoidal | `[(J.W (A := AddCommGrpCat.{u})).IsMonoidal]`. |
| The closed symmetric tensor on abelian sheaves is sheafified tensor over Z | The existing `Sheaf.monoidalCategory` and `Sheaf.symmetricCategory`, registered as global instances, with `Sheaf.monoidalPreadditive`. These are the canonical localization structures packaged by `sfbSheafTensorStructure`. `SheafTensor` is imported for its closedness/colimit statement. No arbitrary ambient monoidal structure is a parameter. |
| R is a commutative ring object | `(R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]`. |
| Reconstructed section ring and the fixed equivalence | `sectionRingSheaf J R` and exactly `(sectionModuleEquivalence J R).functor`, never a new equivalence. Its source is `Mod (Sheaf J AddCommGrpCat.{u}) R`, target `SheafOfModules.{u}` of the reconstructed ring sheaf. |
| Source coequalizer relative tensor and regular unit | The upstream `Mod.monoidalCategory`: `(M ⊗ N).X` is exactly the displayed coequalizer by `Mod.tensorObj_X`; projection `Mod.tensorObjπ`; unit `Mod.regular R`. |
| Target sheafified balanced section tensor | `SheafOfModules.cochainModulesMonoidal`, the existing localization monoidal structure of `def-pur-sheaf-tensor-product`. |
| E is exact | First conjunct `exactFunctor _ _ (sectionModuleEquivalence J R).functor`, preserving finite limits and finite colimits. The auxiliary `comparison_additive` records additivity needed to map complexes. |
| Natural tensor isomorphism E(M tensor N) = EM tensor EN | Existential family `e` of actual isomorphisms, followed by the equation for every pair of maps `f`, `g`. |
| Unit isomorphism E(R) = R_sec | `e₀` from the image of the internal tensor unit to the section-module tensor unit. Both units are the indicated regular modules. Its section formula is `(e₀.hom.val.app U) r = r`. |
| Comparison fixes every local pure tensor | First equation after `e₀`, for every `M N U x y`, states `e.hom(internalTmul x y) = sectionTmul x y`. `comparison_internalTmul` uses the lax tensor map of sheaf inclusion followed by the actual coequalizer projection. `comparison_sectionTmul` uses the module-sheafification unit on `x ⊗[R_sec(U)] y`, then the inverse canonical `tensorObjIsoSheafification`. Thus neither side assumes evaluation preserves coequalizers or that every sheaf section is a global sum of pure tensors. |
| Associators | The displayed equation using `e (M ⊗ N) P`, `e M N`, the target associator, `E.map (α_ M N P).hom`, and `e M (N ⊗ P)`, `e N P`. |
| Both unitors | The two following equations involving `e₀`, `λ_`, and `ρ_`. |
| Symmetry | The equation `(e M N).hom ≫ (β_ _ _).hom = E.map (β_ M N).hom ≫ (e N M).hom`. |
| Apply E termwise to cochain complexes | `E.mapHomologicalComplex (ComplexShape.up ℤ)`; no boundedness restrictions. |
| Identify direct-sum total tensor complexes | For all `K L`, an isomorphism `t` between `E(mapBifunctor K L (curriedTensor _))` and `mapBifunctor (EK) (EL) (curriedTensor _)`. For every `p q n h : p+q=n`, its equation on `ιMapBifunctor` pins it to `e (K.X p) (L.X q)`. These universal coproduct summands determine the map uniquely and force naturality in both complexes. `mapBifunctor` uses the differential `d_K ⊗ 1 + (-1)^p 1 ⊗ d_L`. |
| Preserve and reflect acyclicity | `∀ K, K.Acyclic ↔ (E.mapHomologicalComplex ... |>.obj K).Acyclic`. This is categorical homology vanishing, with the existing abelian structures. |
| Preserve and reflect flatness | `∀ M, exactFunctor _ _ (tensorRight M) ↔ SheafOfModules.IsFlatOnSite (E.obj M)`. The right side is the recorded definition using the sheafified sectionwise tensor functor. |
| Preserve and reflect K-flatness | Last conjunct: the internal acyclic-total-tensor test over every internal acyclic `A` is equivalent to the recorded `CochainComplex.IsKFlatIndependentCoefficients (EK)`. |
| Meaning of the internal tests | Internal flatness is written as the exact right-tensor test itself; internal K-flatness is written as the quantified acyclic-total-tensor test itself. No additional definition or stronger replacement is introduced. |

The auxiliary theorems `comparison_essentiallySmall`,
`comparison_sheafTensorLeft`, `comparison_sheafTensorRight`,
`comparison_internalColimits`, `comparison_additive` and
`comparison_internalTotalExists` discharge consequences of the original hypotheses,
not new hypotheses. Their docstrings explain the size argument, closedness,
transfer of coproducts through the fixed equivalence, and preservation of addition.
The specialized total-existence instance avoids expensive generic elaboration of
coproduct diagrams; the final file compiles in about 6.5 seconds. Every auxiliary
and the main theorem is listed in `lean.declarations`, with the same node tag.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SheafTensorStructure`: `CategoryTheory.sfbSheafTensorStructure`, its structure's monoidal and symmetric fields.
- `Sheaf.CategoryTheory.SheafTensor`: `CategoryTheory.sfbSheafTensor_properties`, expressing the closed canonical tensor and preservation of colimits.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, `sectionModuleFunctor`, `sectionRingSheaf`. The recorded source is absent from the older local checkout; the full current source was read with `scompile.py --source`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: `CategoryTheory.Mod.monoidalCategory`, `tensorObj_X`, `tensorObjπ`, `isColimitTensorπ`. The source and docstrings are in the read-only 51-module framework; its declaration binding is supplied in this delivery.
- `WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`: `CategoryTheory.Mod.symmetricCategory` and its braiding defined by descent of the ambient symmetry.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal`, `cochainModulesSymmetric`, the canonical localization tensor and its additive infrastructure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`; the underlying complexes and their homology are the existing Mathlib ones.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, `ιMapBifunctor`, paired with `CategoryTheory.MonoidalCategory.curriedTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`; its complete source was read, including its `siteSheafTensorRight` definition.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`; the full current source was read through `scompile.py --source` because the older local source differs. It quantifies over all acyclic complexes, with the same canonical total tensor.

Proof-only dependencies with available modules are also imported: the upstream
`ModuleObjects.Abelian` (including `Mod.instAbelian` and the two finite-exactness
instances), `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`. Module sheafification and
abelian sheafification are imported transitively by the public tensor/equivalence
modules. The main docstring retains all eight natural-language proof steps and
the cited node names. No proof dependency is replaced by a new construction.

Edge cases checked: the zero ring (all modules are zero); zero modules; the empty
site and the topology forcing zero sheaves; the regular module and either unit
factor; complexes concentrated in degree zero; zero and acyclic complexes;
unbounded complexes and negative tensor degrees (the Mathlib total-sign convention
is retained); and independent site/coefficient universes. No nonzero, nonempty,
boundedness, point-existence, or degree restriction was added. The pure-tensor
formulas make sense at every site object, and impose no unprovided point structure.

Searches made before writing:

- `msearch.py leanfinder`, query `equivalence internal modules abelian sheaves sectionwise modules tensor flat K-flat`: eight results about ordinary module flatness (`Module.Flat.iff_preservesFiniteLimits_tensorLeft`, `Module.Flat.iff_rTensor_exact'`, etc.); none is this equivalence comparison.
- `msearch.py leansearch`, query `equivalence internal module sheaves sectionwise modules relative tensor product K-flat`: eight results, chiefly `LinearMap.tensorKerEquiv`, `Module.Flat.iff_flat_tensorProduct`, ordinary tensor lemmas, and the type `SheafOfModules`; no match.
- `msearch.py loogle`, query `SheafOfModules, Monoidal, Equivalence`: query rejected because `Monoidal` is unknown to the search index; no absence conclusion drawn from it. The valid follow-up query `"sheaf", "tensor", "equiv"` returned zero hits.
- `msearch.py grep`, query `sectionModuleEquivalence|internal.*tensor.*comparison` in `CategoryTheory`: no match for the comparison.
- Source searches with `rg` in Mathlib, the upstream `WeilConjectures` tree, and the side `lean/Sheaf` tree, using the item id, `sectionModuleEquivalence`, and internal/section tensor patterns: found the recorded equivalence and tensor infrastructure, but no theorem with all the item's conclusions. Related affine tensor statements and scalar-pullback statements concern other categories and maps.
- Read `coord/pefw-upstream-framework.md`, then `ModuleObjects/Monoidal.lean` and `Symmetric.lean`: the former gives the exact relative-tensor construction, so its existing declaration is bound instead of copied. Read the canonical target `tensorObjIsoSheafification` in upstream `Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` and the Mathlib totalization signatures.

Source checked directly: `sites-modules.tex`, section `section-tensor-product`
(Tag 03EK), `lemma-sheafification-tensor` (0GMW), and the subsequent bilinear-map
universal property; current blueprint unit `sk-def-pe-derived-completion/_section.md`.
There is no statement correction or disputed clause.

## Dependency modules

`def-sfb-modobj-relative-tensor`: its record was missing despite the available,
exact upstream construction. This delivery adds only its `lean` record with
`existing: true`, module `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`,
and primary declaration `CategoryTheory.Mod.monoidalCategory`. Its coequalizer
maps, action through the first factor, regular unit, and induced constraints
agree with every clause of the node. The existing upstream declaration is used
by the item; no additional module or copied definition is supplied. The delivery
wrapper checks the primary and supporting declarations with the compiler.

## Validation

`scompile.py N8 lem-pe-internal-section-tensor-comparison` compiled the entire
new module separately as both sandbox and library module, with no errors or
warnings. All variables and universes are explicitly bound. The only postponed
proofs are the named theorems in `lean.declarations`; the pure tensors use actual
sheafification units, tensor comparisons and the coequalizer projection.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
