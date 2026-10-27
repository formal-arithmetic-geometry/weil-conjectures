## Worker report

The delivery states `AlgebraicGeometry.ProEtale.noetherian_scalar_constructible_fp2`
in `Sheaf.Paper.NoetherianScalarConstructibleFp2`. Its statement is unchanged from
the accepted O4 stage-1 split. The current standing brief's stage-handoff paragraph
explicitly resolves the inherited stage-1 live-wins failure: a reviewed split is
input for stage 2, and the item has no pre-existing Lean record or released repair
note. This delivery does not re-split it.

The two maps are `colimit.post`, not arbitrary morphisms or merely factorizations.
The first functor is `preadditiveCoyoneda.obj (Opposite.op C)`, the additive group
of ordinary ambient module maps. The second is `c.yonedaExtOneFunctor C`, whose
carrier is literally `YonedaExtension.Classes M C 1`, the existing quotient of
short exact sequences. Its group is `c.classGroup M C 0`. Its arrows conjugate
Mathlib's covariant Ext action by the recorded canonical normalized additive
comparison. The comparison's `naturality` on sequence maps identifies them with
pushout along the left endpoint; its `baer_sum` identifies the group operation
with geometric Baer sum. Thus the second `colimit.post` is precisely the node's
pushout comparison, including its source and target Yoneda carriers.

The statement quantifies over every `c : YonedaDerivedExtComparison` of this
ambient category. This adds no mathematical condition: the recorded
`nonempty_yonedaDerivedExtComparison` supplies such comparisons for every abelian
category, and its endpoint normalization fixes the action on each quotient class.
No existence-based object or unnormalized arrow is chosen in this delivery.
`HasExt.standard`, enabled as a local attribute on that existing declaration,
uses the universe of the actual Yoneda quotient, `max u v` (here `u + 2`).
The filtered index category remains `Type (u + 1)`, exactly the site's size
convention; it is not forced into the smaller scheme universe.

Clause-by-clause rendering:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. `Mon.mk` isomorphisms
  preserve both ring operations, not only additive groups.
- Finite discrete A killed by an ell-power: the first disjunct of `hΛ` binds
  its `CommRing`, topology, `DiscreteTopology` and `IsTopologicalRing`; it asserts
  `Finite A`, `∃ n, ∀ a, (ℓ ^ n) • a = 0`, and a coefficient ring isomorphism.
  `A : Type` loses no finite isomorphism class. There is no `Nontrivial A` binder.
- Z_ell: the second disjunct uses `continuousMapRingObj ℤ_[ℓ]`.
- O_E: the third disjunct uses `E : PadicAlgCl.FiniteIntermediateField ℓ`
  and `Profinite.padicIntegersRingObj ℓ E`, with its induced norm topology.
- Q_ell and E: the fourth and fifth disjuncts use `continuousMapRingObj`
  on `ℚ_[ℓ]` and on the same kind of finite intermediate field in `PadicAlgCl ℓ`.
  Quantifying over embedded finite fields is the source's fixed-closure convention.
- Omega: the last disjunct is `continuousMapRingObj (PadicAlgCl ℓ)`.
  It includes all continuous functions; it never uses `padicAlgClRingObj`.
  The recorded `IsLocalizingAdmissibleCoefficient` now has an additional
  finite-subextension-valued case. Following the already landed sibling
  `FiniteComplexHeartFilteredApproximation`, `hΛ` spells out exactly these six
  cases instead of silently enlarging this item's coefficient class.
- A Noetherian scheme: `X : Scheme.{u}`, `[IsLocallyNoetherian X]`,
  `[CompactSpace X]`. No affine, separated, finite-type, field or characteristic
  condition is added.
- The small pro-etale site and ordinary uncompleted internal module category:
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  This is the dependency's module-object category with `Λ_X = p_X^*Λ`.
- C belongs to the full replete finite constant scalar-model constructible class:
  `hC : IsConstantModelConstructible Λ X C`, using the recorded definition
  directly. It includes finitely presented torsion models and does not require
  finite Tor amplitude or locally free scalar models.
- Every small filtered diagram of arbitrary ambient modules:
  `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]` and the unrestricted
  `M : I ⥤ Mod ...`. `[HasColimit M]` supplies the chosen colimit needed to write
  `colimit.post`; it is a computational parameter available for every such
  diagram in this Grothendieck category, not a restriction on M's terms.
- Both canonical maps are bijective: the conclusion is the conjunction of
  `IsIso (colimit.post M (preadditiveCoyoneda.obj (Opposite.op C)))` and
  `∀ c, IsIso (colimit.post M (c.yonedaExtOneFunctor C))`. An isomorphism of
  abelian groups means bijectivity on carriers, hence includes injectivity.
  `colimit.ι_post` specifies each component to be the image of `colimit.ι M i`;
  this is postcomposition for Hom and pushout for Yoneda Ext1.
- There is no hypothesis that any M_i is constructible, no cohomological-dimension
  bound, and no derived-completeness assumption.

Statement dependencies read and used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` was read along
  with its coefficient construction imports. Because its final disjunct is
  broader than this item, the exact coefficient disjunction is used as above.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt`, its `topology` and full weakly-etale signature.
- `def-weil-size-convention`: metatheoretic convention, with no declaration;
  rendered by the explicit scheme, site, abelian-group and index universes.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  its ordinary internal-module category, with `condensedRingObj` and the
  existing total derived constructions retained in the imports.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and its complete
  finite-model, finite-stratification and affine-local definitions.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, `colimit.post`, `colimit.ι_post`; filteredness
  is the existing `CategoryTheory.IsFiltered`.
- The new definition node supplies only the missing bundled Yoneda pushout
  functor. It reuses the recorded `YonedaExtension.Classes` and
  `YonedaDerivedExtComparison`, not a second extension quotient or comparison.

The main declaration docstring reproduces all seven proof steps with the named
DAG citations. Every proof dependency with a currently recorded module is imported
with plain `import`, while statement dependencies use `public import`.
The following proof nodes have no recorded module to import yet:
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`.
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
- `lem-sfb-noetherian-space-compact-subsets`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-sfb-scalar-finite-free-resolutions`.
- `lem-sfb-sheaf-cover-local-isomorphism`.
- `lem-cbc-sieve-slice-sheafification`.
- `lem-weil-pbc-ext-via-injective-resolution`.

The available proof interfaces imported are:

- `lem-sfb-module-object-ringed-site-derived-comparison`: `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`: `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, `CategoryTheory.moduleSheaves_colimits_forgetful`.
- `lem-pur-ringed-site-grothendieck-abelian`: `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`, `SheafOfModules.grothendieckAbelian_with_localized_generator`.
- `lem-sfb-finite-constant-model-two-term-free-resolution`: `Sheaf.Paper.FiniteConstantModelResolution`, `AlgebraicGeometry.ProEtale.FiniteConstantModel.finite_constant_model_two_term_free_resolution`.
- `lem-sfb-constant-finite-free-presentation-extension`: `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`, `CategoryTheory.ConstantFiniteFreePresentationExtension.constantFiniteFreePresentationExtension`.
- `lem-weil-pbc-finite-discrete-condensed-ring-constant`: `Sheaf.Paper.FiniteDiscreteCondensedRing`, `Profinite.finiteDiscreteCondensedRing_constant`.
- `lem-weil-pbc-finite-discrete-scheme-ring-constant`: `Sheaf.Paper.FiniteDiscreteSchemeRing`, `AlgebraicGeometry.ProEtale.finiteDiscreteSchemeRing_constant`.
- `def-sbc-standard-tstructure-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, `DerivedCategory.TStructure.t`.
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`: `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`, `CategoryTheory.ringedSite_boundedFree_rhom_model`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`: `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`, `CategoryTheory.RingedHomUniverses.rightShift_existsUnique`.
- `lem-weil-pbc-proetale-internal-hom-lower-bound`: `Sheaf.Algebra.Homology.ProEtaleInternalHomLowerBound`, `AlgebraicGeometry.Scheme.proEtale_internalHom_isGE`.
- `lem-sfb-rhom-continuity-triangle-closure`: `Sheaf.Algebra.Homology.RHomContinuityTriangleClosure`, `CategoryTheory.RingedHomUniverses.boundedTargetHomContinuous_triangle_closure`.
- `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`.
- `lem-sfb-open-closed-internal-hom-formulas`: `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom`, `AlgebraicGeometry.ProEtale.CondensedRing.openClosedInternalHomFormulas`.
- `lem-sfb-closed-support-bounded-continuity`: `Sheaf.Paper.ClosedSupportBoundedContinuity`, `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_bounded_continuity`.
- `lem-weil-pbc-condensed-open-closed-recollement`: `Sheaf.Paper.CondensedOpenClosedRecollement`, `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement`.
- `det-lem-formal-closed-support-adjunction`: `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`, `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_triangle`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`: `Mathlib.CategoryTheory.Adjunction.Limits`, `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`.
- `lem-sfb-rhom-continuity-open-extension`: `Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek_rhom_continuity`.
- `lem-sfb-bounded-finite-model-generation`: `Sheaf.Paper.BoundedFiniteModelGeneration`, `AlgebraicGeometry.ProEtale.CondensedRing.bounded_finiteModel_generation`.
- `det-pe-bounded-continuity-sections`: `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`, `AlgebraicGeometry.Scheme.ProEt.isIso_ringHypercohomology_colimitPost`.
- `lem-pur-rhom-global-sections`: `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`, `CategoryTheory.rhom_global_sectionsOfUniverses`.
- `lem-coef-yoneda-derived-ext-comparison`: `Sheaf.CategoryTheory.YonedaDerivedExtComparison`, `CategoryTheory.nonempty_yonedaDerivedExtComparison`.
- `lem-weil-pbc-complex-injective-resolution-mono`: `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`, `CochainComplex.exists_mono_quasiIso_injective_boundedBelow`.

Edge cases checked before drafting: X empty (both Hom and extension groups vanish);
C = 0; the zero diagram; constant filtered diagrams; the zero coefficient ring
(the exponent n = 0 forces precisely that ring); scalar model of rank zero;
O_E/(pi^m), including m = 0; and A = F_ell[epsilon]/(epsilon^2) with C = A/(epsilon).
The last case may have infinite projective dimension, so neither statement nor
helper has a finite-free-resolution or finite-Tor-dimension hypothesis. The
accepted proof uses finite initial resolution segments and finite Hom diagonals.
Filtered categories are nonempty by `IsFiltered`; no unintended empty-index case
is omitted. The Omega case is continuous functions with unrestricted image in
the algebraic closure; no identification with a colimit of coefficient subrings
is used. There is no STATEMENT-DISPUTED finding or statement correction.

Searches actually run using msearch.py:

- leanfinder: `Hom and Yoneda Ext one from constructible pro etale module sheaves on a Noetherian scheme commute with filtered colimits`: 8 hits, `LightCondensed.ihomPoints_apply`, `SheafOfModules.Presentation.map_π_eq`, `LightCondensed.lanPresheafExt_hom`, `LightCondensed.ihomPoints_symm_apply`, `LightCondMod.hom_naturality_apply`, `Condensed.lanPresheafExt_hom`, `CondensedMod.IsSolid.isIso_solidification_map`, `AlgebraicGeometry.Scheme.LocalRepresentability.yonedaGluedToSheaf_app_comp`.
- loogle: `CategoryTheory.Abelian.Ext, CategoryTheory.IsFiltered`: 0 hits, .
- grep: `Ext.*colim|Ext.*filtered|[Cc]onstructible.*Ext`: 25 hits, `Mathlib/FieldTheory/CardinalEmb.lean`, `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`, `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`, `Mathlib/CategoryTheory/ObjectProperty/Local.lean`, `Mathlib/CategoryTheory/ObjectProperty/FiniteProducts.lean`, `Mathlib/CategoryTheory/ObjectProperty/ColimitsOfShape.lean`, `Mathlib/CategoryTheory/GradedObject/Monoidal.lean`, `Mathlib/CategoryTheory/GradedObject/Trifunctor.lean`.
- leansearch: `Functor of Yoneda Ext one classes by pushout in the second argument`: 8 hits, `CategoryTheory.Abelian.extFunctor`, `CategoryTheory.Abelian.extFunctorObj`, `Ext`, `CategoryTheory.Functor.PushoutObjObj.ctorIdx`, `CategoryTheory.Under.pushout`, `CategoryTheory.Functor.PushoutObjObj.mk`, `CategoryTheory.Functor.PushoutObjObj.pt`, `CategoryTheory.Abelian.extFunctor_map_app`.
- leanfinder: `Yoneda extension classes pushout covariant functor`: 8 hits, `CategoryTheory.Presheaf.uniqueExtensionAlongYoneda`, `CategoryTheory.SmallObject.ιFunctorObj_extension'`, `CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap`, `CategoryTheory.Presheaf.uniqueExtensionAlongULiftYoneda`, `CategoryTheory.OverPresheafAux.YonedaCollection.map₂`, `CategoryTheory.Presheaf.instUniqueHomLeftExtensionOppositeOpObjFunctorTypeYonedaMkYonedaMap`, `CategoryTheory.OverPresheafAux.MakesOverArrow`, `CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeUliftYonedaUliftYonedaMap`.
- grep: `YonedaExtension|yonedaExt|Yoneda.*pushout`: 2 hits, `Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`, `Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean`.
- leansearch: `Functor of Yoneda Ext one classes by pushout in the second argument`: 8 hits, `CategoryTheory.Abelian.extFunctor`, `CategoryTheory.Abelian.extFunctorObj`, `Ext`, `CategoryTheory.Functor.PushoutObjObj.ctorIdx`, `CategoryTheory.Under.pushout`, `CategoryTheory.Functor.PushoutObjObj.mk`, `CategoryTheory.Functor.PushoutObjObj.pt`, `CategoryTheory.Abelian.extFunctor_map_app`.

The whole-item searches found only generic finite presentation, condensed objects,
and Ext/colimit infrastructure, not this six-coefficient assertion. Source `rg`
searches covered the item id, scalar-model constructibility, Ext continuity, and
`yonedaExtOneFunctor` across `lean/WeilConjectures`, `lean/Sheaf` and Mathlib.
`IntegralExtHomContinuity` has extra finite-type/field and coefficient conditions;
it is not a match. No declaration was reattached merely on the strength of its
name. The exact requested item-id grep in upstream returned no match.

## New nodes

`def-sfb-yoneda-ext-one-functor` in the item's chapter supplies the missing bundled
covariant functor on the already existing Yoneda quotient. Its source is Stacks
06XU--06XV, endpoint functoriality, and Homology 010I, Baer sum. The theorem
`nonempty_yonedaDerivedExtComparison` already supplies the canonically normalized
comparison; the new functor takes those existing data as a parameter. Its objects
and additive arrows are real constructions. Its named identity and composition
laws are the only postponed structural proofs, explicitly included in the node's
statement with full natural-language proof docstrings. No new comparison or
quotient is defined. `ComplexExtDiskSphere.mapOne` is the existing unbundled
endpoint action; it does not supply this additive functor required by
`colimit.post`. The new bundled action uses the same normalized conjugation,
specialized to the fixed right endpoint, with no bare Nonempty choice.

The LeanSearch, LeanFinder and Mathlib grep queries and actual returned names are
in the new node's `mathlib_searches`, copied from the original search log.
DAG grep and `tools/blueprint_refs.py search 'Yoneda extension functor'` found no
existing bundled functor node (zero blueprint matches). The existing quotient and
comparison nodes are reused as statement dependencies. `blueprint_refs.py ancestor`
gave `det-sf-comp-coherence-cocycle`; its refinement proof (2) is the recorded
ancestor. The item gains only this definition node in `stmt_deps`. Every other
field outside `lean` is preserved.

## Validation

Both delivered files were compiled separately in dependency order by the prescribed
scompile.py against the live published server library, including their actual
module headers and visibility. The final run passed without errors or warnings
apart from the permitted sorry declarations. No local or global build was run.
The new helper passed artifact compilation in 3.6 seconds and the main statement
in 6.6 seconds, within the standard 60-second limit.

There is no independent worker second reading: the dispatcher's direct-delivery
instruction assigns the independent reading to the maintainer. This report does
not claim one was performed by another agent.

The server preflight requires the standard new-node `import_flags` field in addition
to the standing brief's listed fields. The new definition supplies `import_flags: []`;
there are no imported-statement flags. No maintainer review metadata was added.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
