## Worker report

The module `Sheaf.Paper.PointDerivedTensorTowerCoherence` states
`WeilConjectures.point_derived_tensor_tower_coherence`, with its entire proof `sorry`.
All other declarations are real transparent aliases, instance witnesses obtained from
recorded constructions, or structures/predicates spelling out this node's assertion.
No existing source file is changed. The item JSON changes only in `lean`.
There is no statement correction, disputed assertion, new independent notion or
unusable dependency interface.

Sources read: Stacks `sites-cohomology.tex`, `lemma-pullback-K-flat` (0G7E,
lines 3508ff) and `lemma-derived-pullback-composition` (0D6D, lines 3658ff);
the current blueprint `def-weil-finite-coefficient-point.md`, final paragraph;
the item's eight proof steps and every statement-dependency statement and Lean record.
The theorem docstring carries all eight proof steps, including both balance checks,
the K-flat pullback specialization, the localization argument, the roof calculation,
the identity computation and the four-field product.

Hypotheses and objects, clause by clause:

* The global finite-field datum is `D : FiniteFieldDatum.{t}`. The characteristic
  restriction is `[Fact l.Prime] (_hl : l ≠ D.p)`.
* The fixed algebraic closure is `Ω : Type u` with `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`.
* `PointTensorTower.Fields l Ω` is the subtype of the existing
  `IntermediateField ℚ_[l] Ω` satisfying `FiniteDimensional ℚ_[l] E`.
  Every pair/triple/quadruple is quantified, with weak inclusions `h`, `g`, `j`.
  This is one coherent family of all the towers in the statement, and includes
  repeated fields. The inclusion is exactly `IntermediateField.inclusion`.
* `integers E` is `Padic.coefficientExtensionIntegers l E.1`.
  The scheme is always `Spec (.of D.k)`.
  `modules`, `complexes`, `scalar`, `scalarC`, `scalarD`, `tensor` are transparent
  abbreviations for the published module category, unbounded cochain complexes,
  ordinary sheaf change of rings, its termwise extension, its prescribed ordinary
  K-flat left derived functor and module extension of scalars, respectively.
  In particular `scalarD` is `completedDerivedScalarExtension`, whose name refers
  to the coefficient sheaf and does not apply derived completion.
* `Comparisons.finite` and `.derived` reuse the dependency structures
  `PointFiniteFreeSectionsTensorData` and `PointDerivedSectionsTensorData` for
  every coefficient inclusion. Their existence is part of the theorem, not a
  hypothesis added to it. All their normalization conditions remain in force.
  `sections` uses the identity pair's coefficient identification at each field,
  so its intermediate coefficient action is literally shared between tower legs.
  `theta_normalized` and `thetaD_normalized` identify our maps with the dependency
  maps by `HEq`. This only transports the normalized section-ring identifications:
  each dependency's `constantE` and `constantL` determine those equivalences uniquely.
* `moduleDerived` selects `HasDerivedCategory.standard`, with independently sized
  coefficient and module types. Site size is unchanged: objects in `Type (t+1)`,
  morphisms in `Type t`; coefficients/modules use `max u (t+1)`. No equation between
  `t` and `u`, boundedness, completeness or constructibility is assumed.

Conclusions, clause by clause (names below are in `PointTensorTower`):

* `Maps.sheafComp` and `moduleComp` are natural isomorphisms from successive ordinary
  extensions to direct extension. `OrdinaryLaws.sheaf_formula` says, on every site
  object U and every sheaf F, that the sheafified nested generator maps to the
  direct generator with coefficient `(coefficient k g U a) * b`.
  `sheaf_inverse` fixes its inverse by inserting 1 in the inner factor.
  `module_formula` and `module_inverse` state the identical module formulas.
  The API's tensor notation puts the scalar first: `b tensor (a tensor n)` is
  the node's `((n tensor a) tensor b)`. The coefficient product is mapped into
  the largest ring before multiplication. `generator` is exactly the published
  `completedScalarTensorSection`; it is not a new tensor operation.
* `Maps.alpha` is the canonical ordinary derived scalar associator, as a natural
  isomorphism of the actual derived functors, rather than a per-degree comparison.
  `DerivedLaws.representative` fixes it through the prescribed scalar counits and
  the termwise sheafComp, for EVERY complex. On a flat-term K-flat representative
  the counits are invertible, so this is precisely the asserted representative
  of alpha; inversion of this equation gives its stated inverse representative.
  `module_representative` fixes `alphaMod` by the exact-functor factorization
  isomorphisms and the termwise moduleComp. No arbitrary derived associator is used.
* `OrdinaryLaws.square` is the displayed sections equation before localization,
  written in Lean's left-to-right composition order. `ChainLaws.square` writes
  the same equation in every integer degree of every unbounded complex. These
  are exactly the components of the termwise natural chain maps, so the component
  equations express equality of cochain maps.
  `DerivedLaws.derived_square` is exactly the displayed derived equation:
  `(theta12 tensor 1) ≫ theta23 ≫ Gamma(alpha) = alphaMod ≫ theta13`.
  Its K ranges over all derived objects, and the intermediate A is literally
  `(scalarD k h).obj K`.
* The common section formula is retained by `theta_normalized`, the dependency's
  `comparison_tensor`, `module_formula`, and `square`: their lower route is
  exactly `n tensor ab` mapped to that sheaf section. Applying these formulas
  in every degree gives the cochain version as well. No claim that all sections
  of a sheaf tensor are globally pure is made.
* `PreservesModels` quantifies over every P which is
  `IsKFlatIndependentCoefficients` with every term `IsFlatOnSite` over R_E.
  It concludes K-flatness and flat terms after scalar extension to R_L and
  invertibility of the specified derived counit at P. Together with the
  dependency's quasi-isomorphism preservation this identifies that complex with A.
* Every comparison in `Maps` is a NATURAL isomorphism. Thus naturality quantifies
  over every morphism of the derived category, including arbitrary roofs;
  it is not restricted to chain maps between chosen resolutions.
* `sheafUnit`, `moduleUnit`, `sheaf_unit_formula`, `module_unit_formula` specify
  multiplication `x tensor r ↦ rx` on sheaves and modules. `unit_square` is its
  sections compatibility. `ChainLaws.unit` is the unbounded cochain equation.
  `unitD`, `moduleUnitD` and the two unit representative equations specify their
  descents. `derived_unit_square` intertwines the stipulated thetaD at E/E.
* `OrdinaryLaws.sheaf_tower` and `.module_tower` state equality of the two
  four-field associations; `DerivedLaws.derived_tower` and
  `.derived_module_tower` state those equations in derived categories.
  Applying `NatIso.mapHomologicalComplex` to the ordinary equalities supplies
  the cochain equalities. Repeated application of `square` (or `derived_square`)
  makes every iterated sections comparison compatible with those associations.
  The explicit two-factor formulas then give `n tensor abc` on a three-factor
  generator, with the images of a and b taken in the largest coefficient ring.
* The theorem asserts `∃! C` satisfying these normalization and coherence laws,
  after choosing the dependency witnesses B. This spells out the canonical
  nature/resolution independence already in the node. The representative
  equations hold for every C, so every resolution computes this unique family;
  no choices of resolutions are made in any definition. Basis choices in B
  do not change normalized coefficient identifications or comparison maps.
* No completion comparison or integral scalar-extension functor occurs in any
  conclusion. Only ordinary change of rings and its ordinary left derived
  functor are used.

Dependency declarations used (source files and full signatures/docstrings read):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its field
  and algebraic-closure instances.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` import: `Padic.coefficientExtensionIntegers`, the
  finite-dimensional coefficient convention, and quotient data unchanged.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its imports:
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCoefficientSheafUnrestricted`, the normalized constant
  section maps. These retain independent site and coefficient universes.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the exact `SheafOfModules` category used by `integralTowerModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem,
  including its ordinary-functor prescriptions, universal counit and K-flat
  computation. The specialized functors/counits are the published
  `completedOrdinaryScalarExtension`, `completedOrdinaryScalarComplex`,
  `completedDerivedScalarExtension`, `completedScalarCounit`, reexported by
  the sections-descent dependency. None is reconstructed in this delivery.
* `Sheaf.Paper.PointDerivedSectionsTensorDescent`:
  `WeilConjectures.PointDerivedSectionsTensorData` and
  `point_derived_sections_tensor_descent`, including exactness witnesses,
  the comparison counit, theta normalization, resolution and roof clauses.
* `Sheaf.Paper.PointFiniteFreeSectionsTensor`:
  `pointFiniteFreeEvaluation`, `pointFiniteFreeModuleTensor`,
  `PointFiniteFreeSectionsTensorData`, `point_finite_free_sections_tensor`.
  The normalized constant identifications, comparison_tensor, comparison_unique
  and complexes_hom clauses are retained through Comparisons.finite.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, used with the original R and site explicitly.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the recorded sheafified tensor
  infrastructure, without a duplicate tensor product.
* Proof-only imports: `Sheaf.Paper.KFlatRingedToposPullback`
  (`SheafOfModules.isKFlat_ringedToposPullback`),
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`),
  `Mathlib.CategoryTheory.Sites.Sheafification` (`presheafToSheaf`, `toSheafify`),
  `Mathlib.CategoryTheory.Localization.Predicate` (`Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`). These are the item's proof plan.

Edge cases checked before stating:

* E=L=M=H and identity stages are permitted by weak inclusions; insertion of 1
  and multiplication reduce to the unit formulas, not an excluded case.
* Zero complex, zero sheaf, and modules in one arbitrary integer degree: formulas
  preserve zero and the generator equations still apply.
* Arbitrary ramification: only finite extension of Q_l is required; no unramified
  or etale coefficient hypothesis has been introduced.
* Unbounded complexes in both directions: no index bounds or t-structure
  truncations appear. Coefficients are in degree zero, so the associator has no sign.
* Different site/coefficient universes are retained, including t smaller or larger
  than u. Standard module localizations are chosen in their natural size; this
  selects a presentation of D without equating site and coefficient universes.
* No enumeration/basis assumption is put on sections of a general sheaf tensor.
  Formula fields quantify over pre-sheafification generators at every U.

Searches actually run:

* msearch.py leanfinder: `Canonical ordinary derived scalar extension associators
  compatible with point global sections tensor tower unit and composition`.
  Eight hits, including `ModuleCat.extendScalars_assoc'`,
  `ModuleCat.extendScalars_assoc_assoc`, `ModuleCat.extendScalars_assoc` in
  Mathlib/Algebra/Category/ModuleCat/ChangeOfRings, and scheme module pullback
  pseudofunctor coherence. These give ordinary module/sheaf analogues, not the
  prescribed completed-coefficient point sections comparison and its descent.
  Read the Mathlib extendScalarsComp and extendScalarsId signatures and formulas.
* msearch.py loogle: `TensorProduct.assoc, ModuleCat.extendScalars`.
  Successful service response, zero hits.
* msearch.py grep: `extendScalars.*(assoc|[Cc]omp)|[Ss]calar.*[Aa]ssoc`.
  Successful service response, 25 hits; mostly scalar-tower algebra/localization
  facts, no statement of this item.
* Local rg over lean/Sheaf and lean/WeilConjectures for
  `tensor.*[Tt]ower|[Tt]ower.*[Cc]oher|[Pp]oint[Dd]erived|pointDerived|derivedSectionsTensor`.
  Read the point descent and finite-free modules. Also read
  FlatScalarTowerCoherence (Mod sheaf module objects, another formalism) and
  ScalarExtensionTowerCoherence (strict finite quotient systems and completion);
  neither states this ordinary point-sections assertion. The existing generic
  notions are used through the recorded dependencies instead of redeclared.
* rg and grep -rn for this node id in lean/WeilConjectures, plus the upstream
  declaration index: no existing match for this newly split node.

Compilation uses scompile.py only. During elaboration, explicit module universes,
explicit nested module tensor target types, and a scalar additivity reexport were
needed. Splitting one large dependent record into Maps, OrdinaryLaws, DerivedLaws
and ChainLaws, and disabling unneeded generated injectivity/size lemmas, fixes its
elaboration cost without changing the assertion or increasing the wall-time limit.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
