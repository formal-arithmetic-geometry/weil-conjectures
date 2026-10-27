## Worker report

The module `Sheaf.Paper.StrictCompletionRestrictionComparison` states
`AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strict_completion_restriction_comparison`.
Its only postponed proof is that theorem. `Presentation`, `Comparison`, `IsIntegral`, `SectionReductionModels` and
`IsSectionIntegral` package this node's simultaneous assertions with explicit equations;
they do not construct a second cone, Roos functor, coefficient ring, or completion.
The real-data instance `smallSiteLocalEquivalences` specializes the already existing
`surjectiveTower_wEqualsLocallyBijective.{u, 0}` to `AddCommGrpCat.{u+1}`. This resolves
an unconstrained auxiliary universe in instance search without equating the site
object and morphism universes or adding a hypothesis.

### Hypotheses and clause correspondence

- The fixed prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`, bound before the theorem. The integral ring,
  topology, and uniformizer are the recorded `DerivedNakayama.integerRing l E`
  and `Padic.coefficientExtensionUniformizer l E`. In particular these are the
  continuous condensed coefficients, not discrete constant coefficients.
- Schemes have universe `Scheme.{u}`. `AdicCompletion.Modules l E X` is the
  internal module category over the prescribed pullback coefficient ring.
  Its module-object universe is `u+2`, morphisms and derived-category universe
  are `u+1`. `CochainComplex ... ℤ` and `DerivedCategory` are unbounded;
  no boundedness, quasi-compactness, Noetherianity, or invertibility is assumed.
- The family `S` supplies the completion simultaneously on all schemes.
  `∀ X, IsIntegral l E X (S X)` fixes its scalar and its tower to the
  dependency's canonical `PrincipalReductionConeData` and actual
  `CompletionTriangle.tower`. The reductions are exactly
  `PrincipalReduction.reductionFunctor l E X n`, i.e. derived quotient extension
  followed by scalar restriction. `IsIntegral` identifies the reduction unit
  with `Mod.derivedExtendMapDerivedCategoryAdjunction` and the transition with
  `AdicCompletion.integralStep`. `HEq` here accommodates the displayed equality
  of the functors; it does not replace an isomorphism assertion by mere existence.
- The specified completion and its unit are fixed in `IsIntegral` for every
  K-flat representative `P` and every representative isomorphism `e`: an
  isomorphism to `Q.obj (AdicCompletion.roos l E X P)` must carry `S.unit` to
  `AdicCompletion.completionMap l E X K P e`. Thus the existential presentation
  is constrained by the actual canonical map, not just an arbitrary derived
  limit triangle. `Presentation.descent` and `unit_descent` are natural descent
  data for the actual strict cone/Roos tower on all complexes.
- Section action is the dependency's actual
  `(ModuleObjectRingedComparison.equivalence ... X).functor`. Its local-model
  iff now has the independent section predicate
  `HasSectionFiniteConstantLocalModel l E X (E_X.obj M)` on the right. Each
  chart uses `InternalModuleOperations.upperStar` (presheaf ringed pullback
  followed by sheafification). A section model is `cokernel f` for a matrix
  between finite biproducts of the actual section-ring regular module. Every
  matrix component on every section is multiplication by
  `sectionScalarValue ... (a j k) U`. Each `a j k` is an endomorphism of the
  regular condensed module on the point, hence a scalar in A, pulled back
  before evaluation. Arbitrary varying local coefficient matrices are excluded.
  There is no equivalence applied to either object in the chart isomorphism.
- The section completion conjunct requires `IsSectionIntegral l E X T` in
  addition to `Comparison E_X (S X) T`. Its scalar is multiplication on every
  section by the canonical uniformizer. Its algebra tower `B` has objects equal
  to `sectionRingSheaf (finiteRing ... n)`, algebra maps heterogeneously equal
  to `sectionScalarMap (quotient ... n)` and transitions equal to
  `sectionScalarMap (transition ... n)`. These are the actual quotient rings,
  not arbitrary transported endofunctors. The heterogeneous equalities only
  transport the explicitly displayed equalities of their endpoints.
- `SectionReductionModels.tensor` identifies `T.reduction n` naturally with
  the actual section derived tensor with k_n in degree zero. The closed tensor
  structure `H` and K-flat models `HM` have the dependency's
  `ModuleObjectRingedComparison.TensorComparison`, including its canonical
  K-flat totalization normalization. `tensor_model` fixes the reduction
  realization to `CoefficientTensorModels.iso` after any K-flat resolution
  `q : Q -> k_n[0]`: the total map `id tensor q`, followed by `single`, equals
  the derived comparison followed by the tensor of `Q(q)`. `single_values`
  pins `single` to the identity on local pure tensors, using the actual
  `coefficientTensorGenerator` and `siteSheafTensorTmul`.
- `SectionReductionModels.unit` fixes the reduction unit on every K-flat P
  to the localization of the actual section `tensorUnit`, m to m tensor 1.
  `step` fixes each transition to the actual quotient-induced
  `KFlatRoos.transition`. `IsSectionIntegral` additionally fixes completion
  on every section K-flat representative P of every K to
  `Q.obj (KFlatRoos.roos B ι P)`, carrying `T.unit` to
  `e.inv >> Q.map (KFlatRoos.augmentation B ι P)`. Thus the right-hand C and c
  of the section completion comparison have their prescribed meaning.
- `Comparison.homology` identifies all integer-degree cohomology functors;
  `homology_eq` fixes this isomorphism to
  `Functor.mapDerivedCategoryHomologyFunctorIso`. The reduction comparisons
  retain their naturality, representative equation, transition equation, and
  augmentation equation in the existing `Comparison` fields.
- `Comparison.derived` is a natural isomorphism
  `S.completion ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T.completion`.
  Its component is exactly `F(C(K)) ≅ C(F(K))`; `Comparison.unit` carries
  `F(c_K)` to `c_(F(K))`. `Comparison.representative` fixes the isomorphism on
  the strict chain model, rather than merely comparing homology groups.
- Allowed `h` satisfy the multiplicative closure of
  `IsImmersion f ∨ WeaklyEtale f`. `IsImmersion` is a locally closed immersion;
  `WeaklyEtale` is the structure map of an object of the small pro-etale site.
  Multiplicative closure includes finite composites and the identity. The
  functor is the actual `CondensedRing.upperStar` with its canonical coefficient
  coordinates; no arbitrary map or coefficient-identification parameter is
  introduced. Its existing exact/additive instances provide exact inverse
  image. The asserted `∀ I : Type (u+1), PreservesLimitsOfShape (Discrete I)`
  says exactly that all products in the stipulated coefficient universe are
  preserved. The previous stronger all-limits clause is removed.
- Strict cones have the positive exponent `n+1`: natural `n=0` is the paper's
  level 1. `Presentation.cone` fixes `Cone(π^(n+1))` and `coordinates_eq` fixes
  the dependency's target-first principal-cone coordinates. `diagonal` fixes
  maps to `(f x,f y)`, `transition` to `(x,π y)`. `augmentation_level` fixes the
  cone augmentation to `(m,0)` at every level, and `augmentation_zero` fixes
  the other Roos coordinate to zero. In the dependency's `roosχ` the shifted
  product is listed first, so these equations read `(0,((m,0))_n)`; exchanging
  the two displayed Roos factors gives exactly the node's `(((m,0))_n,0)`.
- `Comparison.tower_coordinates` fixes the cone comparison to the termwise
  map and the canonical biproduct comparison. `product_projection` characterizes
  each product comparison by every projection, `roos_map` intertwines the
  existing `roosU` (the specified `1-T`), `chain_coordinates` is diagonal on
  those product comparisons, and `chain_unit` preserves the entire explicit
  augmentation. These fields impose the node's strict normalization on both
  section action and restriction, including the zero coordinate. The derived
  representative equations retain that normalization after localization.

### Dependencies

The recorded declarations and Mathlib matches were read with their signatures and
docstrings. Statement dependencies are public imports, directly or through the
owning dependency modules; proof tools use plain imports. In addition to the primary
records below, the concrete names used are `AdicCompletion.Modules`, `quotient`,
`integralStep`, `roos`, `completionMap`; `PrincipalReductionConeData`, its
`IsCanonical`, and `reductionFunctor`; `CompletionTriangle.tower`;
`principalConeCoordinates`; `CategoryTheory.roosF`, `roosP`, `roosU`, `roosχ`,
`roosEval`; `DerivedNakayama.scalarOnModules`; `ModuleObjectRingedComparison.equivalence`
and `Modules`; `CondensedRing.upperStar`; `HasFiniteConstantLocalModel` and
`upperStarFromPoint`; and `Functor.mapDerivedCategory` with its representative
factorization. These are reused, not privately redefined.

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-size-convention` is the recorded metatheoretic convention; the module binds all universes explicitly.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `sk-def-pe-derived-completion`: `Sheaf.SixFunctors.ProEtale.DerivedCompletion`, `AlgebraicGeometry.ProEtale.IsDerivedComplete`.
- `lem-pe-completion-triangle-comparison`: `Sheaf.Paper.CompletionTriangleComparison`, `AlgebraicGeometry.ProEtale.CompletionTriangle.completion_triangle_comparison`.
- `lem-sfb-module-object-ringed-site-derived-comparison`: `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`, `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.moduleObject_ringedSite_derived_comparison`.
- `lem-pe-internal-section-tensor-comparison`: `Sheaf.CategoryTheory.InternalSectionTensorComparison`, `CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`.
- `lem-pe-principal-reduction-cone-calculus`: `Sheaf.Paper.PrincipalReductionConeCalculus`, `AlgebraicGeometry.ProEtale.PrincipalReduction.principal_reduction_cone_calculus`.
- `lem-pe-roos-cone-calculus`: `Sheaf.Algebra.Homology.RoosConeCalculus`, `CategoryTheory.RoosConeCalculus.roos_cone_calculus`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`.
- `lem-sfb-internal-module-inverse-image-comparison`: `Sheaf.CategoryTheory.InternalModuleInverseImageComparison`, `CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison`.
- `sk-def-sfb-coefficient-morphisms`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.condensedPullbackHom`.
- `lem-weil-pbc-proetale-immersion-limit-preservation`: `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, `AlgebraicGeometry.Scheme.proEtale_immersion_inverseImage_preservesLimits`.
- `lem-weil-proetale-weakly-etale-localization`: `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`.
- `lem-sfb-proetale-object-inverse-image-restriction`: `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`, `AlgebraicGeometry.Scheme.proEtaleObjectInverseImageRestriction`.
- `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`.
- `lem-weil-pbc-module-sheaves-limits-sectionwise`: Mathlib record `{"declaration": "SheafOfModules.hasLimitsOfSize", "file": "Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean", "how": "one Mathlib instance per clause, for `R : Sheaf J RingCat` and diagrams indexed by categories with objects in the universe v of the modules: existence `SheafOfModules.hasLimitsOfSize` (line 106); limit created by (and computed as) the limit in `PresheafOfModules R.obj`, `SheafOfModules.createsLimit` (line 62) and `SheafOfModules.forgetPreservesLimitsOfSize` (line 111); computed on sections, `SheafOfModules.evaluationPreservesLimitsOfSize` (line 108), with underlying abelian group the limit of abelian groups by `ModuleCat.forget₂AddCommGroup_preservesLimits` (Mathlib/Algebra/Category/ModuleCat/Limits.lean:169)"}`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `lem-sf-exact-functor-derived-triangulated`: Mathlib record `{"declaration": "CategoryTheory.Functor.mapDerivedCategory", "file": "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean", "how": "exact: `F.mapDerivedCategory` with the instances `CommShift ℤ` and `IsTriangulated`, and `F.mapDerivedCategorySingleFunctor n` for complexes concentrated in degree $n$"}`.

### Edge cases

The statement includes `n=0` (the quotient by π, not by 1), every integer cohomology
degree, arbitrary unbounded complexes, zero complexes, the empty scheme, arbitrary
non-quasi-compact complements, identity arrows and empty composites. No cover is
assumed nonempty. The quotient units and transition maps are fixed separately:
the tower alone would not fix the completion unit. The Roos coordinate ordering
was checked against `CompletionTriangle.completion_triangle_comparison`.
Product projections determine the product comparison, and cone coordinates
determine its cone extension; thus no rescaling of the augmentation is permitted.
There are no disputed statements, node corrections, new nodes, or dependency
record repairs in this delivery. The added predicates package the missing clauses
of this same node; they are listed in its `lean.declarations`.

### Searches

Search outputs are retained in the sandbox `searches.jsonl`. The required tools
were invoked via `msearch.py Q98 lem-sfb-strict-completion-restriction-comparison`.

- LeanFinder: `Exact inverse image proetale restriction preserves products derived
  completion unit strict Roos cone section module equivalence`. Eight hits were
  scalar `AdicCompletion` exactness/product lemmas, `Profinite.NobelingProof.succ_exact`
  and the de Rham period ring; none states this augmented strict comparison.
- Loogle: `PreservesLimits, mapDerivedCategory, sectionModuleEquivalence` gave an
  unknown-identifier diagnostic (not counted as a successful no-match search).
  The follow-up `CategoryTheory.Functor.mapDerivedCategory, AdicCompletion`
  returned zero hits.
- Mathlib grep: `roos.*[Cc]ompar|[Cc]ompar.*roos|map.*[Mm]apping[Cc]one`
  returned 25 generic cone/homotopy hits, not this comparison. The search
  `strict.*completion.*restriction|completion.*sectionModuleEquivalence` in
  `CategoryTheory` returned zero hits.
- Direct project searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  the item id and `strict_completion_restriction|StrictCompletionRestriction`
  found no existing statement. Related section action, principal cone, finite
  local model, and Roos searches found the dependency interfaces used above.
  Their individual theorems do not already state the simultaneous comparison
  with the specified completion unit.

### Returned-review repair, immutable head c68f1910f9f5

F1: repaired by `IsSectionIntegral` and `SectionReductionModels`. An arbitrary
transport of S no longer discharges the section conjunct: one must identify its
scalar with the section-ring uniformizer, its reductions with section derived
tensor k_n, its unit and step with the quotient tensor unit and transition, and
its completion and unit with the actual section tensor Roos model. The
K-flat `tensor_model` equation references the existing derived TensorComparison
model, and `single_values` removes scalar ambiguity at chain level.

F2: repaired by `HasSectionFiniteConstantLocalModel`: actual section inverse
image on the left, actual finite scalar-matrix cokernels on the right. The
old clause with the equivalence applied to both sides is deleted. Empty finite
ranks m=0 or n=0 are allowed, including the zero model. The finite biproduct
instance uses `HasFiniteBiproducts.of_hasFiniteProducts`, with real data.

Advisories: the preservation clause now quantifies only over discrete diagrams
(products), and `Comparison.homology_eq` selects the canonical homology iso.

Additional reused interfaces: `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
(`InternalModuleOperations.upperStar`, with its canonical coefficientMap),
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction` (`sectionScalarMap`),
`Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance` (`levelModule`, `level`,
`tensorUnit`, `transition`, `roos`, `augmentation`), and
`Sheaf.Paper.InternalSectionDerivedTensorComparison` (publicly imported through
the existing ringed comparison: `TensorComparison`, `tensorComparisonNormalized`).
No replacement tensor, inverse image or completion construction was introduced.

Repair searches: LeanFinder query "Sectionwise scalar module finite constant matrix
presentation inverse image derived reduction completion normalized K-flat tensor
comparison" returned eight generic module-presentation/flatness/tensor results,
no exact comparison. Loogle query `SheafOfModules.KFlatRoos.roos,
CategoryTheory.InternalAbelianSheafModule.sectionScalarMap` gave an unknown-name
diagnostic; it is not a no-match result. Follow-up query
`CategoryTheory.Functor.mapDerivedCategory` returned twelve generic exact-functor
results. Mathlib grep `sectionScalarMap|HasSectionFiniteConstantLocalModel|
tensorComparisonNormalized` in CategoryTheory returned zero hits. Direct project
searches found the scalar and inverse-image interfaces named above; no existing
`HasSectionFiniteConstantLocalModel`, `SectionReductionModels` or
`IsSectionIntegral` was found. All search tools were actually run.

### Validation

The delivered module was compiled using `scompile.py` against the live published
library. Both the sandbox module and its actual library module compiled without
errors or non-sorry warnings. The JSON copy changes only `lean`; its recorded
signature is copied verbatim from the theorem keyword to the assignment.
The prescribed delivery dry run supplies the final preflight and compile check.

## Second reading by Q98

The dispatched repair forbids other agents; this is my final self-check, not an
independent review. I reopened the current node and both blueprint paragraphs
(Locality and first-reduction Cones), the returned entry, and the saved module.
The dry run of the inherited packet passed mechanically but still contained F1
and F2; those were repaired as described above. Prime/finite-extension binders,
continuous coefficients, arbitrary schemes, unbounded complexes, all integer
cohomology degrees and all positive reduction levels remain. The two new section
predicates state the missing section-ring content, without hypotheses on theorem
inputs. The original internal IsIntegral and every cone/Roos normalization remain.
I checked both quotient transition and unit equations separately and checked
K-flat localization normalization against TensorComparison's source. The h
comparison still uses actual upperStar and both canonical internal completions.
Identity arrows, finite composites, empty schemes, arbitrary covers, rank-zero
models and level n=0 (exponent one) are retained. Products now have precisely the
node's meaning. The node differs from current main only in `lean`; no natural
language statement or proof route was changed. Final dry-run/compiler results
are recorded below after they complete.

### Resumed-packet validation, 2026-10-23

The saved Lean module already contains both returned-review repairs; it is retained.
The initial required dry run timed out at the unchanged 60-second limit. Diagnostic
profiling and a subsequent ordinary scompile.py run both completed. The ordinary
run compiled the sandbox module in 54.3 seconds and the actual library module in
54.6 seconds, with no errors or non-sorry warnings. The temporary profiler was used
only in diagnostics/Profile.lean and is not in the delivered module.

The inherited JSON attachment still recorded the returned, unrepaired theorem
signature. Replaced lean.statement with the exact repaired signature, updated its
UTC date, and listed all ten declarations, including sectionScalarValue,
sectionFiniteBiproducts, HasSectionFiniteConstantLocalModel, SectionReductionModels
and IsSectionIntegral. Comparison against the current shared node confirms that
only lean differs; statement, source, dependencies and proof are retained.

Final self-check against the return: F1 is the IsSectionIntegral conjunct on T,
including the actual quotient tower, uniformizer scalar, normalized section tensor,
reduction unit/step, and augmented K-flat Roos realization. F2 uses independent
section inverse image and finite scalar-matrix cokernels on the right of the iff.
There is no equivalence on both sides of the local chart isomorphism. The actual
upperStar comparison, both internal IsIntegral predicates, all strict cone/Roos
coordinates and augmentation equations are unchanged. Zero ranks, positive level
one (Lean n=0), arbitrary unbounded complexes, identity arrows and empty covers
remain admitted. The product-only assertion and canonical homology equation
address the two advisories. No new hypotheses or statement correction were needed.
