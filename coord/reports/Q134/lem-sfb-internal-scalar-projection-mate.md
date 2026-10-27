## Worker report

Repair of returned immutable head df9feef9c67d (F1–F3). The module is
`Sheaf.Paper.InternalScalarProjectionMate`, declaration
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.internal_scalar_projection_mate`.
The natural-language node statement, six proof steps and proof dependencies stay unchanged.
There is one postponed theorem and no postponed definition, auxiliary theorem or choice.
All twenty-two declarations belong to this node; their docstrings name its source and id.

### Repair of the return

F1: `ScalarProjectionSectionIdentifications a T` now names the actual section-ring
`ScalarDerivedPair`, ordinary restriction and extension identifications, derivedRestriction
and derivedExtension. The latter's source is literally `scalarProjectionExtension a T`;
no existential internalDerived functor occurs. `derivedExtension_kflat` pins this same
comparison on every flat-term K-flat representative, using the actual exact-derived
factor, the ordinary extension comparison, and the section pair's own universal counit.
`ScalarProjectionSectionTensorTransport a d h f` then relates these same identifications
to the SAME h that occurs in the final mate equation. Its k is an isomorphism between
section-ring derived extension followed by section restriction and the canonical section
K-flat tensor. The first displayed square ties k to h, derivedExtension,
derivedRestriction and tensorComparison on every derived object. The second square
identifies the specified inverse `CondensedRing.derivedPullIso` (in
`scalarProjectionSectionPull`) with `tensorPullComparison` followed by the actual
cartesian coefficient arrow. Thus the final E-applied equality has concrete named
section scalar and pullback coordinates, rather than an unrelated generic existence
predicate. All these maps remain fixed when C varies.

F2: removed `ScalarProjectionResolutionTransport`,
`ScalarProjectionGeometricTransport`, and their conjuncts. Removed the standalone
`InternalSectionScalarAdjunction` and `TensorRepresentativeCondition ... (qTensor ...)`
conclusions. The latter is a choose_spec tautology and is not useful statement content.
The already-stated exact resolution, K-injective, geometric-adjunction, unit/counit and
internalDelta normalization results are reused as proof dependencies, rather than
copied into this theorem. The new scalar identification witnesses are consumed by
the h and actual derivedPullIso squares, so they are not the previous independent
scalar-adjunction proposition with renamed existential witnesses.

F3: the three added theorem statement dependencies are replaced by definition owners
`def-sfb-section-scalar-map-data` and `def-sfb-scalar-hom-comparison-data`, together
with the already cited section-functor/derived-realization definitions. All three
theorems stay in proof_deps and are imported as proof imports. The generic adjunction
is used directly from `sk-def-sfb-module-derived-pushpull` through the typed helper
`scalarProjectionInternalAdjunction`. The regular coefficient pull uses the specified
`internalPullOplax` unit, owned by `def-pd-proetale-section-module-functors` and
identified with the ordinary scalar multiplication by the ordinary-oplax proof dependency.
No declaration from the SectionDerivedTensorNormalization theorem is used as statement
data. `def-pd-section-module-operations-data` now explicitly owns the ring, module,
equivalence and pure-tensor aliases used throughout.

### Hypothesis and clause correspondence

- Commutative condensed rings and the ring map: Λ and Λ' are sheaves on coherent
  Profinite with `MonObj` and `IsCommMonObj`; `a : Λ ⟶ Λ'` has `IsMonHom a`.
  This is the underlying-object form of the recorded `Profinite.CondensedRing`.
- Exact scalar extension on every scheme: the single family of
  `PreservesFiniteLimits (Mod.extendScalars (ProEtale.coefficientMap a T))` instances.
  Extension is already a left adjoint, hence preserves finite colimits.
- Arbitrary scheme morphism: `X Y : Scheme.{u}` and `f : X ⟶ Y`, with no geometric
  hypothesis. Small pro-etale sites have objects in u+1 and morphisms in u;
  coefficients are `Ab.{u+1}`. The section `HasDerivedCategory.{u+1}` instances
  select the usual localization size and are not finiteness assumptions.
- R_Z, S_Z and a_Z: `condensedRingObj`, `ProEtale.coefficientMap`, and
  `scalarProjectionSectionMap`; their cartesian squares are the actual
  `comapUpperStarIso`, `derivedComapUpperStarIso` and `derivedComapLowerStarIso`.
- E_Z and ordinary/unbounded derived tensor/resolutions: the recorded `equivalence`,
  `derivedFunctor`, `CondensedRing.derivedTensor`, `tensor` and `tensorComparison`.
  Paragraph two's resolution and geometric-adjunction facts are the imported
  `internal_section_tensor_comparison`, `sectionDerivedPushpullNormalization` and
  `section_derived_tensor_normalization`, used in proof steps 1 and 5; their
  statements are not duplicated as additional conjuncts. In particular the geometric
  section adjunction remains the independently derived `derivedAdjunction`.
- Paragraph two's scalar clause: the named `d : ∀ T, ScalarProjectionSectionIdentifications
  a T`. Its restriction acts identically on sections, and its extension unit equation
  pins every balanced generator because its comparison is S-linear. Derived
  restriction is localization of that ordinary identification. The extension K-flat
  square uses the actual internal functor, with no additional internal-functor witness.
- U and T: `scalarProjectionRestriction` is exact termwise comap, and
  `scalarProjectionExtension` is the specified total left derived extension. The
  section counterparts are `scalarDerivedRestriction` and `d.sectionPair.derived`.
- Tensor notation U T = S tensor: the existential ordinary e has its local s tensor m
  equation; the existential h is normalized by e using actual exact-derived factors,
  Q's lax tensor map, and `mapBifunctorSingle₁Iso`. The named k of
  `ScalarProjectionSectionTensorTransport` is its section-ring counterpart, fixed
  by the h square for every derived input, hence for every derived morphism as well.
- Canonical pullback/tensor arrow: `ScalarProjectionPullTransport` identifies
  actual internal derivedPullIso with internalDelta and the cartesian coefficient
  arrow. The second equation of `ScalarProjectionSectionTensorTransport` identifies
  that SAME derivedPullIso with the section tensor-pullback comparison. Its named
  restriction/pullback and extension/pullback arrows use d's scalar comparisons and
  the fixed geometric `derivedPullComparison`; no arbitrary lambda is supplied.
- Gamma: the first final equation identifies its S-adjunct as inverse derivedPullIso
  followed by scalar extension of the R-counit. Gamma is the original upstream
  `CondensedRing.derivedPushHom a f`, not a map defined by this desired equation.
- d U(gamma) = delta: the last equation is the unchanged, previously reviewed
  `hY.inv ≫ UY(gamma) ≫ derivedComapLowerStarIso ≫ GR(hX.hom)` equality with
  `scalarProjectionCounitMate`, after the fixed E. Delta is explicitly the
  R-adjunction transpose of internalDelta, the cartesian coefficient arrow, and
  tensor with the R-counit. The named d/k diagrams above now identify every scalar
  operation in this equation with the section operations. Internal C ranges over
  all section derived objects by the fixed derived equivalence.
- Conservativity: `scalarProjectionRestriction a Y` reflects isomorphisms;
  d.derivedRestriction and the two derived equivalences identify this with
  conservativity of section restriction.
- No properness, finite type, boundedness, or invertibility of gamma: none occurs
  in any binder or structure field. All complexes and derived objects are unbounded.

### Dependency declarations

Namespace MRC abbreviates AlgebraicGeometry.ProEtale.ModuleRingedComparison.

- `Sheaf.Paper.SectionModuleOperationsData`: MRC `ring`, `modules`, `equivalence`,
  `internalModules`, `internalPureTensor` (definition owner
  def-pd-section-module-operations-data).
- `Sheaf.Paper.ProEtaleSectionModuleFunctors`: MRC `internalPullOplax`
  (def-pd-proetale-section-module-functors).
- `Sheaf.Paper.SectionDerivedTensorData`: MRC `internalDerivedPullback`,
  `internalDerivedPushforward`, `derivedFunctor`, `tensor`, `tensorComparison`
  (def-pd-section-derived-tensor-data).
- `Sheaf.Paper.SectionDerivedRealization`: MRC `internalDelta`, `derivedPullComparison`,
  `tensorPullComparison` (def-pd-section-derived-realization).
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: InternalAbelianSheafModule
  `sectionScalarMap`, `internalScalarGenerator` (def-sfb-section-scalar-map-data).
- `Sheaf.Algebra.Homology.ScalarInternalHomData`: SheafOfModules `ScalarDerivedPair`,
  `scalarRestriction`, `scalarDerivedRestriction`, `scalarPairComplexComparison`
  (def-sfb-scalar-hom-comparison-data). The pair retains the sheafified object/map
  formulas, universal derived property, K-flat counit comparison and normalized
  ordinary/derived adjunctions; no private model replaces them.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and its upstream derived module:
  CondensedRing `derivedUpperStarLowerStarAdjunction` (sk-def-sfb-module-derived-pushpull).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `comapUpperStarIso`, `derivedComapUpperStarIso`,
  `derivedComapLowerStarIso`, `derivedPullIso`, `derivedPushHom`
  (sk-def-sfb-coefficient-change); its Basic dependency supplies `condensedRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  CondensedRing `derivedTensor`; recorded ordinary relative tensor is Mod's monoidal
  tensor, and Q is the actual derived localization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; site flatness is
  `SheafOfModules.IsFlatOnSite` from the existing FlatOnSite module, with
  its landed definition owner def-pc-flat-sheaf-modules explicitly cited.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the existing canonical
  tensor-pullback construction retained through `tensorPullComparison`.
- Mathlib/upstream exact-functor localization and BifunctorSingle:
  `leftDerivedFunctorIsoMapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategorySquareIso`, `mapHomologicalComplexCompIso`,
  `CochainComplex.mapBifunctorSingle₁Iso` and the single functors/maps.

Edge cases: a=id gives the ordinary regular-module unit and identity scalar change;
f=id gives the specified unit/counit normalization. C=0, empty schemes and zero rings
are allowed. Every comparison quantifies over arbitrary unbounded representatives,
including flat-term K-flat representatives with gaps; no boundedness, nonemptiness,
faithful scalar extension or invertible projection map is added. The K-flat premise
is on the fixed section image of P, so it neither assumes a new internal flatness
notion nor identifies site object/morphism universes. No STATEMENT-DISPUTED issue
or natural-language node correction is required.

Searches performed before writing and during the final audit:

- msearch LeanFinder: "Derived scalar extension pushforward mate equals projection
  formula after restriction of scalars and internal section module equivalence";
  8 ordinary ModuleCat change-of-scalars hits, no exact statement.
- msearch Loogle: `"SheafOfModules", "Adjunction"`; 12 ordinary free/pullback
  adjunction hits, no exact derived internal-to-section statement.
- msearch grep: `derivedPushHom|projection.*[Mm]ate|[Mm]ate.*projection`;
  no Mathlib hits.
- msearch LeanSearch: "An exact equivalence of internal sheaf modules and section
  ring modules identifies derived scalar change pushforward mates with the counit
  projection morphism"; 8 ordinary sheaf-module adjunction/section hits, no match.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for scalar/projection/mate and
  `derivedPushHom`: found the actual internal maps and the special constant-ring
  `ProEtaleScalarMateNormalization`, plus distinct scalar tensor-comparison nodes.
  None states this full condensed-ring normalization.
- Exact item-id search in the upstream Lean source found no module owning this
  node. The dependency declarations and their docstrings were read, rather than
  reconstructing their notions from names.

Additional searches during this repair:

- msearch LeanFinder, "Exact section module equivalence identifies derived extension
  of scalars and restriction with K-flat normalized tensor pullback and its projection
  mate": 8 ordinary scalar-adjunction and flatness results; no exact theorem.
- msearch Loogle, `SheafOfModules.scalarRestriction, CategoryTheory.Mod.extendScalars`:
  zero hits; the service reported unknown identifier SheafOfModules.scalarRestriction.
- msearch grep, `derivedPushHom|ScalarProjectionSection|projection.*[Mm]ate`:
  zero Mathlib hits.
- rg over the specified project Lean roots found the original upstream derivedPushHom,
  special constant-coefficient results and distinct scalar diagrams, but no theorem
  identifying these named condensed coefficient scalar/section maps.
- DAG declaration-owner search found the landed definition nodes
  def-sfb-section-scalar-map-data and def-sfb-scalar-hom-comparison-data. Reused their
  actual declarations and read their source definitions/structure fields. No new
  node, dependency replacement or duplicate scalar-module notion was needed.

Validation uses only prescribed scompile.py and deliver2.py, with the 60-second limit,
read-only published sources and no global build. The saved packet's initial dry run
failed by timeout; subsequent concrete compiler diagnostics were repaired in this packet.

## Second reading by Q134

The dispatcher requires this worker to deliver directly and forbids starting other
agents. This is the worker's self-check; the maintainer supplies the independent
second reading. Checked the node and final signatures clause by clause as above.
The original packet's detached scalar-adjunction existence statement is gone: the
witness d now has the literal scalarProjectionExtension as its derived source; its
K-flat equation uses the ordinary extension witness that also pins its balanced
unit. The same d and h enter the k square and the actual derivedPullIso square.
Checked the orientation of every inverse: restrictionPull goes from pulled-back
R-restriction to restricted S-pullback; derivedPullIso.inv goes from L_S T_Y to
T_X L_R; k.inv starts from the section tensor. The coefficient arrow has its
cartesian direction L_R(S_Y) to S_X. Gamma remains the upstream morphism and delta
remains the specified R-counit transpose. No copied K-injective/geometric normalizations
or qTensor choose_spec conjunct survives. Definition ownership and theorem proof imports
match the three findings of the return. No other node is changed.

Compiler diagnosis: explicit site/coefficient universes repaired generic scalar API inference.
The comparison-data structure locally disables only generated SizeOf specification and
constructor-injectivity lemmas, which the profiler identified as avoidable elaboration cost.
The server confirmation compiled the complete repaired module in 49.5 seconds. Temporary
profiling and #check commands were then removed before final validation.
