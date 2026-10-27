## Worker report

Repair of the immutable returned head c84077ecb51e (L, H2 stmt_deps).
The mathematically accepted Lean module from that packet is retained byte for byte.
The earlier a32dd0d66073 H3/H5 repair and its detailed statement audit are retained below.
The retained packet first passed the prescribed dry run at c5dd6c66e33.
Self-check against L's return nevertheless confirmed the missing section-side equations;
this packet replaces that statement rather than re-pushing the unchanged packet.

The module `Sheaf.Paper.InternalScalarPullbackNormalization` states
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_pullback_normalization`.
It has one theorem, whose proof is `sorry`. Eight helper declarations package comparison
data or construct canonical composites; none chooses an unspecified mathematical object
and none contains `sorry`. There are no new DAG nodes, dependency repairs or corrections
to the mathematical statement. The node changes only in `lean` and by adding already
recorded statement dependencies for the section operations now explicitly mentioned.

Hypotheses and every clause of the node:

- Arbitrary commutative condensed rings are the two arbitrary sheaves
  `Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `MonObj` and
  `IsCommMonObj`. The ring homomorphism is `a : Λ ⟶ Λ'` with `IsMonHom a`.
  This is the unbundled form of the recorded `Profinite.CondensedRing`, with no
  continuous-function presentation assumed.
- The arbitrary morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`. Its small sites are
  `Scheme.ProEt.topology X/Y`, of object universe u+1 and morphism universe u.
  Coefficients have universe u+1; no equality of these universes is imposed.
- R_T, S_T and a_T are `condensedRingObj Λ T`, `condensedRingObj Λ' T` and
  `coefficientMap a T`. `Modules`, `D`, `L`, `V`, `B₀`, `B`, `extension` and
  `compute` are the actual declarations of `InternalDerivedScalarComparisons`.
  They retain ordinary unbounded derived categories and uncompleted relative tensor.
- The two universally quantified `HasDerivedCategory` instances specify the section
  localization presentations already used by the recorded section comparisons.
  They impose no flatness, boundedness or geometric hypothesis.
- e_X and e_Y are `tX.derived`, `tY.derived`. The two `TensorNormalized` conjuncts
  state the universal computation-counit equations on every internal cochain complex.
  `TensorNormalization.ordinary_hom` fixes the balanced comparison and symmetry.
- λ is `b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X` (Lean composition order).
  `PullNormalized a f b` retains the fixed `(CondensedRing.pullIso a f).symm`,
  its actual coefficient identifications α_f and its naturality in a. The equation
  holds on every homotopy complex, including identity maps and arbitrary lifts.
- The new `sX/sY : SectionScalarComparison` each contain `pair : ScalarDerivedPair`
  for the actual reconstructed `sectionScalarMap`. Its extension has the prescribed
  sheafified tensor objects and maps, and its derived functor has the universal
  left-derived property and normalized scalar adjunction. The first conjunct of `SectionScalarNormalized`
  fixes the ordinary restriction comparison to the identity on sections;
  its second conjunct fixes the extension comparison to s tensor x on sections.
  Most importantly, `s.derived : D a T ⋙ D(E_S) ≅ D(E_R) ⋙ s.pair.derived`
  now explicitly mentions the specified D. The third conjunct of `SectionScalarNormalized` pins this very comparison
  by `compute a T P` and `scalarPairComplexComparison` on every flat-term K-flat P.
  This repairs the old existential internalDerived that was unrelated to D.
- `SectionTensorNormalized a T s t` gives an ordinary section comparison o with
  the formula s tensor x ↦ x tensor s on every sheafified local scalar-extension
  generator. Its target is `sectionPureTensor` in the actual section tensor.
  It also gives a section-derived comparison e. The representative equation uses
  `qTensor`, `scalarPairComplexComparison`, `scalarRestrictionComparison` and the
  standard `mapBifunctorSingle₂Iso`, so e is the section K-flat balanced construction,
  with no sign and with only P required K-flat. `sectionScalarCoefficient` inserts
  only the canonical exact-equivalence/localization and single-degree-zero factors.
  Finally the displayed all-M equation explicitly equates D(E_R)(t.derived) followed
  by `tensorComparison` to `sectionScalarRestriction`, s.derived and that same e.
  Thus both tX and tY, rather than an unrelated existential map, are identified.
- `SectionPullNormalized a f sX sY b` specifies the ordinary section comparison c
  as the conjugate of r, where r is identity on all sections of the actual common
  restriction/direct-image sheaf. The scalar adjunctions are the normalized ones
  in `ScalarDerivedPair`; the geometric adjunctions are `ModuleRingedComparison.adjunction`.
  This mate equation uniquely characterizes c. Units insert 1 and counits act by
  multiplication, so c sends f inverse (s tensor x) to α_S(f inverse s) tensor
  f inverse x, equivalently f inverse (x tensor s) to f inverse x tensor f inverse s.
  The α_R/α_S in these actual ringed operations come from the same pullback-from-point
  isomorphism; no new coefficient square or arbitrary inverse-image action is used.
  The next equation pins the section-derived d by the section scalar computation
  counits and Q of the termwise c on every flat-term K-flat representative.
  The last all-M equation explicitly compares D(E_SX)(b) with this very d, using
  sX.derived, sY.derived and both fixed `derivedPullComparison` maps.
  `scalarSectionPullComparison` only exposes the source of those same maps as L,
  by unfolding the scalar interface and the existing module-derived-pullback alias.
- For the geometric adjunction clause (including its independently specified Hom
  transposes, units and counits), use the recorded
  `ModuleRingedComparison.sectionDerivedPushpullNormalization` for Λ and Λ'.
  Its node `lem-pd-section-derived-pushpull-normalization` stays in proof_deps only: no
  declaration of its module occurs in the statement. This clause cites the recorded
  theorem without restating it.
  As L's correction permits, the verbatim copied conjuncts have been removed.
- Naturality is encoded by natural isomorphisms throughout. The internal universal
  equations hold on all complexes; the section comparisons are fixed on every
  flat-term K-flat representative and their conjugation identities hold on all
  derived objects. Hence the statement does not select or depend on a resolution.
  No coefficient flatness, boundedness, properness, or completion is assumed.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (unbundled form).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`, `coefficientPullbackIso`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback/Pushforward` and the actual
  `CondensedRing.derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedTensor` and `derivedHom` (relative derived tensor).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Paper.InternalDerivedScalarComparisons`: the scalar/pullback/tensor
  interface declarations listed above; none is copied or replaced.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionModuleEquivalence`, `sectionRingSheaf`.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`:
  `sectionScalarMap`, `internalScalarGenerator`; the existing generic theorem is a
  proof tool, not a standalone repeated conclusion. The definition owner is
  `def-sfb-section-scalar-map-data`, not the scalar-adjunction theorem node.
- `Sheaf.Paper.SectionModuleOperationsData` and `ProEtaleSectionModuleFunctors`:
  `ModuleRingedComparison.equivalence`, `ring`, `modules`, `pullback`, `pushforward`,
  `adjunction`, `sectionPureTensor`.
- `Sheaf.Paper.SectionDerivedRealization` (and its tensor-data import):
  `derivedEquivalence`, `tensor`, `qTensor`, `tensorComparison`,
  `sectionLocalizationComparison`, `derivedPullComparison`, `derivedPullback`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`:
  `sectionDerivedPushpullNormalization`, used for clause 7 rather than restated.
- `Sheaf.Algebra.Homology.ScalarInternalHomData`:
  `SheafOfModules.ScalarDerivedPair`, `scalarPairComplexComparison`,
  `scalarDerivedRestriction`, `scalarRestrictionComparison` (and `scalarComplex` and
  `scalarRestriction`), owned by `def-sfb-scalar-hom-comparison-data`.
- `Sheaf.Paper.SectionDerivedTensorData`:
  `ModuleRingedComparison.derivedEquivalence`, `tensor`, `tensorComparison`,
  `sectionLocalizationComparison`, `derivedPullback`, owned by
  `def-pd-section-derived-tensor-data`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, owned by `def-pc-kflat-complex`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, owned by `def-pc-flat-sheaf-modules`.
- The recorded proof-dependency imports are retained for stage 3.

Edge cases checked: a = id; S = 0 (allowed by MonObj and IsCommMonObj);
nonflat Z → Z/n (no Flat instance on a or on the restricted regular S-module);
f = id; zero complex; empty X or Y; all integer cochain degrees with no boundedness.
The section tensor computation assumes flat-term K-flatness only of the representative
P, not of the fixed coefficient complex. Ringed pullback and scalar extension preserve
the needed K-flat representatives without a flat coefficient map. Identity squares give
identity mate maps because the restriction/direct-image comparison is identity.

Searches for an existing exact statement:

- msearch `leanfinder`: `Derived extension of scalars for commutative condensed rings commutes with geometric pullback, normalized by computation counits and internal section module equivalences`. Result: 8 hits; `SheafOfModules.conjugateEquiv_pullbackComp_inv`, `SheafOfModules.pullbackComp`, `SheafOfModules.pullbackObjUnitToUnit`, `PresheafOfModules.pullbackComp`, `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, `SheafOfModules.freeFunctorCompPullbackIso`, `SheafOfModules.pullbackIso`, `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal`.
- msearch `loogle`: `Mod.extendForgetTensorObjIso, CondensedRing.pullIso, Functor.leftDerivedFunctor`. Result: 0 hits; loogle: unknown identifier 'Mod.extendForgetTensorObjIso'.
- msearch `leanfinder`: `Derived scalar extension commutes with geometric pullback and restricted extension equals derived tensor, normalized on K-flat representatives`. Result: 8 hits; `Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex`, `KaehlerDifferential.moduleBaseChange'`, `Algebra.Extension.lTensor_cotangentComplex_eq_cotangentComplexBaseChange`, `KaehlerDifferential.tensorKaehlerEquiv`, `KaehlerDifferential.tensorKaehlerEquivBase`, `KaehlerDifferential.tensorKaehlerEquiv_left_inv`, `KaehlerDifferential.cotangentComplexBaseChange`, `Algebra.IsPushout.cancelBaseChangeAux`.
- msearch `grep`: `TensorNormalized|PullNormalized|extendForgetTensorObjIso`. Result: 0 hits.
- msearch `loogle`: `SheafOfModules.pullbackComp`. Result: 5 hits; `SheafOfModules.pullbackComp`, `SheafOfModules.pullback_comp_id`, `SheafOfModules.pullback_id_comp`, `SheafOfModules.pullback_assoc`, `SheafOfModules.conjugateEquiv_pullbackComp_inv`.
- `rg` of project `lean/Sheaf` and `lean/WeilConjectures` for
  `TensorNormalized|PullNormalized|internalScalarPullbackNormalization` found the
  comparison definitions and the integral quotient specialization, but no general
  normalized scalar/pullback existence theorem. The exact snake-case proposed
  declaration name also had no match in Mathlib or either project source tree.
- Search of `lean/WeilConjectures` for this blueprint id found no declaration.
  The existing `CondensedRing.derivedPullIso` is constructed in a section with
  a flat coefficient restriction; it does not provide this general nonflat
  normalized assertion and does not replace the new statement.


Additional repair searches:

- `rg` in both live `lean/Sheaf` and `lean/WeilConjectures` for
  `SectionScalarComparison|SectionTensorNormalized|SectionPullNormalized` and the
  three canonical-composite helper names: no matching normalization interface exists.
- msearch loogle `"conjugateEquiv"`: 12 hits including
  `CategoryTheory.conjugateEquiv : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`.
  This is used directly for the canonical ordinary section map; it fixes the inverse
  direction of c and the direction of the identity right-adjoint square.
- Read the existing exact-equivalence and single-factor APIs, including
  `Functor.mapCochainComplexSingleFunctor` and
  `CochainComplex.mapBifunctorSingle₂Iso`; no replacement constructions are introduced.

No STATEMENT-DISPUTED issue or mathematical statement correction was found.

## Repair self-check by Q14

I reopened the node and the complete changed signature after the initial dry run.
The returned H3/H5 gap was real: neither the old scalar-adjunction predicates nor the
old tensor-representative predicates constrained the chosen D, tX, tY or b. They are
removed. The replacement explicitly identifies D with pair.derived by its counits,
identifies tX and tY with generator-normalized section tensor maps by conjugation,
and identifies b with the representative-normalized section scalar/pullback map by
conjugation. The ordinary pullback map is uniquely pinned by the identity restriction/
direct-image square and the actual normalized adjunctions. Clause 7 is cited as the
existing pushpull node in proof_deps, instead of copied as six conjuncts.
The data-only `SectionScalarComparison` is accompanied by
`SectionScalarNormalized a X sX` and `SectionScalarNormalized a Y sY` as actual
conjuncts of the theorem, so its generator/counit equations are required, not assumed.
Every new helper belongs to this same comparison and is recorded in lean.declarations.
No generic operation is duplicated, and no universal normalization is replaced by a
mere Nonempty isomorphism. This is a self-check; no other agent was started, as required
by the dispatch brief. The maintainer supplies the independent reading.

Validation: only scompile.py was used. Elaboration diagnostics led to explicit
site/coefficient/localization universe arguments and an exact alias for the fixed
geometric comparison; the object and morphism universes were preserved. Separating
scalar comparison data from its normalization proposition avoids a large dependent
structure recursor. The ordinary unused-variable linter is disabled, as the imported
section normalization interfaces do for these large types; autoImplicit remains false,
and every binder was checked explicitly. Diagnostic #check/profiler commands and
experimental heartbeat settings were removed. The final self-check verifies one named
theorem sorry, no sorry in data, all lines at most 100 characters, and the exact signature
in lean.statement. Server compilation of the repaired interface passed within the
unchanged 60-second limit before the diagnostic cleanup. The final clean scompile.py
run passed both the sandbox compile (37.1 s) and library-artifact compile (29.9 s),
with no errors or unexpected warnings.


## Returned H2 repair: c84077ecb51e

The required saved-packet dry run passed at 09a2cf0be90. I then checked each
numbered return point against the current main node and the retained module:

1. Replaced `lem-sfb-internal-section-scalar-adjunction` in stmt_deps by
   `def-sfb-section-scalar-map-data`. The module uses its owned definitions
   `sectionScalarMap` and `internalScalarGenerator`; the theorem remains a proof
   dependency. The existing:true definition record landed on 2026-10-21.
2. Removed `lem-pd-section-derived-pushpull-normalization` from stmt_deps and
   retained it, unchanged, in proof_deps. The geometric-adjunction clause invokes
   that existing theorem as a proof tool; its declaration is absent from the Lean
   signature and helper definitions. No extra conclusion was added.
3. Added the missing definition owners `def-sfb-scalar-hom-comparison-data`,
   `def-pd-section-derived-tensor-data`, `def-pc-kflat-complex`, and
   `def-pc-flat-sheaf-modules`. The declaration-to-owner mapping is listed above.
   I read each recorded definition's full signature and docstring in live source.

The Lean module is unchanged (SHA256
`bbc5620076d595b6badf2ad8eff4f803c357575bef9acc81f74ff2a757d8112f`).
Relative to current main, only lean and stmt_deps differ; stmt_deps only gains
eight already landed nodes. Both theorem nodes removed from the saved packet
were saved-packet additions, so no current-main dependency is removed. The node's
statement, proof, proof_deps and all other fields remain identical to main.
There is no mathematical statement correction, new node, or dependency module.
The wrapper refreshes and rebases delivery bookkeeping; no direct Git command
was run in the shared repository.

## Repair self-check by Q14: H2 ownership

I reopened the unchanged theorem and all eight helpers, and checked every requested
owner against its recorded declaration. SectionScalarComparison uses the actual
sectionScalarMap and ScalarDerivedPair. The scalar counit and restriction equations
use scalarPairComplexComparison, scalarDerivedRestriction and
scalarRestrictionComparison. The tensor and pullback conjugation equations use
derivedEquivalence, tensor, tensorComparison, sectionLocalizationComparison and
derivedPullback. Their representative quantifiers use IsKFlatIndependentCoefficients
and IsFlatOnSite. These occurrences account for the five added/replacement owners.
The two theorem nodes are used for proofs only. The prior hypothesis/clause and
edge-case audit remains applicable because the module has not changed. No other
agent was started; the maintainer provides the independent reading.

Current H2 repair validation (2026-10-22 UTC): scompile.py passed the unchanged
module as sandbox Sheaf.Stage2.Sandbox0 (34.5 s) and as its library artifact
Sheaf.Paper.InternalScalarPullbackNormalization (37.0 s), with no errors or
unexpected warnings. The local read-only self-check passed the exact module hash,
verbatim lean.statement, one named theorem sorry, 100-character line widths,
autoImplicit false, JSON layout, all three requested dependency corrections,
and the current-main field boundaries.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
