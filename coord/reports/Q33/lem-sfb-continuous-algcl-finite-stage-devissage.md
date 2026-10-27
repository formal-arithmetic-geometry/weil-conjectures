## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_finite_stage_devissage`
in `Sheaf.Paper.ContinuousAlgClFiniteStageDevissage`. Its only postponed proof is that
named theorem, with the seven-step DAG proof transcribed into its docstring.
The item node is unchanged outside `lean`. No new nodes or dependency rebindings.
The prior worker's objection concerned a stage-1 split: the live node has reviewed PASS
for stage 1 but no Lean record, so stage 2 is still required.

The auxiliary definitions package this item's witnesses and actual canonical arrows;
they do not replace any dependency notion. `ContinuousAlgClFiniteStageDevissage` is an
existential predicate, not a choice of data from an unproved existence assertion.
All helper data are explicit compositions of published functors and morphisms.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]` and Mathlib's `ℚ_[ℓ]`.
- The algebraic closure with extended norm topology: `(Ω : Type u) [NormedField Ω]`,
  `[NormedAlgebra ℚ_[ℓ] Ω]`, `[IsAlgClosure ℚ_[ℓ] Ω]`. Completeness of Ω is not assumed.
- The field k of positive characteristic p unequal to ell: `[Field k]`,
  `[Fact (ringChar k).Prime]`, `[Fact (ringChar k ≠ ℓ)]`. A field's positive
  characteristic is prime, so this expresses exactly p>0 rather than imposing an extra case.
- Separated finite type schemes over k: `S.Over`, `T.Over`, and the three properties
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of their structure morphisms.
- A constructible locally closed k-immersion: `(a : S ⟶ T)`, `a.IsOver`,
  `IsImmersion a`, and `ha : Topology.IsConstructible (Set.range a)`.
- Internal B_S-module L: `Mod (Sheaf ... Ab) (condensedRingObj ... S)`;
  `hL : IsLisseCoefficientModule ... L` is the recorded local finite-free definition.
- B(P)=C(P,Ω) with ALL continuous maps: the existing `continuousCoefficientRingObj Ω`
  has exactly this presheaf and is definitionally the recorded
  `continuousMapRingObjOfUniverse` at common universe u. No finite-valued-function ring.
- A_E(P)=C(P,E): the same existing construction on `E : IntermediateField ℚ_[ℓ] Ω`,
  with the inherited subtype norm and topology. `finiteStageFieldMap` is postcomposition
  by `algebraMap E Ω` via `continuousMapRingSheafMapOfUniverse`; `coefficientMap`
  pulls this exact morphism to each scheme. `finite_fields` is expressed by
  `∀ t, FiniteDimensional ℚ_[ℓ] (E t)` in the existential predicate.
- A finite partition with actual scheme immersions: `P : S.FiniteLocallyClosedStratification`.
  This gives `Fin P.n`, its locally closed disjoint subsets covering S, domains and immersions.
  The first conjunct imposes constructibility. The next conjunct says every closure is a
  union of strata, exactly goodness. `IsEmpty S → P.n = 0` enforces the empty partition.
- Exact support extensions a_! and b_t!: witnesses `j,hj,i` and `v,hv,c` are
  open-then-closed factorizations, with their closed-immersion and composition conditions.
  `finiteStageSupportExtension` is literally `openImmersionLowerShriek ⋙ lowerStar`.
  These factorizations exist for the quasi-compact immersions in question; they are
  conclusion data, not extra hypotheses. The partition's maps compose with a and therefore
  inherit their k-structures. No arbitrary extension functors are quantified.
- The lisse finite-field modules N_t: the existential family `N` has precisely the
  internal A_{E_t,V_t}-module types, and its first conjunct is the recorded lisse predicate.
- Ordinary model isomorphisms: the following `Nonempty (... ≅ ...)` compares
  `(Mod.extendScalars (coefficientMap ...)).obj (N t)` with
  `(upperStar B (P.immersion t)).obj L`. Reversing the direction of an isomorphism
  changes no assertion.
- C_t=(a_!b_t!N_t)[0]: `finiteStageSupportedComplex` applies the two actual support
  extensions then `DerivedCategory.singleFunctor _ 0` in the ordinary unbounded category.
  The `constantModelBoundedConstructible` conjunct is exactly membership in B_E(T),
  with bounded cohomology and the recorded finite constant local models.
- B_T tensor^L C_t -> G_t and its normalization: `support_comparison` is the
  `IsIso (finiteStageDerivedSupportMap ...)` conjunct. This is a morphism in the
  B_T internal-module derived category, so destination B_T-linearity is built into its type.
  Its source is the published total `leftDerivedFunctor` of ordinary scalar extension.
  Its target is exactly the double support extension of ordinary scalar extension, in
  degree zero. The arrow itself is the generic left-derived counit, followed by the
  degree-zero mapping identification and the ordinary support/scalar mate.
  The ordinary mate `finiteStageSupportScalarMap` is `pushHom` at the closed factor,
  followed by `openImmersionShriekIso` at the open factor; the double map composes the
  two support comparisons. Thus the assertion concerns the canonical support projection
  and not an unspecified isomorphism. Inverting this `IsIso` gives the displayed iso.
- Filtration F_0,...,F_n: `F : Fin (P.n+1) → DerivedCategory ...`; `IsZero (F 0)`
  expresses F_0=0 invariantly; the next isomorphism is F_n ≅ (a_!L)[0].
  For each `t : Fin P.n`, `t.castSucc` and `t.succ` index the preceding and next terms.
  The existential arrows f,g,h with `Triangle.mk f g h ∈ distTriang _` give exactly
  the distinguished triangle with third term G_t and shift by integer 1.
- Empty filtration: when S is empty, P.n=0; there are no model entries or triangles,
  and the sole F_0 is zero and isomorphic to (a_!L)[0].
- Rank zero is included because the dependency's `Mod.IsFree` permits zero generators.
  No positive-rank, connectedness or nonempty-stratum condition is introduced.
  The family E has no equality constraint, allowing different fields.

Dependency declarations read and used:

- `def-weil-l-adic-numbers`: recorded Mathlib match `Padic` in `Mathlib/NumberTheory/Padics/PadicNumbers.lean`.
- `def-weil-algebraic-closure`: recorded Mathlib match `AlgebraicClosure` in `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`.
- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`, `Profinite.continuousMapRingSheafOfUniverse`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `def-sfb-continuous-map-condensed-ring-map`: `Sheaf.Topology.ContinuousMapCondensedRingMap`, `Profinite.continuousMapRingSheafMapOfUniverse`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `sk-def-sfb-derived-extension-of-scalars`: `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`, `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`.
- `det-def-sfb-constructible-local-model`: `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`, `AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover`.
- `def-constructible-stratification`: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`, `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-sfb-lisse-coefficient-module`: `Sheaf.Paper.CoefficientHeartStratificationDefs`, `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `sk-def-sfb-module-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerShriek`.
- `def-weil-triangulated-category`: recorded Mathlib match `CategoryTheory.Pretriangulated` in `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`.

The canonical maps additionally use the already published ModuleObject.ChangeOfCoefficients:
`coefficientMap`, `CondensedRing.pushHom`, `CondensedRing.openImmersionShriekIso`,
and the module scalar-extension and derived-counit APIs. Their signatures and docstrings
were read in full. No duplicate of these constructions is introduced; the helpers only
compose them in this item's displayed order. The module exports every helper explicitly.

Edge cases checked: empty S (zero strata and zero triangles), rank-zero local systems,
one stratum, nonreduced S (the existence proof uses reduced refinements), disjoint components,
independent finite fields, arbitrary cohomological shifts in the ambient derived category,
and positive characteristic unequal to ell. The scheme, coefficient and base carriers are
in an arbitrary common universe u; the small sites retain object/morphism universe separation
and module coefficients Ab^{u+1}. There is no equation identifying the site's object and
morphism universes. General carriers can be lifted into a common universe as in the shared
continuous-coefficient convention.

Searches actually run (msearch log retained in the sandbox):

- grep: `finite.stage.*devissage|devissage.*finite.stage|good.*stratification`. Result: 0 hits. None states this finite-field scalar/support devissage.
- loogle: `"filtration", "stratification"`. Result: 0 hits. None states this finite-field scalar/support devissage.
- leanfinder: `A lisse sheaf over all continuous functions to the algebraic closure of Q ell has a finite good stratification, finite field scalar models and a localization filtration with canonical derived support projection comparisons`. Result: 8 hits: `SheafOfModules.LocalGeneratorsData.IsFiniteType`, `SheafOfModules.IsFiniteType`, `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit`, `SheafOfModules.IsFiniteType.exists_localGeneratorsData`, `LightCondMod.ofSheafLightProfinite`, `SheafOfModules.localGeneratorsDataOfIsFiniteType`, `SheafOfModules.IsFinitePresentation`, `SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType`. None states this finite-field scalar/support devissage.
- leansearch: `Finite good stratification of a lisse sheaf over continuous algebraic closure coefficients with finite field models and distinguished localization filtration`. Result: 8 hits: `SheafOfModules.isFinitePresentation`, `SheafOfModules.IsFiniteType.mk`, `SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`, `SheafOfModules.LocalGeneratorsData.IsFiniteType.mk`, `CategoryTheory.Sheaf.hasFilteredColimitsOfSize`, `instHasFiniteColimitsCondensedOfHasWeakSheafifyCompHausCoherentTopology`, `SheafOfModules.QuasicoherentData.IsFinitePresentation`, `SheafOfModules.IsFinitePresentation.casesOn`. None states this finite-field scalar/support devissage.

Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for the node id,
`finiteStageDevissage`, finite devissage and norm-algebraic-closure names found no exact
match. The nearby `continuousQbar_constructible_generators` is only a triangulated
finite-construction theorem without this finite-field support projection assertion.
The norm-algebraic-closure ordered-filtration node and supported-generation nodes have
no recorded statement yet; they are proof inputs, not notions needed to type this statement.
No source-based statement correction is required; no STATEMENT-DISPUTED finding.

Available recorded proof modules are imported privately. The recorded
`Sheaf.Paper.ContinuousAlgClStratifiedFiniteModels` source is absent locally and
`scompile.py --source Sheaf.Paper.ContinuousAlgClStratifiedFiniteModels` returned
`Module source unavailable`. That absent proof import is omitted for now; the maintainer
can add it when that interface is published, as required by the proof-import rule.
Other unstated proof dependencies are not imported. No missing proof theorem is assumed
as a hypothesis of this theorem.

Validation: the explicit-helper version compiled cleanly, then the full existential
statement compiled cleanly under the prescribed 60-second per-file limit (only the
expected sorry warning is permitted). An initial large witness structure exceeded the
limit due to generated size/equality machinery; the equivalent existential predicate
retains every clause and avoids that machinery. The final version, including available
proof imports, is checked by scompile and the delivery dry run.

Delivery dry run: `deliver2.py Q33 lem-sfb-continuous-algcl-finite-stage-devissage --no-push`
returned OK: packet compiles and passes server preflight.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
