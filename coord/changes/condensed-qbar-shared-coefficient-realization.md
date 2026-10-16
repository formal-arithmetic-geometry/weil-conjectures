# Consolidate the condensed Qbar coefficient realization

## Reason

The returned delivery duplicated three statements already proved privately in
`Sheaf.Paper.CondensedQbarLfpMatrixRefinement`: `liftContinuousDown`,
`liftContinuousUp`, and `isMonHom_of_colimit`. Importing that module from
`Sheaf.Paper.CondensedQbarFunctionCoefficients` would make a cycle, since matrix
refinement imports function presentations, which now imports the coefficient module.
The old helpers are also private, so they cannot supply an imported API.

The complete private coefficient-realization section is consolidated into the lower
coefficient module, whose construction is canonical and additionally normalized.
Matrix refinement, currently unclaimed, imports and reuses that construction. This
removes the duplicate proofs rather than changing their statements to evade detection.
No public signature, definition, visibility, target, or unit realization changes.
The removed private definitions have no users outside their own section. The old
private realization gave `Nonempty` under noetherianity; the canonical construction
supplies an explicit isomorphism for every scheme and hence the required witness.

## Old

The following private section is removed verbatim:

```lean
section CoefficientUniverse
open Opposite CategoryTheory.MonObj CategoryTheory.MonoidalCategory

variable (E : Type) [NormedField E]
@[instance_reducible]
private noncomputable def liftNormedField : NormedField (ULift.{u} E) :=
  NormedField.induced _ E ULift.ringEquiv.toRingHom ULift.down_injective

@[instance_reducible]
private noncomputable def liftNormedAlgebra (K : Type) [NormedField K] [NormedAlgebra K E] :
    letI := liftNormedField.{u} E
    NormedAlgebra K (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  exact { norm_smul_le := fun c x ↦ norm_smul_le c x.down }

private lemma liftContinuousDown :
    letI := liftNormedField.{u} E
    Continuous (ULift.down : ULift.{u} E → E) := by
  let := liftNormedField.{u} E
  exact continuous_induced_dom

private lemma liftContinuousUp :
    letI := liftNormedField.{u} E
    Continuous (ULift.up : E → ULift.{u} E) := by
  let := liftNormedField.{u} E
  exact continuous_induced_rng.mpr continuous_id

private noncomputable def liftCondensedRingIso :
    letI := liftNormedField.{u} E
    Profinite.continuousMapRingSheaf.{u} E ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  let F (T : Type u) [TopologicalSpace T] :
      C(T, E) ≃+* C(T, ULift.{u} E) :=
    { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f x), (liftContinuousUp E).comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ (f x).down, (liftContinuousDown E).comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop).toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop).symm.toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    rfl
  · ext S f
    rfl

private noncomputable def liftSchemeRingIso (X : AlgebraicGeometry.Scheme.{u}) :
    letI := liftNormedField.{u} E
    AlgebraicGeometry.ProEtale.continuousMapRingSheaf X E ≅
      AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf X (ULift.{u} E) := by
  letI := liftNormedField.{u} E
  let F (T : Type u) [TopologicalSpace T] :
      C(T, E) ≃+* C(T, ULift.{u} E) :=
    { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f x), (liftContinuousUp E).comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ (f x).down, (liftContinuousDown E).comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop.left).toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom.comp (F S.unop.left).symm.toRingHom).comp
            ULift.ringEquiv.toRingHom)
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    rfl
  · ext S f
    rfl

private lemma finiteFieldComparison (ℓ : ℕ) [Fact ℓ.Prime]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ∃ d : Mon.mk (condensedRingObj (Profinite.continuousMapRingObj E) X) ≅
      Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)),
      ∀ (S : Profinite.{u}) (f : C(S, E)),
        (((pointUpperStarLowerStarAdjunction.comp
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
            _ _ d.hom.hom).hom.app (op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := by
  let := liftNormedField.{u} E
  let := liftNormedAlgebra.{u} E ℚ_[ℓ]
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm
  obtain ⟨e, he, _⟩ := existsUnique_condensedFieldContinuousMapIso ℓ (ULift.{u} E) X
  let L := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftCondensedRingIso E)
  let M := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (liftSchemeRingIso E X)
  let L' := (upperStarFromPoint X).mapIso L
  have : IsMonHom L.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftCondensedRingIso E).hom
  have : IsMonHom L'.hom := by
    change IsMonHom ((upperStarFromPoint X).map L.hom)
    infer_instance
  have : IsMonHom M.hom := by
    exact Sheaf.isMonHom_sheafCompose_map _ (liftSchemeRingIso E X).hom
  let d := Mon.mkIso' L' ≪≫ e ≪≫ (Mon.mkIso' M).symm
  refine ⟨d, ?_⟩
  intro S f
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  change ((adj.homEquiv _ _
    (((pointUpperStar ⋙ upperStar AddCommGrpCat.{u + 1} (toSpecZ X)).map
      L.hom ≫ e.hom.hom) ≫ M.inv)).hom.app (op S))
      (ULift.up f) = _
  erw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  let f' : C(S, ULift.{u} E) :=
    ⟨fun s ↦ ULift.up (f s), (liftContinuousUp E).comp f.continuous⟩
  have hf := he S f'
  change _ = ULift.up (f'.comp (profiniteTestProjection X S)) at hf
  change ULift.up (⟨fun x ↦
    (((adj.homEquiv _ _ e.hom.hom).hom.app (op S)) (ULift.up f')).down x |>.down,
    _⟩ : C(_, E)) = _
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z ↦ (z.down x).down) hf

section Colimit
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {J : Type w} [Category.{z} J] [IsSifted J]
  {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  [MonObj c.pt] [∀ j, MonObj (F.obj j)]
  [PreservesColimit₂ F F (curriedTensor C)]
include hc in
private lemma isMonHom_of_colimit {R : C} [MonObj R] (g : c.pt ⟶ R)
    (hι : ∀ j, IsMonHom (show F.obj j ⟶ c.pt from c.ι.app j)) (hg : ∀ j, IsMonHom (c.ι.app j ≫ g)) :
    IsMonHom g := by
  have : Nonempty J := IsSifted.nonempty
  constructor
  · obtain ⟨j⟩ := ‹Nonempty J›
    have := hι j
    have := hg j
    rw [← IsMonHom.one_hom (c.ι.app j), Category.assoc]
    exact IsMonHom.one_hom (c.ι.app j ≫ g)
  · apply (IsColimit.tensor hc hc).hom_ext
    intro j
    have := hι j
    have := hg j
    change (c.ι.app j ⊗ₘ c.ι.app j) ≫ μ[c.pt] ≫ g =
      (c.ι.app j ⊗ₘ c.ι.app j) ≫ (g ⊗ₘ g) ≫ μ[R]
    rw [← IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Colimit

private lemma fieldDiagramIso (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ∃ d : Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X ≅
      padicSubfieldSheafFunctor X ℓ ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}),
      ∀ E : PadicAlgCl.FiniteIntermediateField ℓ, IsMonHom (show
        condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
              (continuousMapRingSheaf X E) from d.hom.app E) := by
  classical
  have hi (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    finiteFieldComparison E ℓ X
  choose e he using hi
  let d (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X).obj E ≅
        (padicSubfieldSheafFunctor X ℓ ⋙
          sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj E :=
    (Mon.forget _).mapIso (e E)
  refine ⟨NatIso.ofComponents d ?_, ?_⟩
  · intro E F a
    let adj := pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _
      ((pointUpperStar ⋙ upperStar AddCommGrpCat.{u + 1} (toSpecZ X)).map
        (Profinite.padicSubfieldRingObjMap ℓ (leOfHom a)) ≫ (e F).hom.hom) =
      adj.homEquiv _ _ ((e E).hom.hom ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
            (padicSubfieldSheafMapOfLE X ℓ (leOfHom a)))
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    ext S f
    cases f with
    | up f =>
      change (((adj.homEquiv _ _ (e F).hom.hom).hom.app S)
        (ULift.up ⟨_, _⟩)) = _
      rw [he F S.unop]
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      exact congrArg (fun z ↦ IntermediateField.inclusion (leOfHom a) (z.down x))
        (he E S.unop f).symm
  · intro E
    change IsMonHom (e E).hom.hom
    infer_instance

noncomputable section
private lemma globalCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    Nonempty (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
      Mon.mk (padicAlgClSheaf X ℓ)) := by
  obtain ⟨d, hd⟩ := fieldDiagramIso ℓ X
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (toSpecZ X))).leftAdjoint_preservesColimits
  let h₁ := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone.{u} ℓ)
  let h₂ := (IsColimit.precomposeHomEquiv d (padicAlgClSheafCocone X ℓ)).symm
    (isColimitPadicAlgClSheafCocone X ℓ)
  let e : condensedRingObj (Profinite.padicAlgClRingObj ℓ) X ≅ padicAlgClSheaf X ℓ :=
    h₁.coconePointUniqueUpToIso h₂
  have he (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
        e.hom = d.hom.app E ≫ (padicAlgClSheafCocone X ℓ).ι.app E :=
    h₁.comp_coconePointUniqueUpToIso_hom h₂ E
  have : IsSifted (PadicAlgCl.FiniteIntermediateField ℓ) := IsFiltered.isSifted
  have : IsMonHom e.hom := by
    refine @isMonHom_of_colimit _ _ _ _ _ _ _
      ((upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone.{u} ℓ)) h₁
      (inferInstanceAs (MonObj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
      (fun E ↦ inferInstanceAs
        (MonObj (condensedRingObj (Profinite.continuousMapRingObj E) X)))
      _ _ _ e.hom ?_ ?_
    · intro E
      change IsMonHom ((upperStarFromPoint X).map
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E))
      infer_instance
    · intro E
      change IsMonHom
        ((upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ e.hom)
      rw [he E]
      change IsMonHom ((show condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
              (continuousMapRingSheaf X E) from d.hom.app E) ≫
        padicSubfieldSheafToPadicAlgClSheaf X ℓ E.1)
      have := hd E
      infer_instance
  exact ⟨Mon.mkIso' e⟩

end
end CoefficientUniverse

```

Its sole external-to-section use was:

```lean
      (globalCoefficientIso ℓ X) P hP'
```

## New

The section is removed, and the proof-only import is added:

```lean
import Sheaf.Paper.CondensedQbarFunctionCoefficients
```

The existing matrix-refinement theorem supplies its comparison hypothesis using:

```lean
      ⟨CondensedQbarCoefficientRealization.globalCoefficientIso ℓ X⟩ P hP'
```

The new coefficient module retains the single shared implementation of the lifted
field topology, continuity lemmas, finite-extension comparisons and multiplicative
colimit comparison. Its four-property theorem remains the same admitted theorem;
no new admission is introduced by this repair. The three now-unused proof imports
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`,
`Mathlib.CategoryTheory.Monoidal.Limits.Colimits`, and `Mathlib.Algebra.Field.ULift`
are removed from matrix refinement. Their former local uses were in the deleted section.
All original public imports are retained.

The full landing check also matched private coordinate lemmas in the item against
`Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank`. The latter fixes
`E : Type u` and `F : D ⥤ ModuleCat.{u + 1} E`, while the item independently permits
`E : Type uE` with the same carrier universe. The old implicit context in the item is:

```lean
variable {E : Type uE} [Field E]
variable {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)
```

The new private declarations `finiteFreeEvaluationCoords_apply`,
`finiteFreeEvaluationCoords_symm_single`, and `finiteFreeEvaluationCoords_matrix`
write this same context explicitly as the initial binders:

```lean
    {E : Type uE} [Field E]
    {D : Type v} [Category.{w} D] [Preadditive D] [HasFiniteBiproducts D]
    (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive] (e : F.obj A ≃ₗ[E] E)
```

Their remaining binders, conclusions and proofs are unchanged. The explicit context
makes the independent coefficient universe visible to the text checker, as its message
requests for declarations that differ through section variables. No external module
uses these private declarations; the generic continuous-field theorem still cannot
be applied to the small coefficient field required here. No public signature changes.

## Users

`tools/downstream.py` was run for all ten removed private declaration names. Each
name was found only in matrix refinement itself. The following table includes all
58 transitive consumers; none needs a source change. This is an allowed unclaimed
module consolidation, not a forced adaptation of a module held by another group.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | unclaimed | Remove duplicate private coefficient section; reuse canonical coefficient isomorphism. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | A4 | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | Public API unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Public API unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Public API unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Public API unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Public API unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Public API unchanged; no adaptation. |

## Status

landed 20261016T082348-L-1529163 2026-10-16 (merge of deliver/H3/Sheaf.Paper.CondensedQbarFunctionPresentations)
consumer compilation, and the landing duplicate checker against the complete overlay.
