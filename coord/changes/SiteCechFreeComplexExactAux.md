# CategoryTheory.SiteCechComplex definitions: auxiliary-module extraction

## Reason

Keep the four existing constructions available to the new objectwise contracting-identity
lemma without creating an import cycle. This moves definitions unchanged, not a slow-compile
workaround. The target module publicly imports the auxiliary module. Its target theorem
keeps its signature and docstring. No definition uses a new unproved theorem to choose data.
The auxiliary theorem is a proof obligation only; its witnesses are used inside the target proof.

The only original public import used exclusively by the proof, Presheaf.Abelian, becomes
an ordinary import of the target. SiteCechComplex, Presheaf.Free and AlternatingFaceMapComplex
remain publicly available through the auxiliary module. PowerSetComplexContractible is a
proof-only import of the auxiliary lemma's planned argument. The target's proof-only import
is Mathlib.Algebra.Homology.ShortComplex.ModuleCat.

## Old

In lean/Sheaf/CategoryTheory/Sites/SiteCechFreeComplexExact.lean:

```lean
/-- The coproduct of representables on the degree-p products, as a presheaf of sets.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tuplePresheaf (p : ℕ) : Cᵒᵖ ⥤ Type v where
  obj X := Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t
  map g := ↾fun x ↦ ⟨x.1, g.unop ≫ x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (𝟙 X.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t) = x
    rw [Category.id_comp]
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (h.unop ≫ g.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, _ ⟶ S.W p t) = ⟨x.1, h.unop ≫ (g.unop ≫ x.2)⟩
    rw [Category.assoc]

/-- A map of tuple indices induces a map of the corresponding representable sums.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tupleMap {p q : ℕ} (α : Fin (q + 1) → Fin (p + 1)) :
    S.tuplePresheaf p ⟶ S.tuplePresheaf q where
  app X := ↾fun x ↦ ⟨x.1 ∘ α, x.2 ≫ S.indexMap x.1 α⟩
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ α, (g.unop ≫ x.2) ≫ S.indexMap x.1 α⟩ :
      Σ t : Fin (q + 1) → T, Y.unop ⟶ S.W q t) =
      ⟨x.1 ∘ α, g.unop ≫ (x.2 ≫ S.indexMap x.1 α)⟩
    rw [Category.assoc]

/-- The simplicial representable sums; index-map laws follow from product uniqueness.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
abbrev tupleSimplicial : SimplicialObject (Cᵒᵖ ⥤ Type v) where
  obj n := S.tuplePresheaf n.unop.len
  map α := S.tupleMap α.unop.toOrderHom
  map_id n := by
    have hi (t : Fin (n.unop.len + 1) → T) : S.indexMap t id = 𝟙 _ := by
      obtain ⟨c, _, hu⟩ := S.universal n.unop.len t (S.W n.unop.len t)
        (S.pr n.unop.len t) (S.comm n.unop.len t)
      apply (hu _ ?_).trans (hu _ (fun k ↦ Category.id_comp _)).symm
      intro k
      exact S.indexMap_pr t id k
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ id, x.2 ≫ S.indexMap x.1 id⟩ :
      Σ t : Fin (n.unop.len + 1) → T, X.unop ⟶ S.W n.unop.len t) = x
    rw [hi, Category.comp_id]
    cases x
    rfl
  map_comp α β := by
    have hi (t) : S.indexMap t (α.unop.toOrderHom ∘ β.unop.toOrderHom) =
        S.indexMap t α.unop.toOrderHom ≫
          S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom := by
      let b := S.indexMap t α.unop.toOrderHom ≫
        S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom
      obtain ⟨c, _, hu⟩ := S.universal _ _ _
        (fun k ↦ b ≫ S.pr _ _ k)
        (fun k ↦ by simp only [Category.assoc, S.comm])
      apply (hu _ ?_).trans (hu b (fun _ ↦ rfl)).symm
      intro k
      dsimp [b]
      symm
      rw [Category.assoc]
      exact (congrArg (fun h ↦ S.indexMap t α.unop.toOrderHom ≫ h)
        (S.indexMap_pr (t ∘ α.unop.toOrderHom) β.unop.toOrderHom k)).trans
        ((S.indexMap_pr t α.unop.toOrderHom (β.unop.toOrderHom k)).trans
          (S.indexMap_pr t (α.unop.toOrderHom ∘ β.unop.toOrderHom) k).symm)
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ (α.unop.toOrderHom ∘ β.unop.toOrderHom),
      x.2 ≫ S.indexMap x.1 (α.unop.toOrderHom ∘ β.unop.toOrderHom)⟩ :
      Σ t : Fin (_ + 1) → T, X.unop ⟶ S.W _ t) =
      ⟨(x.1 ∘ α.unop.toOrderHom) ∘ β.unop.toOrderHom,
        (x.2 ≫ S.indexMap x.1 α.unop.toOrderHom) ≫
          S.indexMap (x.1 ∘ α.unop.toOrderHom) β.unop.toOrderHom⟩
    rw [hi, Category.assoc]
    rfl

/-- The actual alternating chain complex of free module presheaves on the tuple sums.
Source: Stacks 03F5 (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
noncomputable abbrev freeComplex (R : Cᵒᵖ ⥤ RingCat.{v}) :
    ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (S.tupleSimplicial ⋙ PresheafOfModules.free R)
```

## New

Verbatim in lean/Sheaf/CategoryTheory/Sites/SiteCechFreeComplexExactAux.lean,
publicly imported by SiteCechFreeComplexExact:

```lean
/-- The coproduct of representables on the degree-p products, as a presheaf of sets.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tuplePresheaf (p : ℕ) : Cᵒᵖ ⥤ Type v where
  obj X := Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t
  map g := ↾fun x ↦ ⟨x.1, g.unop ≫ x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (𝟙 X.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t) = x
    rw [Category.id_comp]
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (h.unop ≫ g.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, _ ⟶ S.W p t) = ⟨x.1, h.unop ≫ (g.unop ≫ x.2)⟩
    rw [Category.assoc]

/-- A map of tuple indices induces a map of the corresponding representable sums.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tupleMap {p q : ℕ} (α : Fin (q + 1) → Fin (p + 1)) :
    S.tuplePresheaf p ⟶ S.tuplePresheaf q where
  app X := ↾fun x ↦ ⟨x.1 ∘ α, x.2 ≫ S.indexMap x.1 α⟩
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ α, (g.unop ≫ x.2) ≫ S.indexMap x.1 α⟩ :
      Σ t : Fin (q + 1) → T, Y.unop ⟶ S.W q t) =
      ⟨x.1 ∘ α, g.unop ≫ (x.2 ≫ S.indexMap x.1 α)⟩
    rw [Category.assoc]

/-- The simplicial representable sums; index-map laws follow from product uniqueness.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
abbrev tupleSimplicial : SimplicialObject (Cᵒᵖ ⥤ Type v) where
  obj n := S.tuplePresheaf n.unop.len
  map α := S.tupleMap α.unop.toOrderHom
  map_id n := by
    have hi (t : Fin (n.unop.len + 1) → T) : S.indexMap t id = 𝟙 _ := by
      obtain ⟨c, _, hu⟩ := S.universal n.unop.len t (S.W n.unop.len t)
        (S.pr n.unop.len t) (S.comm n.unop.len t)
      apply (hu _ ?_).trans (hu _ (fun k ↦ Category.id_comp _)).symm
      intro k
      exact S.indexMap_pr t id k
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ id, x.2 ≫ S.indexMap x.1 id⟩ :
      Σ t : Fin (n.unop.len + 1) → T, X.unop ⟶ S.W n.unop.len t) = x
    rw [hi, Category.comp_id]
    cases x
    rfl
  map_comp α β := by
    have hi (t) : S.indexMap t (α.unop.toOrderHom ∘ β.unop.toOrderHom) =
        S.indexMap t α.unop.toOrderHom ≫
          S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom := by
      let b := S.indexMap t α.unop.toOrderHom ≫
        S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom
      obtain ⟨c, _, hu⟩ := S.universal _ _ _
        (fun k ↦ b ≫ S.pr _ _ k)
        (fun k ↦ by simp only [Category.assoc, S.comm])
      apply (hu _ ?_).trans (hu b (fun _ ↦ rfl)).symm
      intro k
      dsimp [b]
      symm
      rw [Category.assoc]
      exact (congrArg (fun h ↦ S.indexMap t α.unop.toOrderHom ≫ h)
        (S.indexMap_pr (t ∘ α.unop.toOrderHom) β.unop.toOrderHom k)).trans
        ((S.indexMap_pr t α.unop.toOrderHom (β.unop.toOrderHom k)).trans
          (S.indexMap_pr t (α.unop.toOrderHom ∘ β.unop.toOrderHom) k).symm)
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ (α.unop.toOrderHom ∘ β.unop.toOrderHom),
      x.2 ≫ S.indexMap x.1 (α.unop.toOrderHom ∘ β.unop.toOrderHom)⟩ :
      Σ t : Fin (_ + 1) → T, X.unop ⟶ S.W _ t) =
      ⟨(x.1 ∘ α.unop.toOrderHom) ∘ β.unop.toOrderHom,
        (x.2 ≫ S.indexMap x.1 α.unop.toOrderHom) ≫
          S.indexMap (x.1 ∘ α.unop.toOrderHom) β.unop.toOrderHom⟩
    rw [hi, Category.assoc]
    rfl

/-- The actual alternating chain complex of free module presheaves on the tuple sums.
Source: Stacks 03F5 (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
noncomputable abbrev freeComplex (R : Cᵒᵖ ⥤ RingCat.{v}) :
    ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (S.tupleSimplicial ⋙ PresheafOfModules.free R)
```

## Users

The complete transitive downstream list from tools/downstream.py is below. Only
InjectivePresheafModuleCechExact directly mentions any of the moved definitions outside
the item; its original compiles against the baseline but fails against the delivered overlay.
The forced adaptation adds only an ordinary proof import of Presheaf.Abelian;
it restores the instance needed by descToInjective inference and compiles.
Its declarations, signatures, visibility, docstrings and proof bodies are unchanged. Extraction preserves the meaning of all targets;
no target definition changes and no semantic target re-review is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExact | V3 | Publicly imports the same constructions; unchanged theorem signature |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | W3 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit | F3 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModuleHigherDirectImageCyclicReduction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitAffineSectionDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModuleLimitFiberDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardGermVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitInjectivity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimitSurjectivity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleBaseChangeRestrictScalars | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineCorrectedLift | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitAffineEventualZero | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyAffineComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyBinaryGluing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyDegreeZeroDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.EtaleRestrictedCohomologyNeighbourhoodColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassRep | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | F1 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | J2 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1 | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1 | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAbelianStalkExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.PrimeInjectiveCohomologyComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.PullbackIsoTorsionColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit | H2 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeQuotientDetection | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | T1 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | E2 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic | V2 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.CategoryTheory.Sites.InjectivePresheafModuleCechExact | unclaimed | Forced one-line ordinary import of Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian; otherwise unchanged |
| Sheaf.Paper.EtaleClassVanishingSpreads | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.Paper.GabberCriterion | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.Paper.GabberCriterionDegree | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.Paper.GabberPrincipalClassLocallyZero | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| TargetsCheck | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X3 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same declaration names, types and definition bodies via public auxiliary import; no meaning changes |

The adapted module formerly had just this proof import:

```lean
import Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExact
```

It now has:

```lean
import Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
```

The original compiler error against the changed overlay was an application type
mismatch at `e q (hK.descToInjective a ha)` (line 162): inference left the domain
as `ShortComplex.X₃ ?m` instead of `(S.freeComplex R).X q`. The explicit import
supplies the presheaf abelian instance and removes that error.

## Status

landed 20261012T173914-L-3309198 2026-10-12 (merge of deliver/V3/Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExact)
