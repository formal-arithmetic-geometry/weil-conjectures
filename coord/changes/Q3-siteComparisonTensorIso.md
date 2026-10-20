# AlgebraicGeometry.ProEtale.siteComparisonTensorIso

## Reason

The finite-free Hom comparison needs the strong monoidal structure of exact comparison
pullback on the derived category. Identifying the original four-factor tensor isomorphism
with its transported tensorator made Lean unfold large site and derived monoidal
constructions, exceeding the single-file limit. Cache the canonical monoidal structure
as `siteComparisonDerivedMonoidal`, using the existing proved
`Functor.residueDerivedMonoidal` inside a proof of existence with prescribed tensor
components, and construct the same natural isomorphism from those components. No mathematical choice or hypothesis is added. These constructed definitions are
irreducible to prevent elaboration from repeatedly expanding the site and derived
category structures; the proved component equation provides their tensor API.

Write F for comparisonUpperStar and e for leftDerivedFunctorIsoMapDerivedCategory.
The derived oplax tensorator is leftDerivedTensorComparison.app K |>.app M by construction.
The transported tensorator is
`e.inv.app (K ⊗ M) ≫ δ(LF) K M ≫ (e.hom.app K ⊗ₘ e.hom.app M)`
by `Functor.Monoidal.transport_δ`. The new theorem
`siteComparisonDerivedMonoidal_δ` proves this formula for the selected structure. Expanding tensorHom_def' gives exactly the four
factors of the original natural isomorphism. Thus the natural isomorphism and its inverse
are preserved; the evaluation-defined Hom comparison keeps the same meaning.
The target statements and their definitions retain their mathematical content, but this
representation change is explicitly submitted for the independent definition-reader check.

`siteComparisonDerivedMonoidal_exists` first proves that a strong structure has these
prescribed components. Its selected structure therefore has no unspecified tensor map;
the tensorator used in evaluation is the unique inverse of its specified oplax component.
The selected auxiliary unit data do not occur in either comparison map. The existence
proof is complete and uses no `sorry`. This is the equality used downstream required by
the rule on definitions selected from theorems. The integral-residue module is now a
private proof import, so its unrelated instances do not enter consumer elaboration.

The repaired module is unclaimed. All consumers are listed below. There are no forced
adaptations of another group's files, and no WeilConjectures source edits.

## Old

```lean
noncomputable def siteComparisonTensorIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ (comparisonUpperStar A X).mapDerivedCategory ≅
      (comparisonUpperStar A X).mapDerivedCategory ⋙
        (derivedTensor A X).obj ((comparisonUpperStar A X).mapDerivedCategory.obj K) := by
  letI : (comparisonLowerStar A X).LaxMonoidal := by
    unfold comparisonLowerStar
    infer_instance
  letI : (comparisonUpperStar A X).OplaxMonoidal :=
    (comparisonAdjunction A X).leftAdjointOplaxMonoidal
  letI (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow X.toProEt.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (unop V))
  letI (F G : Sheaf X.smallEtaleTopology A) :
      IsIso (Functor.OplaxMonoidal.δ (comparisonUpperStar A X) F G) := by
    unfold comparisonUpperStar
    infer_instance
  letI : IsIso (Functor.OplaxMonoidal.η (comparisonUpperStar A X)) := by
    unfold comparisonUpperStar
    infer_instance
  letI : (comparisonUpperStar A X).Monoidal := .ofOplaxMonoidal _
  exact Functor.isoWhiskerLeft _
      (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (asIso (comparisonUpperStar A X).leftDerivedTensorComparison).app K ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft (comparisonUpperStar A X).mapDerivedCategory
      ((derivedTensor A X).mapIso
        ((comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory.app K))
```

## New

```lean
/-- The canonical strong monoidal structure of comparison inverse image.
Source: Stacks Tag 03EL (blueprint: def-sf-evaluation-hom-site-comparison). -/
@[irreducible]
noncomputable def siteComparisonMonoidal
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    (comparisonUpperStar A X).Monoidal := by
  let : (comparisonLowerStar A X).LaxMonoidal := by
    unfold comparisonLowerStar
    infer_instance
  let : (comparisonUpperStar A X).OplaxMonoidal :=
    (comparisonAdjunction A X).leftAdjointOplaxMonoidal
  let (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow X.toProEt.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (unop V))
  let (F G : Sheaf X.smallEtaleTopology A) :
      IsIso (Functor.OplaxMonoidal.δ (comparisonUpperStar A X) F G) := by
    unfold comparisonUpperStar
    infer_instance
  let : IsIso (Functor.OplaxMonoidal.η (comparisonUpperStar A X)) := by
    unfold comparisonUpperStar
    infer_instance
  exact .ofOplaxMonoidal _

private theorem derived_monoidal_exists
    {C : Type u₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (e : F.leftDerivedFunctor ≅ F.mapDerivedCategory) :
    ∃ m : F.mapDerivedCategory.Monoidal,
      let := m
      ∀ K M, Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
        e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
          (e.hom.app K ⊗ₘ e.hom.app M) := by
  let : F.leftDerivedFunctor.Monoidal := F.residueDerivedMonoidal
  refine ⟨Functor.Monoidal.transport e, ?_⟩
  dsimp only
  intro K M
  rw [Functor.Monoidal.transport_δ
    (C := DerivedCategory C) (D := DerivedCategory D) e K M]
  rfl

/-- The canonical derived tensor comparison admits a strong monoidal structure.
Its tensor components are prescribed, so the structure determines the comparison maps
used below. Source: Stacks Tags 03EL, 08J7
(blueprint: def-sf-evaluation-hom-site-comparison). -/
theorem siteComparisonDerivedMonoidal_exists
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    let := siteComparisonMonoidal A X
    let F := comparisonUpperStar A X
    let e := F.leftDerivedFunctorIsoMapDerivedCategory
    ∃ m : F.mapDerivedCategory.Monoidal,
      let := m
      ∀ K M, Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
        e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
          (e.hom.app K ⊗ₘ e.hom.app M) := by
  let : (comparisonUpperStar A X).Monoidal := siteComparisonMonoidal A X
  exact derived_monoidal_exists
    (C := Sheaf X.smallEtaleTopology A)
    (D := Sheaf (Scheme.ProEt.topology X) A)
    (comparisonUpperStar A X)
    (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory

/-- Strong monoidal structure with the prescribed canonical derived tensor components.
Only those components and their inverses occur in the comparison maps. The preceding
proved theorem specifies them before the structure is selected.
Source: Stacks Tags 03EL, 08J7 (blueprint: def-sf-evaluation-hom-site-comparison). -/
@[irreducible]
noncomputable def siteComparisonDerivedMonoidal
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    (comparisonUpperStar A X).mapDerivedCategory.Monoidal :=
  (siteComparisonDerivedMonoidal_exists A X).choose

set_option backward.isDefEq.respectTransparency true in
/-- The chosen structure has exactly the canonical transported tensor components.
Source: Stacks Tags 03EL, 08J7 (blueprint: def-sf-evaluation-hom-site-comparison). -/
theorem siteComparisonDerivedMonoidal_δ
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := siteComparisonMonoidal A X
    let F := comparisonUpperStar A X
    let e := F.leftDerivedFunctorIsoMapDerivedCategory
    let := siteComparisonDerivedMonoidal A X
    Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
      e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
        (e.hom.app K ⊗ₘ e.hom.app M) := by
  dsimp only
  unfold siteComparisonDerivedMonoidal
  exact (siteComparisonDerivedMonoidal_exists A X).choose_spec K M

/-- The canonical derived tensor comparison of the comparison inverse image.
It is obtained by deriving the oplax structure conjugate to restriction of sheaves;
representable flatness makes that structure strong monoidal.
Source: Stacks Tags 03EO, 03EL (blueprint: def-sf-evaluation-hom-site-comparison). -/
@[irreducible]
noncomputable def siteComparisonTensorIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ (comparisonUpperStar A X).mapDerivedCategory ≅
      (comparisonUpperStar A X).mapDerivedCategory ⋙
        (derivedTensor A X).obj ((comparisonUpperStar A X).mapDerivedCategory.obj K) := by
  let F := comparisonUpperStar A X
  let : F.mapDerivedCategory.Monoidal := siteComparisonDerivedMonoidal A X
  exact NatIso.ofComponents
    (fun M ↦ (Functor.Monoidal.μIso F.mapDerivedCategory K M).symm)
    (fun f ↦ (Functor.OplaxMonoidal.δ_natural_right F.mapDerivedCategory K f).symm)

/-- Component formula for the canonical derived tensor comparison.
Source: Stacks Tags 03EL, 08J7 (blueprint: def-sf-evaluation-hom-site-comparison). -/
theorem siteComparisonTensorIso_hom_app
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := siteComparisonDerivedMonoidal A X
    (siteComparisonTensorIso A X K).hom.app M =
      Functor.OplaxMonoidal.δ (comparisonUpperStar A X).mapDerivedCategory K M := by
  unfold siteComparisonTensorIso
  rfl
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison | unclaimed | Both comparison definitions retain their signatures and evaluation meaning; the proved API exposes the constructed maps. |
| Sheaf.Paper.FiniteFreeHomComparison | Q3 | Proves invertibility through the canonical derived monoidal structure and dualizability. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Its `IsEvaluationComparison` predicate names the Hom comparison. The signature and evaluation specification are preserved; no edit. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | States invertibility of the same Hom arrow for constructible complexes; no edit. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Its `siteHom` definition uses the same Hom arrow; no edit. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Its compatibility predicates use both comparison maps. Their signatures and mathematical maps are preserved; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Its mapping-arrow composites use both comparison maps; no edit. |

The five additional users occur in the restored sources listed by `coord/rework.tsv`.
Inspection finds uses in statements and composite-map definitions, with no proof unfolding
of the changed comparison bodies. Their existing interfaces are preserved. No module held
by another group is edited, and no forced adaptation is claimed.

## Status

landed 20261020T211816-L-3504665 2026-10-20 (merge of deliver/Q3/Sheaf.Paper.FiniteFreeHomComparison)
