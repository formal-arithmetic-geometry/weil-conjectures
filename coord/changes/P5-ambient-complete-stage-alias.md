# pbcConstructibleCompleteStage

## Reason

Normalize the existing constructions so Lean can check their complete proofs within the
per-file limit. The constructible stage alias is definitionally the existing
`pbcStageCategory`; explicit functor categories and result types preserve the old
inferred types and universes. The finite-stage inclusion is irreducible, with its
original object and arrow formulas. Both transition abbreviations retain the same
raw scalar extensions and Mathlib Karoubi extensions, with explicit category arguments.

The two generic typed constructors perform Mathlib's Karoubi `mapIso` conversion once
with abstract functors. The associators and finite-stage inclusion comparison apply
these constructors. The omitted `coefficientCompositionIso` adapters are `Iso.refl`;
composition with those identities gives the same natural isomorphism. Both complete
systems retain their original inline constructors and original transition and
associator data. Their existing cocycle theorem is now proved.

System-facing comparisons use their explicit canonical formulas instead of choosing
those formulas from existence-and-uniqueness theorems. Their HEq specifications fix
each whole isomorphism uniquely. The common-stage functors use the same supported
pair-functor construction, with their result types and comparisons made explicit.
Neither finite-stage nor outer projector is removed.

The raw tower proof now applies a private, proved lemma for arbitrary stage systems:
it handles repeated fields using unitors and strict towers using the localized
integral associator equation. This avoids duplicating large concrete terms in three
branches. No new mathematical statement or assumption is introduced.

No target signature or mathematical meaning changes. Target statements using these
definitions remain subject to the project's independent semantic review.

## Old

`pbcConstructibleCompleteStage`:

```lean
abbrev pbcConstructibleCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalConstructible l (pbcFiniteField.{u} l Ω E) W
```

`pbcConstructibleCompleteInclusion`:

```lean
noncomputable def pbcConstructibleCompleteInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcAmbientCompleteKaroubiStage l Ω W E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
```

`pbcAmbientCompleteKaroubiTransition`:

```lean
abbrev pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂ _ _).obj (pbcAmbientCompleteRawTransition l Ω W h)
```

`pbcConstructibleCompleteKaroubiTransition`:

```lean
abbrev pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂ _ _).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
```

`pbcAmbientCompleteKaroubiAssociator`:

```lean
@[irreducible] def pbcAmbientCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientCompleteKaroubiTransition l Ω W h ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W k ≅
      pbcAmbientCompleteKaroubiTransition l Ω W (h.trans k) :=
  (Idempotents.coefficientCompositionIso (pbcAmbientCompleteRawTransition l Ω W h)
    (pbcAmbientCompleteRawTransition l Ω W k)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso (pbcAmbientCompleteRawAssociator l Ω W h k)
```

`pbcConstructibleCompleteKaroubiAssociator`:

```lean
@[irreducible] def pbcConstructibleCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteKaroubiTransition l Ω W k ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W (h.trans k) :=
  (Idempotents.coefficientCompositionIso (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso
        (pbcScalarAssociator l Ω W hDim.out hInv.out h k)
```

`pbcCompleteRawInclusionComparison`:

```lean
@[irreducible] def pbcCompleteRawInclusionComparison (h : E ≤ F) :=
  (pbcCompleteRawInclusionComparison_exists l Ω W h).exists.choose
```

`pbcCompleteKaroubiInclusionComparison`:

```lean
@[irreducible] def pbcCompleteKaroubiInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W h ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteInclusion l Ω W F :=
  (Idempotents.coefficientCompositionIso
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
    (pbcAmbientCompleteRawTransition l Ω W h)).symm ≪≫
      (Idempotents.functorExtension₂ _ _).mapIso (pbcCompleteRawInclusionComparison l Ω W h) ≪≫
    Idempotents.coefficientCompositionIso
      (pbcScalarExtension l Ω W hDim.out hInv.out h)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W)
```

`pbcCompleteInclusionComparison`:

```lean
@[irreducible] def pbcCompleteInclusionComparison (h : E ≤ F) :=
  (pbcCompleteInclusionComparison_exists l Ω W h).exists.choose
```

`pbcCompletePairInclusion`:

```lean
@[irreducible] def pbcCompletePairInclusion :=
  StageSystem.coefficientPairFunctor
    (pbcConstructibleCompleteSystem l Ω W) (pbcAmbientCompleteSystem l Ω W)
    (pbcConstructibleCompleteInclusion l Ω W) (pbcCompleteInclusionComparison l Ω W)
    (fun h k P ↦ (pbcCompleteInclusion_coherent l Ω W h k).2 P)
```

`pbcRawStageToCompleteComparison`:

```lean
@[irreducible] def pbcRawStageToCompleteComparison (h : E ≤ F) :=
  (pbcRawStageToCompleteComparison_exists l Ω W h).exists.choose
```

`pbcRawPairToComplete`:

```lean
@[irreducible] def pbcRawPairToComplete :=
  StageSystem.coefficientPairFunctor (pbcScalarSystem l Ω W hDim.out hInv.out)
    (pbcConstructibleCompleteSystem l Ω W)
    (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W)
    (pbcRawPairToComplete_coherent l Ω W)
```

The two generic typed constructors have no previous declarations.

## New

`coefficientInclusionComparisonIso`:

```lean
@[irreducible] def coefficientInclusionComparisonIso
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    (J₀ : C₀ ⥤ D₀) (U : D₀ ⥤ D₁) (V : C₀ ⥤ C₁) (J₁ : C₁ ⥤ D₁)
    (b : J₀ ⋙ U ≅ V ⋙ J₁) :
    (functorExtension₂ _ _).obj J₀ ⋙ (functorExtension₂ _ _).obj U ≅
      (functorExtension₂ _ _).obj V ⋙ (functorExtension₂ _ _).obj J₁ :=
  (functorExtension₂ _ _).mapIso b
```

`coefficientAssociatorIso`:

```lean
@[irreducible] def coefficientAssociatorIso (F : C ⥤ D) (G : D ⥤ H) (L : C ⥤ H)
    (a : F ⋙ G ≅ L) :
    (functorExtension₂ _ _).obj F ⋙ (functorExtension₂ _ _).obj G ≅
      (functorExtension₂ _ _).obj L := (functorExtension₂ _ _).mapIso a
```

`pbcConstructibleCompleteStage`:

```lean
abbrev pbcConstructibleCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  pbcStageCategory l Ω W E
```

`pbcConstructibleCompleteInclusion`:

```lean
@[irreducible] noncomputable def pbcConstructibleCompleteInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcAmbientCompleteKaroubiStage l Ω W E :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W E)).obj
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
```

`pbcAmbientCompleteKaroubiTransition`:

```lean
abbrev pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcAmbientCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W F)).obj
      (pbcAmbientCompleteRawTransition l Ω W h)
```

`pbcConstructibleCompleteKaroubiTransition`:

```lean
abbrev pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
```

`pbcAmbientCompleteKaroubiAssociator`:

```lean
@[irreducible] def pbcAmbientCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientCompleteKaroubiTransition l Ω W h ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W k ≅
      pbcAmbientCompleteKaroubiTransition l Ω W (h.trans k) :=
  Idempotents.coefficientAssociatorIso
    (pbcAmbientCompleteRawTransition l Ω W h)
    (pbcAmbientCompleteRawTransition l Ω W k)
    (pbcAmbientCompleteRawTransition l Ω W (h.trans k))
    (pbcAmbientCompleteRawAssociator l Ω W h k)
```

`pbcConstructibleCompleteKaroubiAssociator`:

```lean
@[irreducible] def pbcConstructibleCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteKaroubiTransition l Ω W k ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W (h.trans k) :=
  Idempotents.coefficientAssociatorIso
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)
    (pbcScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcScalarAssociator l Ω W hDim.out hInv.out h k)
```

`pbcCompleteRawInclusionComparison`:

```lean
@[irreducible] def pbcCompleteRawInclusionComparison (h : E ≤ F) :
    WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W :=
  (pbcCompleteRawInclusionComparison_exists l Ω W h).exists.choose
```

`pbcCompleteKaroubiInclusionComparison`:

```lean
@[irreducible] def pbcCompleteKaroubiInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W h ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteInclusion l Ω W F := by
  with_unfolding_all
    exact Idempotents.coefficientInclusionComparisonIso
      (C₀ := pbcConstructibleCompleteStage l Ω W E)
      (C₁ := pbcConstructibleCompleteStage l Ω W F)
      (D₀ := pbcAmbientCompleteStage l Ω W E)
      (D₁ := pbcAmbientCompleteStage l Ω W F)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
      (pbcAmbientCompleteRawTransition l Ω W h)
      (pbcScalarExtension l Ω W hDim.out hInv.out h)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W)
      (pbcCompleteRawInclusionComparison l Ω W h)
```

`pbcCompleteInclusionComparison`:

```lean
@[irreducible] def pbcCompleteInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        (pbcAmbientCompleteSystem l Ω W).T h ≅
      (pbcConstructibleCompleteSystem l Ω W).T h ⋙
        pbcConstructibleCompleteInclusion l Ω W F := by
  delta pbcAmbientCompleteSystem pbcConstructibleCompleteSystem
  exact pbcCompleteKaroubiInclusionComparison l Ω W h
```

`pbcCompletePairInclusion`:

```lean
@[irreducible] def pbcCompletePairInclusion :
    (pbcConstructibleCompleteSystem l Ω W).PairCategory ⥤
      (pbcAmbientCompleteSystem l Ω W).PairCategory :=
  StageSystem.coefficientPairFunctor
    (pbcConstructibleCompleteSystem l Ω W) (pbcAmbientCompleteSystem l Ω W)
    (pbcConstructibleCompleteInclusion l Ω W) (pbcCompleteInclusionComparison l Ω W)
    (fun h k P ↦ (pbcCompleteInclusion_coherent l Ω W h k).2 P)
```

`pbcRawStageToCompleteComparison`:

```lean
@[irreducible] def pbcRawStageToCompleteComparison (h : E ≤ F) :
    pbcRawConstructibleStageToComplete l Ω W E ⋙
        (pbcConstructibleCompleteSystem l Ω W).T h ≅
      (pbcScalarSystem l Ω W hDim.out hInv.out).T h ⋙
        pbcRawConstructibleStageToComplete l Ω W F := by
  delta pbcConstructibleCompleteSystem
  exact (Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).app
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
```

`pbcRawPairToComplete`:

```lean
@[irreducible] def pbcRawPairToComplete : pbcQbarCategory l Ω W ⥤
    (pbcConstructibleCompleteSystem l Ω W).PairCategory :=
  StageSystem.coefficientPairFunctor (pbcScalarSystem l Ω W hDim.out hInv.out)
    (pbcConstructibleCompleteSystem l Ω W)
    (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W)
    (pbcRawPairToComplete_coherent l Ω W)
```

## Users

The table lists the defining module and every current transitive Lean importer. Compilation results and any necessary proof adaptations are recorded in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | P5 | Same constructions, normalized definitions. |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | Forced two-line associator proof adaptation; signatures unchanged. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | Unchanged source passed the complete consumer check. |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | Unchanged source passed the complete consumer check. |

## Status

landed 20261022T002427-L-1928742 2026-10-22 (merge of deliver/P5/Sheaf.Paper.AmbientCompleteCoefficientCategories)
