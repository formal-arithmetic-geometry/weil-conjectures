# AlgebraicGeometry.Scheme.pbcFiniteRawScalarComparison_existsUnique

## Reason

Prove the existing integral-normalized comparison using proved private helpers.
The preflight command scanner conservatively classifies the added `open scoped
TensorProduct` and `omit [IsNoetherian T] dT iT in` as a change requiring this record.
The scope command enables tensor notation only inside this module. The `omit` applies
only to the new private `rawScalar_coefficientMap` lemma, which needs no geometric
hypotheses. Local transparency options apply to individual proofs and permit Lean to
compare the existing coefficient/category aliases. None changes a public signature,
public import, public definition body, instance, attribute, or mathematical object.

## Old

```lean
theorem pbcFiniteRawScalarComparison_existsUnique :
    ∃! c : (pbcScalarSystem l Ω T dT.out iT.out).T h ≅
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h)
          T dT.out iT.out,
      ∀ K : pbcIntegralStage l Ω T E,
        HEq (c.hom.app ((pbcStageLocalization l Ω T E).obj K))
          ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K) := by
  sorry
```

## New

```lean
theorem pbcFiniteRawScalarComparison_existsUnique :
    ∃! c : (pbcScalarSystem l Ω T dT.out iT.out).T h ≅
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h)
          T dT.out iT.out,
      ∀ K : pbcIntegralStage l Ω T E,
        HEq (c.hom.app ((pbcStageLocalization l Ω T E).obj K))
          ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K) := by
  have hJ : pbcIntegralScalarExtension l Ω T dT.out iT.out h ⋙
      pbcStageLocalization l Ω T F =
      pbcStageLocalization l Ω T E ⋙
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T dT.out iT.out := by
    rw [rawScalar_integralTensor l Ω T h]
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro K L f
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
      pbcScalarLocalization_naturality l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T f
  exact rawScalar_comparison (pbcStageUniformizer.{u} l Ω E)
    ((pbcScalarSystem l Ω T dT.out iT.out).T h)
    (pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T dT.out iT.out)
    _ (pbcScalarIntegralComparison l Ω T dT.out iT.out h) hJ
```

The new private lemmas are `rawScalar_naturality`, `rawScalar_comparison`,
`rawScalar_levelConstant_hom`, `rawScalar_coefficientMap`, and
`rawScalar_integralTensor`. All are fully proved. The original definition choosing
the unique comparison is byte-identical. The theorem retains every hypothesis,
universe parameter, conclusion and normalization. Its proof now constructs the
comparison from the existing integral one, with no new unproved theorem.

## Users

`python3 tools/downstream.py Sheaf.Paper.PbcFiniteRawScalarComparison` reports
zero current Lean importers. The item remains needed by its DAG parents whose
proofs have not yet imported it; no withdrawal or dependency pruning is proposed.
All future users see the same public declarations and definitions. No target
statement or definition changes meaning; no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcFiniteRawScalarComparison | S7 | Existing theorem proved; private helpers only. |

## Status

landed 20261021T130146-L-2571775 2026-10-21 (merge of deliver/S7/Sheaf.Paper.PbcFiniteRawScalarComparison)
