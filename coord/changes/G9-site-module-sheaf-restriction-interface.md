# CategoryTheory.site_moduleSheaf_restriction_equivalence

## Reason

The bounded truncation-model proof needs the inverse scalar-restriction equivalence
and its natural compatibility with restriction of arbitrary module sheaves to slices.
The original public equivalence only exposes slice compatibility for constants.
Expose the already constructive inverse using the existing private scalar-restriction
object, extension functor, sheafification counit and constant unit. The module is
unclaimed. No existing public signature, public import, target or definition changes.

## Old

`CategoryTheory.site_moduleSheaf_restriction_equivalence` did not exist.
`CategoryTheory.site_moduleSheaf_constantRing_equivalence` is retained verbatim.

## New

```lean
theorem site_moduleSheaf_restriction_equivalence
    (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
    (R : Sheaf J RingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :
    let c := SheafOfModules.strictPerfectConstantPresheaf (C := C) Λ ⋙
      PresheafOfModules.sheafification.{u} α
    ∃ G : SheafOfModules.{u} R ⥤ Sheaf J (ModuleCat.{u} Λ),
      G.IsEquivalence ∧ Nonempty (c ⋙ G ≅ constantSheaf J (ModuleCat.{u} Λ)) ∧
      ∀ U : C, ∃ GU : SheafOfModules.{u} (R.over U) ⥤
          Sheaf (J.over U) (ModuleCat.{u} Λ),
        GU.IsEquivalence ∧ Nonempty
          (SheafOfModules.overFunctor R U ⋙ GU ≅
            G ⋙ J.overPullback (ModuleCat.{u} Λ) U)
```

The theorem and all added private constructions are fully proved. The inverse functor
restricts each section's scalar action; no arbitrary existence witness supplies data.
The existing node records both public declarations and the inverse construction.

## Users

The downstream scan with `--uses CategoryTheory.site_moduleSheaf_constantRing_equivalence`
found only its own defining module as a textual user. The only direct importer is the
assigned item. Existing declarations, instances and public imports are unchanged, so
all other downstream statements retain their meaning and need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence | unclaimed | Add proved inverse interface; original theorem unchanged. |
| Sheaf.Paper.SiteBoundedTruncationModels | G9 | Use new inverse interface in its proof. |

## Status

landed 20261020T122108-L-476463 2026-10-20 (merge of deliver/G9/Sheaf.Paper.SiteBoundedTruncationModels)
