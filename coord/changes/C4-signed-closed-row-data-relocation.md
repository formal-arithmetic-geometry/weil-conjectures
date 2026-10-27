# AlgebraicGeometry.SignedClosedFamily and AlgebraicGeometry.SignedClosedRow

## Reason

Split the assigned signed-refinement construction into individual row existence and
refinement maps between given rows. Both statements must see the existing family and
row specifications without importing the theorem that uses them. Relocate these two
structures into a common data module, retaining their names, binders, fields and
executable bodies verbatim. The original module publicly re-exports them. The refinement
system and target theorem retain their exact signatures and module path.

The proof constructs total maps and proves their diagonal component and augmentation
formulas. It does not use a cover or alter any target meaning. No adopted-source file,
shared instance, transparency setting, simp attribute or target statement is changed.

## Old

Module: `Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements`.

```lean
structure SignedClosedFamily {X Z : Scheme.{u}} (i : Z ⟶ X) where
  length : ℕ
  positive : 0 < length
  members : Fin length → Over X
  closed : ∀ a, IsClosedImmersion (members a).hom
  factor : ∀ a, Nonempty (members a ⟶ Over.mk i)
  complement : ∀ a, ∃ U : X.Opens,
    Set.range U.ι = (Set.range (members a).hom)ᶜ ∧ QuasiCompact U.ι

structure SignedClosedRow {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : SignedClosedFamily i) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  support_additive : (finiteClosedRestriction i A).Additive
  intersection_additive : ∀ s : Finset (Fin F.length),
    (finiteClosedRestriction (finiteClosedIntersection F.members s).hom A).Additive
  restriction : ∀ s t : Finset (Fin F.length),
    finiteClosedRestriction (finiteClosedIntersection F.members s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection F.members t).hom A
  restriction_unit : ∀ (s t : Finset (Fin F.length)), s ⊆ t →
    finiteClosedUnit (finiteClosedIntersection F.members s).hom A ≫ restriction s t =
      finiteClosedUnit (finiteClosedIntersection F.members t).hom A
  restriction_comp : ∀ (s t h : Finset (Fin F.length)), s ⊆ t → t ⊆ h →
    restriction s t ≫ restriction t h = restriction s h
  fromSupport : ∀ (s : Finset (Fin F.length)) (_hs : s.Nonempty),
    finiteClosedRestriction i A ⟶
      finiteClosedRestriction (finiteClosedIntersection F.members s).hom A
  fromSupport_unit : ∀ (s : Finset (Fin F.length)) (hs : s.Nonempty),
    finiteClosedUnit i A ≫ fromSupport s hs =
      finiteClosedUnit (finiteClosedIntersection F.members s).hom A
  fromSupport_comp : ∀ (s t : Finset (Fin F.length))
    (hs : s.Nonempty) (ht : t.Nonempty), s ⊆ t →
    fromSupport s hs ≫ restriction s t = fromSupport t ht
  rows : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤
    CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ
  additive : rows.Additive
  terms : ∀ p : ℕ, rows ⋙ HomologicalComplex.eval _ _ (p : ℤ) ≅
    finiteClosedTerms F.members A p
  differential : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
    (terms p).inv.app M ≫ (rows.obj M).d (p : ℤ) ((p : ℤ) + 1) ≫
      (terms (p + 1)).hom.app M =
        (finiteClosedDifferential F.members A restriction p).app M
  support : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℤ),
    p < 0 ∨ (F.length : ℤ) ≤ p → IsZero ((rows.obj M).X p)
  augment : finiteClosedRestriction i A ⟶ rows ⋙ HomologicalComplex.eval _ _ (0 : ℤ)
  augment_components : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
    (t : Fin 1 ↪o Fin F.length),
    augment.app M ≫ (terms 0).hom.app M ≫
      (finiteClosedTermProjection F.members A 0 t).app M =
        (fromSupport (Finset.univ.image t)
          ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩).app M
  alpha : finiteClosedRestriction i A ⋙
    HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⟶ rows
  alpha_f : ∀ M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A),
    (alpha.app M).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((finiteClosedRestriction i A).obj M)).hom ≫ augment.app M
  totalAugment : (finiteClosedRestriction i A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
    @finiteClosedTotal X A rows additive
  totalAugment_f : ∀ (K : CochainComplex
    (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) (n : ℤ),
    (totalAugment.app K).f n = augment.app (K.X n) ≫
      ((@finiteClosedDouble X A rows additive).obj K).ιTotal (ComplexShape.up ℤ)
        0 n n (Int.zero_add n)
```

The original module publicly imports `FiniteClosedCoverResolution` and
`Mathlib.Algebra.Homology.Single`.

## New

The same declarations, in `Sheaf.AlgebraicGeometry.ClosedRestrictionSignedData`:

```lean
structure SignedClosedFamily {X Z : Scheme.{u}} (i : Z ⟶ X) where
  length : ℕ
  positive : 0 < length
  members : Fin length → Over X
  closed : ∀ a, IsClosedImmersion (members a).hom
  factor : ∀ a, Nonempty (members a ⟶ Over.mk i)
  complement : ∀ a, ∃ U : X.Opens,
    Set.range U.ι = (Set.range (members a).hom)ᶜ ∧ QuasiCompact U.ι

structure SignedClosedRow {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : SignedClosedFamily i) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  support_additive : (finiteClosedRestriction i A).Additive
  intersection_additive : ∀ s : Finset (Fin F.length),
    (finiteClosedRestriction (finiteClosedIntersection F.members s).hom A).Additive
  restriction : ∀ s t : Finset (Fin F.length),
    finiteClosedRestriction (finiteClosedIntersection F.members s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection F.members t).hom A
  restriction_unit : ∀ (s t : Finset (Fin F.length)), s ⊆ t →
    finiteClosedUnit (finiteClosedIntersection F.members s).hom A ≫ restriction s t =
      finiteClosedUnit (finiteClosedIntersection F.members t).hom A
  restriction_comp : ∀ (s t h : Finset (Fin F.length)), s ⊆ t → t ⊆ h →
    restriction s t ≫ restriction t h = restriction s h
  fromSupport : ∀ (s : Finset (Fin F.length)) (_hs : s.Nonempty),
    finiteClosedRestriction i A ⟶
      finiteClosedRestriction (finiteClosedIntersection F.members s).hom A
  fromSupport_unit : ∀ (s : Finset (Fin F.length)) (hs : s.Nonempty),
    finiteClosedUnit i A ≫ fromSupport s hs =
      finiteClosedUnit (finiteClosedIntersection F.members s).hom A
  fromSupport_comp : ∀ (s t : Finset (Fin F.length))
    (hs : s.Nonempty) (ht : t.Nonempty), s ⊆ t →
    fromSupport s hs ≫ restriction s t = fromSupport t ht
  rows : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤
    CochainComplex (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ
  additive : rows.Additive
  terms : ∀ p : ℕ, rows ⋙ HomologicalComplex.eval _ _ (p : ℤ) ≅
    finiteClosedTerms F.members A p
  differential : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
    (terms p).inv.app M ≫ (rows.obj M).d (p : ℤ) ((p : ℤ) + 1) ≫
      (terms (p + 1)).hom.app M =
        (finiteClosedDifferential F.members A restriction p).app M
  support : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℤ),
    p < 0 ∨ (F.length : ℤ) ≤ p → IsZero ((rows.obj M).X p)
  augment : finiteClosedRestriction i A ⟶ rows ⋙ HomologicalComplex.eval _ _ (0 : ℤ)
  augment_components : ∀ (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
    (t : Fin 1 ↪o Fin F.length),
    augment.app M ≫ (terms 0).hom.app M ≫
      (finiteClosedTermProjection F.members A 0 t).app M =
        (fromSupport (Finset.univ.image t)
          ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩).app M
  alpha : finiteClosedRestriction i A ⋙
    HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⟶ rows
  alpha_f : ∀ M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A),
    (alpha.app M).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((finiteClosedRestriction i A).obj M)).hom ≫ augment.app M
  totalAugment : (finiteClosedRestriction i A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
    @finiteClosedTotal X A rows additive
  totalAugment_f : ∀ (K : CochainComplex
    (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) (n : ℤ),
    (totalAugment.app K).f n = augment.app (K.X n) ≫
      ((@finiteClosedDouble X A rows additive).obj K).ιTotal (ComplexShape.up ℤ)
        0 n n (Int.zero_add n)
```

The data module publicly imports the shared `FiniteClosedRowConstructions` and
`Mathlib.Algebra.Homology.Single`. The original module keeps its public import of
`FiniteClosedCoverResolution`, publicly imports the data module, and privately imports
the two new construction statements. All previously public dependencies remain publicly
reachable; only their import path changes. No field is added, removed or changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements | C4 | Publicly re-exports relocated structures; unchanged system and theorem signatures. |
| Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRows | C4, new | States individual row existence using the common data module. |
| Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRowMaps | C4, new | States row refinement existence for already supplied rows. |

A search of both live Lean roots finds no existing direct importer of the assigned
module and no other existing user of either relocated name. The assigned item is still
needed in its parents' DAG proof plans; neither it nor any parent is withdrawn. All four
modules of this delivery are checked together through `lcompile.py --all`.

## Status

landed 20261026T081218-L-1873471 2026-10-26 (merge of deliver/C4/Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements)
