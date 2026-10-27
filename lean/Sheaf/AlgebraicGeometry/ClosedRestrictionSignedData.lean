/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.FiniteClosedRowConstructions
public import Mathlib.Algebra.Homology.Single

/-!
# Data for signed closed-restriction rows

The family and row structures are relocated verbatim from the signed-refinement module.
Source: Stacks Project, Tags 09AH and 01FG; the agent's signed construction.
(blueprint: def-sfb-signed-closed-row-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- An ordered nonempty closed family inside Z, with quasi-compact open complements
in X. Factorizations are morphisms over X, so they retain the scheme structures.
Source: the ordered-family data in the agent deduction from Stacks Tag 09AH
(blueprint: def-sfb-signed-closed-row-data). -/
structure SignedClosedFamily {X Z : Scheme.{u}} (i : Z ⟶ X) where
  length : ℕ
  positive : 0 < length
  members : Fin length → Over X
  closed : ∀ a, IsClosedImmersion (members a).hom
  factor : ∀ a, Nonempty (members a ⟶ Over.mk i)
  complement : ∀ a, ∃ U : X.Opens,
    Set.range U.ι = (Set.range (members a).hom)ᶜ ∧ QuasiCompact U.ι

/-- A signed row with its actual unit-normalized restrictions. The unit equations
characterize the restrictions: the closed units are epimorphisms by Tag 09AH.
`alpha` is the degree-zero chain augmentation; equivalently it supplies column -1
of the augmented row. Its domain is E_Z concentrated in degree zero. The support
condition gives zero outside columns 0,...,m-1, including the empty tuple ranges.
No object is selected from this structure in any definition.
Source: the signed-complex deduction from Stacks Tags 09AH and 01FG
(blueprint: def-sfb-signed-closed-row-data). -/
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

end AlgebraicGeometry
