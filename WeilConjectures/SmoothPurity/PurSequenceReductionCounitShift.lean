/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurSequenceReductionCounitResolutionShift
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Descent of the quotient counit shift compatibility

Source: Stacks 06YY and 0G7D; descent through the universal left-derived
counit.
(blueprint: lem-pur-sequence-reduction-counit-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

set_option linter.unusedVariables false in
/-- Shift compatibility of the quotient counit descends from all resolving
representatives by the universal property of the left-derived functor.
Source: Stacks sites-cohomology.tex, Tags 06YY and 0G7D.
(blueprint: lem-pur-sequence-reduction-counit-shift).

Proof: choose a flat-term K-flat resolution of each complex. The derived source
functor sends its augmentation to an isomorphism, as it does the shifted
augmentation. Precompose the shift square with this latter isomorphism and use
naturality of the counit and both shift comparisons. It becomes the supplied
square on the resolving complex, proving the desired equality by cancellation.
-/
theorem purSequenceReductionCounitShift
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : PurReductionLimitShiftData l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O)
    (hres : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)),
      letI := D.reduction_shift
      ((DerivedCategory.Q ⋙ S.reduction).commShiftIso r).hom.app Q ≫
          (A.reductionCounit.app Q)⟦r⟧' =
        A.reductionCounit.app (Q⟦r⟧) ≫
          ((O.pullback.mapHomologicalComplex (.up ℤ) ⋙
            DerivedCategory.Q).commShiftIso r).hom.app Q) :
    letI := D.reduction_shift
    NatTrans.CommShift A.reductionCounit ℤ := by
  let := D.reduction_shift
  let F₁ := DerivedCategory.Q ⋙ S.reduction
  have hresolve : ∀ (X : CochainComplex (scalarReductionSource l E W) ℤ),
      ∃ (Y : CochainComplex (scalarReductionSource l E W) ℤ)
        (f : Y ⟶ X),
        CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W)
          (R := completedIntegralCommRingSheafUnrestricted l E W) Y ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := Scheme.ProEt.topology W)
          (R := completedIntegralCommRingSheafUnrestricted l E W) (Y.X i)) ∧
        IsIso (F₁.map f) := by
    intro X
    obtain ⟨Y, f, hY, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
    have : QuasiIso f := hf
    have hflat' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (Y.X i) := by
      intro i
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted l E W) (Y.X i)).symm (hflat i)
    refine ⟨Y, f, hY, hflat', ?_⟩
    change IsIso (S.reduction.map (DerivedCategory.Q.map f))
    infer_instance
  refine { shift_comm := ?_ }
  intro r
  ext X
  obtain ⟨Y, f, hY, hflat, hf⟩ := hresolve X
  have : IsIso (F₁.map f) := hf
  have hYsq := hres Y r hY hflat
  have hshift : IsIso (F₁.map (f⟦r⟧')) := by
    have heq : F₁.map (f⟦r⟧') =
        (F₁.commShiftIso r).hom.app Y ≫ (F₁.map f)⟦r⟧' ≫
          (F₁.commShiftIso r).inv.app X := by
      rw [← Functor.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, Category.comp_id]
    rw [heq]
    infer_instance
  rw [← cancel_epi (F₁.map (f⟦r⟧'))]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    A.reductionCounit.naturality, Functor.map_comp, reassoc_of% hYsq,
    A.reductionCounit.naturality_assoc, Functor.commShiftIso_hom_naturality]

end WeilConjectures
