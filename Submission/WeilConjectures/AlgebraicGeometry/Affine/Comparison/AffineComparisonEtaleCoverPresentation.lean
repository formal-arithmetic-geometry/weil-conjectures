/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Submission.WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Submission.WeilConjectures.CategoryTheory.Pro.Generating
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Simultaneous affine étale presentations of a finite covering family

Source: Stacks Project, Tag 099U, the geometric finite-cover reductions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace AlgebraicGeometry.ProEtale

private theorem exists_surjective_presentation
    {Y : Scheme.{u}} {A B : Y.AffineProEt} (q : A ⟶ B) [Surjective q.left] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (pA : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) A)
      (pB : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) B)
      (f : pA.Hom pB), f.map = q ∧
      ∀ i, Sieve.generate (Presieve.singleton (f.natTrans.app i)) ∈
        Scheme.AffineEtale.topology Y (pB.diag.obj i) := by
  have hrel : PreZeroHypercover.IsRelativelyPresentable.{u}
      (Scheme.AffineEtale.toAffineProEt Y) (Scheme.AffineEtale.topology Y)
      (Presieve.singleton q).preZeroHypercover := by
    apply Scheme.AffineProEt.singleton_inf_le_relativelyPresentable
    refine ⟨⟨A, q, rfl⟩, ?_⟩
    rw [MorphismProperty.singleton_mem_precoverage_iff]
    infer_instance
  obtain ⟨I, _, _, p, hp⟩ := hrel
  let a₀ : (Presieve.singleton q).preZeroHypercover.I₀ :=
    ⟨⟨A, q⟩, Presieve.singleton.mk⟩
  have ha (a : (Presieve.singleton q).preZeroHypercover.I₀) : a = a₀ := by
    rcases a with ⟨⟨Z, t⟩, ht⟩
    cases ht
    rfl
  refine ⟨I, inferInstance, inferInstance, p.pres₀ a₀, p.pres, p.f a₀, p.hf a₀, ?_⟩
  intro i
  have he : (p.preZeroHypercover i).sieve₀ =
      Sieve.generate (Presieve.singleton ((p.f a₀).natTrans.app i)) := by
    apply congrArg Sieve.generate
    apply le_antisymm
    · rintro Z t ⟨a⟩
      obtain rfl := ha a
      exact Presieve.singleton.mk
    · rintro Z t ⟨⟩
      exact ⟨a₀⟩
  rw [← he]
  exact hp i

end AlgebraicGeometry.ProEtale
