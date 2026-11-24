/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIso

/-! # Columnwise comparison of cutoff quotients and smart windows

## References

* [Stacks Project, Tag 012X](https://stacks.math.columbia.edu/tag/012X), smart truncations
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def windowProjection (a b : ℤ) :
    verticalCutoff (C := C) b ⟶ verticalWindow a b :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight
      (Functor.whiskerRight ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans C)
        ((ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C))
      (ComplexShape.embeddingUpNat.restrictionFunctor C))

/-- The quotient of nested cutoffs has a columnwise quasi-isomorphism to the window. -/
theorem verticalCutoff_cokernel_column_comparison
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (a b : ℤ) (hab : a ≤ b)
    (f : (((verticalCutoff a).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ⟶
      (((verticalCutoff b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    (hf : f ≫ ((verticalCutoffι b).mapHomologicalComplex (ComplexShape.up ℕ)).app K =
      ((verticalCutoffι a).mapHomologicalComplex (ComplexShape.up ℕ)).app K) :
    ∃ q : cokernel f ⟶
      (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K),
      ∀ p : ℕ, QuasiIso (q.f p) := by
  let β := ((windowProjection (C := C) a b).mapHomologicalComplex
    (ComplexShape.up ℕ)).app K
  have hβ : f ≫ β = 0 := by
    ext p : 1
    let L : CochainComplex C ℤ := (K.X p).extend ComplexShape.embeddingUpNat
    let j := HomologicalComplex.restrictionMap
      (CochainComplex.ιTruncLE (CochainComplex.truncGE L a) (b - 1)) ComplexShape.embeddingUpNat
    have : Mono j := by
      apply HomologicalComplex.mono_of_mono_f
      intro n
      change Mono ((HomologicalComplex.ιTruncLE (CochainComplex.truncGE L a)
        (ComplexShape.embeddingUpIntLE (b - 1))).f (ComplexShape.embeddingUpNat.f n))
      infer_instance
    apply (cancel_mono j).1
    change (f.f p ≫ HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap (CochainComplex.πTruncGE L a) (b - 1))
        ComplexShape.embeddingUpNat) ≫ j = 0 ≫ j
    rw [Category.assoc]
    change f.f p ≫ HomologicalComplex.restrictionMap _ _ ≫
      HomologicalComplex.restrictionMap _ _ = _
    rw [← HomologicalComplex.restrictionMap_comp, CochainComplex.ιTruncLE_naturality]
    rw [HomologicalComplex.restrictionMap_comp, ← Category.assoc]
    have hp := congrArg (fun g ↦ g.f p) hf
    change f.f p ≫ HomologicalComplex.restrictionMap (CochainComplex.ιTruncLE L (b - 1))
      ComplexShape.embeddingUpNat = HomologicalComplex.restrictionMap
        (CochainComplex.ιTruncLE L (a - 1)) ComplexShape.embeddingUpNat at hp
    rw [hp, ← HomologicalComplex.restrictionMap_comp]
    have hz : CochainComplex.ιTruncLE L (a - 1) ≫ CochainComplex.πTruncGE L a = 0 :=
      (ComplexShape.Embedding.embeddingUpInt_areComplementary (a - 1) a (by omega)).hom_ext _
    rw [hz]
    simp only [zero_comp]
    ext n
    rfl
  let q := cokernel.desc f β hβ
  refine ⟨q, ?_⟩
  intro p
  let E := HomologicalComplex.eval (CochainComplex C ℕ) (ComplexShape.up ℕ) p
  let e := PreservesCokernel.iso E f
  have hp := congrArg (fun g ↦ g.f p) hf
  have hq : cokernel.π (f.f p) ≫ (e.inv ≫ q.f p) = β.f p := by
    change cokernel.π (E.map f) ≫ (e.inv ≫ E.map q) = E.map β
    simp [e, q]
  have := verticalCutoff_column_quasiIso (K.X p) a b hab (f.f p) hp
    (e.inv ≫ q.f p) hq
  exact quasiIso_of_comp_left e.inv (q.f p)

end HomologicalComplex₂
