/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure

import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# K-flat resolutions and the homotopy derivability structure

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-kflat-derivability).

The hypotheses and conclusions are stated for an arbitrary Grothendieck abelian monoidal
category.  The K-flat property on the homotopy category is expressed by the existence of a
K-flat cochain-complex representative; the quotient and its localizer morphism provide the
full subcategory and its restricted quasi-isomorphisms.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/--
Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-kflat-derivability).

Proof plan.  A Grothendieck abelian category has small colimits and exact filtered colimits;
the two-sided flat objects contain zero and are closed under finite sums and direct summands,
so the supplied functorial flat epimorphisms are covers by the flat class.  The functorial
bounded-above flat-resolution statement gives one functor on all bounded-above complexes,
with a natural quasi-isomorphism and flat terms, compatible with every upper bound.  Apply it
to good truncations and take their integer-indexed termwise colimit to obtain a functor `R`
on all unbounded complexes and a natural map `r` to the identity.  Exactness of filtered
colimits identifies cohomology of this colimit with the colimit of the cohomologies, so each
component of `r` is a quasi-isomorphism.  The bounded-above flat-complex result makes each
stage two-sided K-flat.  Tensoring the colimit with a quasi-isomorphism commutes with the
colimit in either variable because tensoring preserves all small colimits; the stagewise
quasi-isomorphisms therefore show that every `R`-value is K-flat.  K-flatness is invariant
under homotopy and closed under zero, shifts and cones by the K-flat homotopy-triangulated
statement.  Finally apply the homotopy-resolution derivability criterion to `R` and `r`;
this gives the left derivability structure on the full subcategory of `K(C)` consisting of
objects with K-flat representatives.  The construction is functorial on complexes only.
-/
theorem kFlat_derivability
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X : C), PreservesColimits (tensorLeft X)]
    [∀ (X : C), PreservesColimits (tensorRight X)]
    (P : C ⥤ C) (p : P ⟶ 𝟭 C)
    (hflat : ∀ X : C, ObjectProperty.flat (P.obj X))
    (hepi : ∀ X : C, Epi (p.app X)) :
    ∃ (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (r : R ⟶ 𝟭 (CochainComplex C ℤ)),
      (∀ X : CochainComplex C ℤ, (R.obj X).IsKFlatForTotalTensor) ∧
      (∀ X : CochainComplex C ℤ, QuasiIso (r.app X)) ∧
      (HomotopyCategory.quasiIsoLocalizerMorphism
        (fun K : HomotopyCategory C (.up ℤ) =>
          ∃ X : CochainComplex C ℤ,
            (HomotopyCategory.quotient C (.up ℤ)).obj X = K ∧
              X.IsKFlatForTotalTensor)).IsLeftDerivabilityStructure := by
  -- Shrink the colimit hypotheses to the integer and graded-coproduct shapes.
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
  have (X : C) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    preservesColimitsOfSize_shrink (tensorLeft X)
  have (X : C) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    preservesColimitsOfSize_shrink (tensorRight X)
  have : HasExactColimitsOfShape ℤ C := by
    have := AB5OfSize_of_univLE.{0, 0, v, v} C
    infer_instance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
    intro i j
    infer_instance
  -- The binary total tensor and the source monoidal tensor have the same maps.
  have hiff (X : CochainComplex C ℤ) :
      X.IsKFlatForTotalTensor ↔ (HomologicalComplex.quasiIso C (.up ℤ)).kFlat X := by
    rfl
  have hprop :
      (fun K : HomotopyCategory C (.up ℤ) ↦
        ∃ X : CochainComplex C ℤ, (HomotopyCategory.quotient C (.up ℤ)).obj X = K ∧
          X.IsKFlatForTotalTensor) = (HomotopyCategory.quasiIso C (.up ℤ)).kFlat := by
    funext K
    apply propext
    constructor
    · rintro ⟨X, rfl, hX⟩
      exact (HomotopyCategory.kFlat_quotient_obj_iff X).2 ((hiff X).1 hX)
    · intro hK
      obtain ⟨X, rfl⟩ := K.quotient_obj_surjective
      exact ⟨X, rfl, (hiff X).2 ((HomotopyCategory.kFlat_quotient_obj_iff X).1 hK)⟩
  -- Reduction removes the zero summand without requiring additivity of P.
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) :=
    { F := ObjectProperty.lift _ P hflat
      π := p
      epi_π_app := hepi }
  let Γ := Λ.reduced
  have hΓ (X : CochainComplex C ℤ) :=
    Γ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le X
  refine ⟨Γ.resolutionFunctor, Γ.resolutionNatTrans, ?_, ?_, ?_⟩
  · intro X
    exact (hiff _).2 (hΓ X)
  · intro X
    infer_instance
  · rw [hprop]
    exact Γ.homotopyCategory_kFlat_isLeftDerivabilityStructure
      ObjectProperty.flat.essImage_ι_le

end CategoryTheory
