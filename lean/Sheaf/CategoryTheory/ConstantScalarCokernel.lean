/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import all Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
import all Sheaf.Paper.PurInverseImageScalarComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Constant module realization preserves cokernels

Source: Stacks Project, Tags 03CY, 03EI and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

/-- Constant module sheafification followed by scalar extension preserves every
cokernel, with its prescribed quotient map. No flatness assumption is needed.
Source: Stacks Project, Tags 03CY, 03EI and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
(blueprint: lem-per-constant-scalar-cokernel).

Proof: The underlying additive constant sheaf functor preserves finite colimits:
it is constant presheaf formation followed by left adjoint sheafification, and
ordinary modules have colimits on their underlying abelian groups. The forgetful
functor from module sheaves preserves and reflects these colimits, so the constant
module functor preserves finite colimits. Extension of scalars is left adjoint to
restriction of scalars, hence also preserves finite colimits. Their composite
therefore preserves cokernels. The canonical cokernel comparison has the stated
quotient-map equation. -/
theorem constantScalarCokernel {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [CommRing R]
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [HasWeakSheafify J RingCat.{max u v}]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (B : Sheaf J CommRingCat.{max u v})
    (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)
    {M N : ModuleCat.{max u v} R} (d : M ⟶ N) :
    ∃ w : extension J R B σ (cokernel d) ≅ cokernel (extensionMap J R B σ d),
      extensionMap J R B σ (cokernel.π d) ≫ w.hom =
        cokernel.π (extensionMap J R B σ d) := by
  let H := constantModuleHomFunctor J R
  let G := SheafOfModules.toSheaf (homRing J R)
  have : PreservesFiniteColimits (H ⋙ G) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ constantSheaf J AddCommGrpCat)
    have : PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{max u v}) :=
      comp_preservesFiniteColimits _ _
    exact comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits H := preservesFiniteColimits_of_reflects_of_preserves H G
  let T := AlgebraicGeometry.Scheme.PurScalar.tensorFunctor σ
  have : T.IsLeftAdjoint :=
    (AlgebraicGeometry.Scheme.PurScalar.tensorAdjunction σ).isLeftAdjoint
  have : PreservesFiniteColimits (H ⋙ T) := comp_preservesFiniteColimits _ _
  let F := extensionFunctor J R B σ
  have : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits (H ⋙ T))
  have : F.PreservesZeroMorphisms := by infer_instance
  exact ⟨PreservesCokernel.iso F d, PreservesCokernel.π_iso_hom F d⟩

end CategoryTheory.ConstantFiniteFreePresentationExtension
