/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Paper.ModuleCupHZeroIdentification
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Canonical H-zero comparison and its flat-model transport

Source: Stacks Project, Tag 06YH, derived tensor and its comparison to ordinary tensor.
-/

@[expose] public section

universe w v u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{w} C]

noncomputable section

/-- The total tensor of the two degree-zero complexes is the ordinary tensor in degree zero.
This uses the tensor/single comparison followed by the termwise functor/single comparison. -/
def moduleCup_singleTensorIso (F G : C) :
    (CochainComplex.singleFunctor C 0).obj F ⊗
      (CochainComplex.singleFunctor C 0).obj G ≅
        (CochainComplex.singleFunctor C 0).obj (F ⊗ G) :=
  (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) G).app
      ((CochainComplex.singleFunctor C 0).obj F) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorRight G) (.up ℤ) 0).app F

/-- H-zero of the canonical derived-to-ordinary tensor comparison is invertible.
Source: Stacks Project, Tag 06YH, flat construction of derived tensor.
(blueprint: lem-sc-module-cup-canonical-hzero-identification)
Here F₀ and G₀ are the actual single complexes. Their total tensor is canonically
(F tensor G)[0], so the first assertion identifies H-zero of the derived tensor
with F tensor G. The second assertion specifies the transport for every strictly
nonpositive termwise-flat K-flat resolution p:P→F₀: tensor the localized p with
the identity of QG₀, invert this isomorphism, then use the recorded K-flat-model
isomorphism and Q of p tensor identity. This composite is the canonical Q tensor
comparison itself, not merely some isomorphism with the same endpoints.
Proof: a bounded-above flat resolution is K-flat. Right exactness of tensor and
the cokernel calculation in moduleCup_hzero_identification give invertibility
on H-zero in this model. Naturality of the lax tensor comparison of Q, and the
fact that its component at a K-flat left factor is the displayed flat-model
isomorphism, give the transport equation. The localized resolution and its tensor
with the identity are invertible. Transporting the model H-zero isomorphism
therefore proves the first assertion. The canonical single-complex isomorphisms
identify its target with the ordinary tensor, without flatness of F or G. -/
theorem moduleCup_canonical_hzero_identification (F G : C) :
    let F₀ := (CochainComplex.singleFunctor C 0).obj F
    let G₀ := (CochainComplex.singleFunctor C 0).obj G
    let c := Functor.LaxMonoidal.μ Q F₀ G₀ ≫ Q.map (moduleCup_singleTensorIso F G).hom
    IsIso ((homologyFunctor C 0).map c) ∧
      ∀ (P : CochainComplex C ℤ) (p : P ⟶ F₀)
        [P.IsStrictlyLE 0] [QuasiIso p]
        (_hflat : ∀ i : ℤ, ObjectProperty.flat (P.X i))
        (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P),
        c =
          (tensorIso (asIso (Q.map p)) (Iso.refl (Q.obj G₀))).inv ≫
            (QObjTensorQObjIsoOfKFlatLeft P G₀ hP).hom ≫
            Q.map (p ⊗ₘ 𝟙 G₀) ≫ Q.map (moduleCup_singleTensorIso F G).hom := by sorry

end
end DerivedCategory
