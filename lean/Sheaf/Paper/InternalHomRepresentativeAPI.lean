/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Sheaf.Paper.DerivedInternalHomFilteredColimitData
import all Sheaf.Paper.InternalHomFiniteFreeStage
import all Sheaf.Paper.InternalHomFilteredContinuity

/-! # Interface to the strict coefficient representative calculations

The canonical pure tensors, their degree-zero total-tensor comparison, exactness,
and resolution properties are exposed without importing their private implementations.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v r w a
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures.SfbHomFilteredColimit.RepresentativeAPI
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-- The sheafification-unit pure tensor in the ordinary sheaf tensor product.
Source: Stacks 03EK (blueprint: lem-sfb-strict-representative-interface). -/
noncomputable def pure (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    letI := SheafOfModules.monoidalCategory R
    (A ⊗ B).val.obj U :=
  letI := SheafOfModules.monoidalCategory R
  (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max u v r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r}
        RingCat.{max u v r})).obj R).obj)).unit.app (A.val ⊗ B.val)).app U
          (a ⊗ₜ[R.obj.obj U] b))

/-- The canonical comparison for tensor with a degree-zero single complex.
Source: Stacks 06YN (blueprint: lem-sfb-strict-representative-interface). -/
noncomputable def singleTensorIso (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    let := SheafOfModules.monoidalCategory R
    (tensor.{u, v, r} J R).obj (T, B) ≅
      ((MonoidalCategory.tensorLeft T).mapHomologicalComplex (.up ℤ)).obj B := by
  let := SheafOfModules.monoidalCategory R
  exact CochainComplex.mapBifunctorSingle₁Iso (MonoidalCategory.curriedTensor _) T B


/-- The canonical representative calculation `tensorGenerator_hom`.
Source: Stacks 03EK, 06YN, 079P and 0A95
(blueprint: lem-sfb-strict-representative-interface).
Proof: apply the proved representative calculation in the data module;
its canonical constructions agree definitionally with the interface above. -/
theorem tensorGenerator_hom (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    let := SheafOfModules.monoidalCategory R
    ((singleTensorIso.{u, v, r} J R T B).hom.f n).val.app U
        (tensorGenerator.{u, v, r} J R T B n U t b) =
      pure.{u, v, r} J R T (B.X n) U t b := by
  exact WeilConjectures.SfbHomFilteredColimit.tensorGenerator_hom.{u, v, r} J R T B n U t b

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
/-- The canonical representative calculation `homValue_map_right`.
Source: Stacks 03EK, 06YN, 079P and 0A95
(blueprint: lem-sfb-strict-representative-interface).
Proof: apply the proved representative calculation in the data module;
its canonical constructions agree definitionally with the interface above. -/
theorem homValue_map_right (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : Q ⟶ Q')
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (z : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q' n p q hpq U
        (((((homComplexFunctor (R := R)).obj (op P)).map g).f n).val.app U z) x =
      (g.f q).val.app U (homValue.{u, v, r} J R P Q n p q hpq U z x) := by
  exact WeilConjectures.SfbHomFilteredColimit.homValue_map_right.{u, v, r} J R P g n p q hpq U z x

/-- The canonical representative calculation `tensorPreadditive`.
Source: Stacks 03EK, 06YN, 079P and 0A95
(blueprint: lem-sfb-strict-representative-interface).
Proof: this is the established strict representative calculation. -/
theorem tensorPreadditive (R : Sheaf J CommRingCat.{max u v r}) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    MonoidalPreadditive (Modules.{u, v, r} J R) := by
  exact WeilConjectures.SfbHomFilteredColimit.tensorPreadditive.{u, v, r} J R

/-- The canonical representative calculation `resolutionProperties`.
Source: Stacks 03EK, 06YN, 079P and 0A95
(blueprint: lem-sfb-strict-representative-interface).
Proof: this is the established strict representative calculation. -/
theorem resolutionProperties (R : Sheaf J CommRingCat.{max u v r})
    (K : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    QuasiIso ((resolutionUnit.{u, v, r} J R).app K) ∧
      ((coefficientHomResolution.{r, u, v} J R).obj K).IsKInjective := by
  exact WeilConjectures.SfbHomFilteredColimit.resolutionProperties.{u, v, r} J R K

/-- The canonical representative calculation `homFixedQuasiIso`.
Source: Stacks 03EK, 06YN, 079P and 0A95
(blueprint: lem-sfb-strict-representative-interface).
Proof: this is the established strict representative calculation. -/
theorem homFixedQuasiIso (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {K L : CochainComplex (Modules.{u, v, r} J R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((homFixed.{u, v, r} J R P).map f) := by
  exact WeilConjectures.SfbHomFilteredColimit.homFixedQuasiIso.{u, v, r} J R P f

/-- Pure tensors detect maps into every component of the product Hom complex.
Source: Stacks 03EK and 0A8X (blueprint: lem-sfb-strict-representative-interface).
Proof: the single-complex tensor isomorphism reduces to ordinary pure tensor
extensionality, then Hom-product projections and evaluation on every slice. -/
theorem tensorGenerator_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (B P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n m : ℤ)
    (a b : ((tensor.{u, v, r} J R).obj (T, B)).X n ⟶
      (homComplex (R := R) P Q).X m)
    (h : ∀ (p q : ℤ) (hpq : p + m = q) (U : Cᵒᵖ)
      (t : T.val.obj U) (z : (B.X n).val.obj U) (x : (P.X p).val.obj U),
      homValue.{u, v, r} J R P Q m p q hpq U
          (a.val.app U (tensorGenerator.{u, v, r} J R T B n U t z)) x =
        homValue.{u, v, r} J R P Q m p q hpq U
          (b.val.app U (tensorGenerator.{u, v, r} J R T B n U t z)) x) : a = b := by
  exact WeilConjectures.SfbHomFilteredColimit.tensorGenerator_hom_ext.{u, v, r}
    J R T B P Q n m a b h

section Exactness
variable {A : Type a} [Category.{w} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A]

/-- Finite-free tensor is exact, including rank zero.
Source: Stacks 06YN (blueprint: lem-sfb-strict-representative-interface).
Proof: tensor is a finite direct sum of the identity. -/
theorem tensorLeft_finiteFree_exact (d : ℕ) :
    PreservesFiniteLimits
      (tensorLeft (limit (Discrete.functor (fun _ : Fin d ↦ 𝟙_ A)))) := by
  exact WeilConjectures.SfbHomFilteredColimit.tensorLeft_finiteFree_exact d

variable [HasColimitsOfSize.{w, w} A]
  [∀ X : A, PreservesColimitsOfSize.{w, w} (tensorRight X)]
  {I : Type w} [SmallCategory I] [HasExactColimitsOfShape I A]

omit [Abelian A] [MonoidalPreadditive A] in
/-- Tensor by an exact colimit of flat objects is exact.
Source: Stacks 06YN (blueprint: lem-sfb-strict-representative-interface).
Proof: commute tensor with the colimit and use exactness of that colimit. -/
theorem tensorLeft_colimit_exact (T : I ⥤ A)
    (hT : ∀ i, PreservesFiniteLimits (tensorLeft (T.obj i))) :
    PreservesFiniteLimits (tensorLeft (colimit T)) := by
  exact WeilConjectures.SfbHomFilteredColimit.tensorLeft_colimit_exact T hT
end Exactness
end WeilConjectures.SfbHomFilteredColimit.RepresentativeAPI
