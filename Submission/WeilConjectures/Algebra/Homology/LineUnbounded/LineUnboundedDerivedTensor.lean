/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Submission.WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import Submission.WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Unbounded derived tensor with a locally free line

Source: Stacks Project, Tags 0B8N, 0B8Q, 06YN, 06YT, 06YU and 015F;
blueprint main-20261015, Tate-twist local freeness, proof (3).
(blueprint: lem-pur-line-unbounded-derived-tensor)

The tensor bifunctor is the published K-flat derived tensor. The representative
normalizations below specify the actual evaluation transformations, including their
triangle identities. The ring of global sections acts canonically; restriction along
any B-algebra structure B → Γ(R) gives every asserted B-linearity statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t a w u v b

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace SheafOfModules.LineUnbounded

section Localization

variable {C D : Type*} [Category C] [Category D]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (T S : C ⥤ C) (F G : D ⥤ D)
  (cF : Q ⋙ F ≅ T ⋙ Q) (cG : Q ⋙ G ≅ S ⋙ Q)

private def cancellationComparison (e : T ⋙ S ≅ 𝟭 C) : Q ⋙ (F ⋙ G) ≅ Q :=
  (Functor.associator Q F G).symm ≪≫ Functor.isoWhiskerRight cF G ≪≫
    Functor.associator T Q G ≪≫ Functor.isoWhiskerLeft T cG ≪≫
    (Functor.associator T S Q).symm ≪≫ Functor.isoWhiskerRight e Q ≪≫
    Functor.leftUnitor Q

private def localizedCancellation (e : T ⋙ S ≅ 𝟭 C) : F ⋙ G ≅ 𝟭 D :=
  Localization.liftNatIso Q W _ _ _ _
    (cancellationComparison Q T S F G cF cG e ≪≫ (Functor.rightUnitor Q).symm)

end Localization

variable (X : Scheme.{t})
  [EssentiallySmall.{max a (t + 1)} X.ProEt]
  (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})

/-- The existing module category on the small pro-etale site.
Source: Stacks, 03DA (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev Modules := KFlatFixedTensor.Modules.{t + 1, t, max a (t + 1)} R

/-- Global sections of the given commutative ring sheaf, with the coefficient size fixed.
Source: Stacks, 04TT (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev scalars := RingCat.sectionsSubring
  (R.obj ⋙ forget₂ CommRingCat.{max a (t + 1)} RingCat.{max a (t + 1)})

/-- The existing global-section action on module morphisms, componentwise on sections.
Source: Stacks, 04TT (blueprint: lem-pur-line-unbounded-derived-tensor). -/
instance coefficientLinear : Linear (scalars.{t, a} X R) (Modules.{t, a} X R) :=
  SheafOfModules.homLinear.{max a (t + 1), t, t + 1, max a (t + 1)} R.obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max a (t + 1)} RingCat.{max a (t + 1)})).obj R).property

/-- Ordinary tensor with a fixed right factor.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def tensor (P : Modules.{t, a} X R) : Modules.{t, a} X R ⥤ Modules.{t, a} X R := tensorRight P

/-- Additivity of the existing ordinary tensor functor.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
instance tensorAdditive (P : Modules.{t, a} X R) : (tensor.{t, a} X R P).Additive :=
  inferInstanceAs (tensorRight P).Additive

/-- A module in degree zero in the unbounded cochain category.
Source: Stacks, 06YN (blueprint: lem-pur-line-unbounded-derived-tensor). -/
abbrev single (P : Modules.{t, a} X R) : CochainComplex (Modules.{t, a} X R) ℤ :=
  (CochainComplex.singleFunctor (Modules.{t, a} X R) 0).obj P

/-- The canonical pure tensor in the localization tensor, via the sheafification unit.
Source: Stacks, 03EK (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def pureTensor (P Q : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U) : (P ⊗ Q).val.obj U :=
  (tensorObjIsoSheafification P Q).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app (P.val ⊗ Q.val)).app U
          (p ⊗ₜ[R.obj.obj U] q))

/-- Associate, evaluate the last two factors, then apply the right unitor.
Source: Stacks, 0B8N (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def cancellation (P Q : Modules.{t, a} X R) (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X R)) :
    tensor.{t, a} X R P ⋙ tensor.{t, a} X R Q ≅ 𝟭 (Modules.{t, a} X R) :=
  (tensorRightTensor P Q).symm ≪≫ (tensoringRight (Modules.{t, a} X R)).mapIso e ≪≫
    rightUnitorNatIso (Modules.{t, a} X R)

/-- Collapse the total tensor with a degree-zero right factor to termwise tensor.
Source: Stacks, 06YU (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def collapse (P : Modules.{t, a} X R) :
    (KFlatFixedTensor.totalTensor.{t + 1, t, max a (t + 1)} R).flip.obj (single.{t, a} X R P) ≅
      (tensor.{t, a} X R P).mapHomologicalComplex (.up ℤ) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (KFlatFixedTensor.ordinaryTensor.{t + 1, t, max a (t + 1)} R) P

variable [HasDerivedCategory.{w} (Modules.{t, a} X R)]

/-- Tensor with the degree-zero object using exactly the published derived tensor.
Source: Stacks, 06YU (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def derived (P : Modules.{t, a} X R) :
    DerivedCategory (Modules.{t, a} X R) ⥤ DerivedCategory (Modules.{t, a} X R) :=
  (KFlatFixedTensor.derivedTensor.{t + 1, t, max a (t + 1), w} R).flip.obj
    (DerivedCategory.Q.obj (single.{t, a} X R P))

/-- The canonical normalization of a termwise comparison on resolving complexes.
It uses the actual K-flat representative comparison and the degree-zero total collapse.
Source: Stacks, 06YU and 015F (blueprint: lem-pur-line-unbounded-derived-tensor). -/
def normalization (P : Modules.{t, a} X R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (single.{t, a} X R P))
    (hPf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) ((single.{t, a} X R P).X n))
    (F : DerivedCategory (Modules.{t, a} X R) ⥤ DerivedCategory (Modules.{t, a} X R))
    (hF : F = derived.{t, a} X R P) (K : CochainComplex (Modules.{t, a} X R) ℤ)
    (c : F.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj
      (((tensor.{t, a} X R P).mapHomologicalComplex (.up ℤ)).obj K)) : Prop :=
  ∀ (hK : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) K)
    (hKf : ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (K.X n)),
    c = eqToIso (congrArg (fun H ↦ H.obj (DerivedCategory.Q.obj K)) hF) ≪≫
      (KFlatFixedTensor.representativeIso.{t + 1, t, max a (t + 1), w} R K
        (single.{t, a} X R P) hK hP hKf hPf).symm ≪≫
          DerivedCategory.Q.mapIso ((collapse.{t, a} X R P).app K)

end SheafOfModules.LineUnbounded
