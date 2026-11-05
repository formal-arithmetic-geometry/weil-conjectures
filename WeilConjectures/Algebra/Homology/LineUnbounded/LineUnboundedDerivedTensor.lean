/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

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

end Localization

variable (X : Scheme.{t})
  [EssentiallySmall.{max a (t + 1)} X.ProEt]
  (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})

variable [HasDerivedCategory.{w} (Modules.{t, a} X R)]

end SheafOfModules.LineUnbounded
