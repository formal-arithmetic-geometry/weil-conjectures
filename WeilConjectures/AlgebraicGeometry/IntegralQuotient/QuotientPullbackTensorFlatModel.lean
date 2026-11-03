/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorNormalization
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation

/-! # The quotient tensor square on resolving complexes

Source: Stacks Project, Tags 07A4, 0G7E and 06YY; the representative calculation
in steps 2--5 of the quotient pullback tensor coherence argument.
(blueprint: lem-sfb-quotient-pullback-tensor-flat-model).

The statement is restricted to flat-term K-flat complexes. The parent module
performs the separate resolution and naturality argument for arbitrary inputs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

attribute [local semireducible] AlgebraicGeometry.ProEtale.QuotientChange.L

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

open QuotientChange QuotientSectionTensor

/-- The quotient tensor square on two flat-term K-flat complexes.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 06YY;
steps 2--5 and the signed-total calculation of step 6 of
`lem-sfb-quotient-pullback-tensor-coherence`.
(blueprint: lem-sfb-quotient-pullback-tensor-flat-model).

Proof: compute each derived path separately using the normalized scalar tensor
and pullback counit equations. The left computation uses only b at X; the right
computation uses only b at Y. Both have the same source computation and target
localization inverse. The ordinary signed-total paths agree by monoidality of
the actual balancing isomorphism, prolonged to complexes. Geometric pullback
preserves K-flatness, so its counits and the scalar counits on the pulled-back
factors are invertible. Tensor normalization proves invertibility of the target
localization tensorator without assuming exactness of quotient extension.
Rewrite the ordinary square and cancel the common factor computation. The
parent supplies the resolution and naturality step for arbitrary derived
objects. -/
theorem quotient_pullback_tensor_flat_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (integral l E) T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (finite l E n) T)]
    (b : ∀ T : Scheme.{u}, TensorIso (reduction l E n) T)
    (_hb : ∀ T : Scheme.{u}, QuotientSectionTensor.TensorNormalized
      (reduction l E n) T (b T))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D (reduction l E n) Y ⋙ L (finite l E n) f ≅
      L (integral l E) f ⋙ D (reduction l E n) X)
    (_hlam : PullNormalized (reduction l E n) f lam)
    (P Q : CochainComplex (Modules (integral l E) Y) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (_hPflat : ∀ i : ℤ, ObjectProperty.flat (P.X i))
    (_hQflat : ∀ i : ℤ, ObjectProperty.flat (Q.X i)) :
    lam.hom.app ((Functor.uncurry.obj
      (CondensedRing.derivedTensor (integral l E) Y)).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (D (reduction l E n) X).map
          (((CondensedRing.leftDerivedUpperStarTensor (integral l E) f).app
            (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)) ≫
        (b X).hom.app ((L (integral l E) f).obj (DerivedCategory.Q.obj P),
          (L (integral l E) f).obj (DerivedCategory.Q.obj Q)) =
      (L (finite l E n) f).map
          ((b Y).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        ((CondensedRing.leftDerivedUpperStarTensor (finite l E n) f).app
          ((D (reduction l E n) Y).obj (DerivedCategory.Q.obj P))).app
            ((D (reduction l E n) Y).obj (DerivedCategory.Q.obj Q)) ≫
        (Functor.uncurry.obj (CondensedRing.derivedTensor (finite l E n) X)).map
          (Prod.mkHom (lam.hom.app (DerivedCategory.Q.obj P))
            (lam.hom.app (DerivedCategory.Q.obj Q))) := by
  have := QuotientTensorFlatModel.targetCompute_isIso (reduction l E n) f P Q _hP _hQ
  apply (cancel_mono (QuotientTensorFlatModel.targetCompute (reduction l E n) f P Q)).1
  have := QuotientTensorFlatModel.targetLocalization_isIso (reduction l E n) f
    (b X) (_hb X) P Q _hP _hQ _hPflat _hQflat
  have hleft := QuotientTensorFlatModel.left_flat_computation
    (reduction l E n) f lam _hlam (b X) (_hb X) P Q _hP _hQ _hPflat _hQflat
  have hright := QuotientTensorFlatModel.right_flat_computation
    (reduction l E n) f lam _hlam (b Y) (_hb Y) P Q _hP _hQ _hPflat _hQflat
  rw [QuotientTensorFlatModel.ordinary_square] at hleft
  simpa only [Category.assoc, CondensedRing.derivedTensor, Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, curriedTensor_obj_obj, curriedTensor_map_app,
    curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] using hleft.trans hright.symm

end AlgebraicGeometry.ProEtale.IntegralQuotient
