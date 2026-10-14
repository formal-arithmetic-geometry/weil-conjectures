/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Algebra.Homology.LocalizationModelSemilinear
public import Sheaf.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
import Sheaf.Algebra.Homology.DerivedTensorActionNaturality
import Sheaf.Algebra.Homology.KFlatScalarExtensionCounit

/-! # Universal derived cohomology comparisons for a fixed balanced tensor complex

Source: Stacks Project, Tags 064L and 06Y6. The K-flat resolution is supplied explicitly.
(blueprint: new-lem-pc-balanced-tensor-unit-model-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology
variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

variable (B D : Type u) [CommRing B] [CommRing D] [Algebra R B]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Universal model comparisons and naturality for a specified K-flat second factor.
Source: Stacks Project, Tags 064L and 06Y6; the balanced computation and
naturality explained by lem-pc-balanced-derived-tensor-model and
lem-pc-derived-tensor-action-naturality.
(blueprint: new-lem-pc-balanced-tensor-unit-model-comparison).

Proof: use the quasi-isomorphism f : F -> B[0] to compute Q tensor_R^L B by
Tot(Q tensor_R F). To compare this computation with L.derived, resolve the
underlying R-complex of Q by P -> Q. K-flatness of F makes
Tot(P tensor_R F) -> Tot(Q tensor_R F) a quasi-isomorphism; K-flatness of P makes
Tot(P tensor_R F) -> Tot(P tensor_R B[0]) a quasi-isomorphism. The last complex
is the ordinary extension of P to B. The universal counit at P is invertible by
ModuleCat.scalarExtensionCounit_isIso_of_kFlat (P is K-flat over R). Counit
naturality for P -> Q then identifies its image
with L.derived(Q), giving the cohomology comparison. Do the same with
Aq tensor_A Q and K, using the same F. Multiplication by a on Q acts on all
these maps; naturality and L.cohomologyIso_smul make the first comparison
A-linear. The analogous argument using K.cohomologyIso_smul makes the second
comparison A-linear after restriction from Aq. The displayed pure-tensor formula
for θ identifies unit followed by θ with tensoring uQ by F. Naturality of the
resolution comparisons and uniqueness of the universal derived-counit comparison
therefore identify its cohomology map with localizationModelMap, giving the square.
There is no assertion about an arbitrary complex with the same cohomology as Q tensor_R F:
the two complexes in this statement are the specified mixed total tensors. -/
theorem exists_balancedTensorUnitModelComparison (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      (ModuleCat.of R B))
    (hf : QuasiIso f)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    (θ : (extend A Aq).obj
        (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ≅
      ((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj ((extend A Aq).obj Q)).obj F)
    (hθ :
    ∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
      θ.hom.f n ((1 : Aq) ⊗ₜ[A,algebraMap A Aq]
        ((HomologicalComplex.ιMapBifunctor Q F
          (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
            (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))) =
      (HomologicalComplex.ιMapBifunctor ((extend A Aq).obj Q) F
        (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
          (((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) ⊗ₜ[Aq]
            ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) :
    let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
    let Cq := ((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj
      ((extend A Aq).obj Q)).obj F
    ∃ (e : (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeft (S := R) : A →ₐ[R] A ⊗[R] B).toRingHom).obj
          (L.cohomology i) ≅ C.homology i)
      (eq : (ModuleCat.restrictScalars
        ((Algebra.TensorProduct.includeLeft (S := R) : Aq →ₐ[R] Aq ⊗[R] B).toRingHom.comp
          (algebraMap A Aq))).obj (K.cohomology i) ≅ ((restrict A Aq).obj Cq).homology i),
      ∀ x : L.cohomology i,
        eq.hom (localizationModelMap R A Aq B D i Q L K uQ x) =
          (HomologicalComplex.homologyMap
            ((((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
              (.up ℤ)).unit.app C) ≫ (restrict A Aq).map θ.hom) i) (e.hom x) := by sorry

end RingTensorCohomology
