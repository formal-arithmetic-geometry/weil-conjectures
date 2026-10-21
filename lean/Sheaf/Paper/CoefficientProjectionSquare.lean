/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Paper.ModuleObjectProjectionMap
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.RingedComparisonTensorAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Coefficient compatibility of the actual projection mate

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (3), projection on integral-model pairs before invertibility
(blueprint: lem-sfb-coefficient-projection-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the internal-Hom construction and the inverse image from the point opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxHeartbeats 200000 in
-- Share the geometric and scalar derived tensor instances.
/-- The specified scalar push mate and pull comparison commute with the actual projection
morphism, on ordinary unbounded derived module-object categories.
Source: blueprint main-20261015, proper-base-change-rational.proof.md (3)
(blueprint: lem-sfb-coefficient-projection-square).

Proof:
1. Transport the module tensors and geometric derived adjunctions to section-ring modules
using lem-pd-module-ringed-topos-derived-comparison. Transport scalar extension, restriction
and their units and counits using lem-sfb-internal-section-scalar-adjunction. Exact extension
makes restriction preserve K-injectives (lem-sfb-comap-preserves-k-injectives). The coefficient
square commutes. The K-injective normalization of derived pushforward composition identifies
its direct-image comparison with the inverse of derivedComapLowerStarIso. The conjugate
pullback comparison in lem-sfb-ringed-comparison-tensor-adjunction is therefore c inverse.
2. The tensor equation of that ringed comparison lemma identifies the composite tensorators
for T_X P_R and P_S T_Y. On flat-term K-flat representatives the scalar tensorator sends
s tensor (x tensor y) to (s tensor x) tensor (1 tensor y), so it is precisely mu here.
3. Expand derivedPushHom as the scalar-unit, inverse restriction comparison, scalar-counit
composite. Conjugacy of derivedPullIso and the composite adjunction counits, naturality,
and the scalar triangle identity give epsilon_S P_S(gamma_K) = T_X(epsilon_R) c_inverse.
4. Transpose the left composite under P_S adjoint to G_S. The definition of the projection
mate and naturality of the pullback tensor map give counit tensor identity after the
comparison. Insert step 3, then the tensor equation of step 2; naturality of mu rewrites it
as q T_X((epsilon_R tensor identity) d_R) c_inverse, with q = (identity tensor c_M) mu_X.
5. Transpose the right composite. Naturality of the counit and step 3 give
q T_X(epsilon_R) c_inverse P_S T_Y(pi_R). Naturality of c_inverse and the defining
transpose of pi_R rewrite this to the same expression as step 4. Injectivity of the
adjunction Hom bijection proves equality, without cancelling any projection or push map. -/
theorem coefficientProjectionSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj R X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj R Y.left))) :
    ((internalScalarTensorComparison a Y.left).app
        ((moduleObjectDerivedPushforward R f.left).obj K)).app M ≫
      ((derivedTensor S Y.left).map ((derivedPushHom a f.left).app K)).app
        ((internalScalarExtension a Y.left).obj M) ≫
      moduleObjectProjectionMap S f.left
        ((internalScalarExtension a X.left).obj K)
        ((internalScalarExtension a Y.left).obj M) =
    (internalScalarExtension a Y.left).map
        (moduleObjectProjectionMap R f.left K M) ≫
      (derivedPushHom a f.left).app
        (((derivedTensor R X.left).obj K).obj
          ((moduleObjectDerivedPullback R f.left).obj M)) ≫
      (moduleObjectDerivedPushforward S f.left).map
        (((internalScalarTensorComparison a X.left).app K).app
            ((moduleObjectDerivedPullback R f.left).obj M) ≫
          ((derivedTensor S X.left).obj
            ((internalScalarExtension a X.left).obj K)).map
              ((derivedPullIso a f.left).hom.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
