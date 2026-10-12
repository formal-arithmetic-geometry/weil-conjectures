/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction

import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # Local computations for the perfect internal dual -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Tensor evaluation is invertible for a perfect first argument.
Source: Stacks Project, Cohomology, Tags 08DQ and 08DM.
Proof: refine the perfect neighbourhoods to affine opens and represent K by a
bounded complex E of direct summands of finite free sheaves. Restriction of RHom
commutes with these opens, and the strictly-perfect Hom lemma computes RHom by
ordinary Hom complexes. The dual of E is again bounded and termwise finite projective,
hence K-flat. For an arbitrary complex F, the evaluation comparison is the total
of F^p tensor Hom(E^q,O) to Hom(E^q,F^p). It is an isomorphism for finite free
E^q and for its direct summands. These identifications respect differentials and the canonical
adjunction. For any natural adjunction bijection in the statement, Yoneda changes
its adjuncts by invertible natural transformations, so invertibility is unchanged.
Finally test the globally defined maps on cohomology sheaves on the open cover;
no morphisms are glued. This works for unbounded F and does not assume F is quasi-coherent.
(blueprint: lem-pc-perfect-rhom-evaluation-isomorphisms) -/
theorem perfect_rhom_evaluation_isomorphisms
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (D : schemeDerivedCategory X)
    (hD : D =
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X))) :
    (∀ N : schemeDerivedCategory X,
      IsIso ((adj (N ⊗ D) K.obj N).symm
        ((α_ N D K.obj).hom ≫ N ◁
          (adj D K.obj (𝟙_ (schemeDerivedCategory X)) (eqToHom hD)) ≫ (ρ_ N).hom))) := by
  sorry

end AlgebraicGeometry
