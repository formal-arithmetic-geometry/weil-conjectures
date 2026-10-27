/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModuleData

/-! # LeftTranslationCoaction

Source: Kaneda, On the Frobenius morphism of flag schemes (1994), Section 2.3,
printed pp.320--321; Milne, Algebraic Groups (2017), Sections 4a and 5f.
(blueprint: def-sfb-regular-function-left-translation-coaction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct
namespace AlgebraicGeometry.FrobeniusBorelInduction

/-- The canonical left-translation coaction on a specified actual function subspace.
The evaluation identity uniquely characterizes the canonical coaction by
(s f)(g) = f(s inverse g) on every algebra, including nilpotents. The identity
and multiplication of L imply its counit and coassociativity identities. Thus
this is a characterization of the actual rational action, not an abstract action.
No finite-dimensionality or choice of a representation is assumed.
Source: Kaneda, Section 2.3, pp.320--321, and Milne, Sections 4a--4b.
(blueprint: def-sfb-regular-function-left-translation-coaction) -/
def IsLeftTranslationCoaction {F : Type u} [Field F]
    {G L : Grp (Over (Spec (.of F)))} [IsAffine L.X.left] (i : L ⟶ G)
    (W : Submodule F (RhoSection.Coordinate G.X))
    (c : W →ₗ[F] W ⊗[F] RhoSection.Coordinate L.X) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ L.X)
    (g : StandardGroupSchemes.affine F A ⟶ G.X) (f : W),
    (Algebra.TensorProduct.lift (R := F) (S := F)
      (RhoSection.evaluate g) (RhoSection.evaluate s) (fun _ _ ↦ Commute.all _ _))
        ((W.subtype.rTensor (RhoSection.Coordinate L.X)) (c f)) =
          RhoSection.evaluate ((s ≫ i.hom.hom)⁻¹ * g) f.val

end AlgebraicGeometry.FrobeniusBorelInduction
