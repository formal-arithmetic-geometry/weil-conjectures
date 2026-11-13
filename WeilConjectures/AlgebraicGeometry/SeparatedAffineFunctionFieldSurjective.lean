/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
import WeilConjectures.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCore
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization

/-!
# Separated affine and local charts surject onto the function field

## References

* [Stacks Project, Tag 09NB](https://stacks.math.columbia.edu/tag/09NB)
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- On a separated integral scheme, for a nonempty affine open `U` and a point `x ∉ U` whose
stalk is noetherian of dimension one, the canonical tensor-product map from the sections over
`U` and the stalk at `x` onto the function field is surjective. -/
theorem Scheme.separated_affine_functionField_surjective
    (X : Scheme.{u}) [IsIntegral X]
    [hsep : X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [hUn : Nonempty U]
    (x : X) (hx : x ∉ U)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    let A : Type u := Γ(X, U)
    let B : Type u := X.presheaf.stalk x
    let K : Type u := X.functionField
    let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
      Algebra.TensorProduct.lift
        (X.germToFunctionField U).hom.toIntAlgHom
        (algebraMap B K).toIntAlgHom
        (fun _ _ => Commute.all _ _)
    Function.Surjective φ := by
  dsimp only
  let f : TensorProduct ℤ (Γ(X, U)) (X.presheaf.stalk x) →ₐ[ℤ] X.functionField :=
    Algebra.TensorProduct.lift
      (X.germToFunctionField U).hom.toIntAlgHom
      (algebraMap (X.presheaf.stalk x) X.functionField).toIntAlgHom
      (fun _ _ => Commute.all _ _)
  change Function.Surjective f
  let hclosed := Scheme.isClosedImmersion_specMap_tensor_functionField X U hU x hx hdim
  exact @surjective_of_isClosedImmersion_SpecMap _ _ (CommRingCat.ofHom f.toRingHom) hclosed

end AlgebraicGeometry
