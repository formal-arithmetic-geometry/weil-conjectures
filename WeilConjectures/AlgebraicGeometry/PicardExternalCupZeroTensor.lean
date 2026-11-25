/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorBijective
import WeilConjectures.AlgebraicGeometry.ExternalCupZeroGlobalSections

/-! # Degree-zero external tensor comparison

## References

* Stacks Project, Varieties, Tag 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections of the external tensor product are the tensor of global sections,
with the identification expressed on degree-zero scalar cohomology, sending a pure tensor
to the product of its projection pullbacks (Stacks, Tag 0BED). -/
theorem picardExternalCup_zero_tensor
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    : ∃ e : (scalarCohomology f F 0 ⊗[k] scalarCohomology g G 0) ≃ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) 0,
      ∀ (a : scalarCohomology f F 0) (b : scalarCohomology g G 0),
        e (a ⊗ₜ[k] b) = externalCup f g F G 0 0 a b := by
  let eF := scalarGlobalSectionsEquiv f F
  let eG := scalarGlobalSectionsEquiv g G
  let eP := scalarGlobalSectionsEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
  let eS := LinearEquiv.ofBijective (externalGlobalSectionsTensor f g F G)
    (externalGlobalSectionsTensor_bijective k X Y f g F G)
  refine ⟨((TensorProduct.congr eF eG).trans eS).trans eP.symm, ?_⟩
  intro a b
  apply eP.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul]
  exact (externalCup_zero_globalSections k X Y f g F G a b).symm

end AlgebraicGeometry.Scheme.Modules
