/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsPushforwardTensorComparison

/-! # Affine-basis comparison for the presheaf coproduct

## References

* Stacks Project, Varieties, Tag 0BED.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- On the affine basis, the presheaf coproduct indexed by a basis of sections of F
is naturally isomorphic to the underlying presheaf of the external direct image.
(Stacks, Tag 0BED) -/
theorem exists_external_coproduct_comparison
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (I : Type w) (_b : Module.Basis I k (scalarObj f F (op ⊤))) :
    Nonempty ((PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
        Y.ringCatSheaf.obj).obj (∐ fun _ : I ↦ G.val) ≅
      (PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
        Y.ringCatSheaf.obj).obj
        ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
          (externalCupCoefficients f g F G)).val) := by
  obtain ⟨eb⟩ := exists_picard_constant_sections_tensor_basis
    k Y g (scalarObj f F (op ⊤)) G I _b
  obtain ⟨et⟩ := exists_external_constant_sections_tensor_comparison k X Y f g F G
  exact ⟨(PresheafOfModules.pushforward₀
    (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
    Y.ringCatSheaf.obj).mapIso eb ≪≫ et⟩

end AlgebraicGeometry.Scheme.Modules
