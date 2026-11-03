/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition

/-! # Binary tensor coherence of quotient scalar extension

Source: smooth-purity reduction compatibilities (3), scalar tensor balancing.
(blueprint: lem-pur-quotient-scalar-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The canonical scalar associator respects the binary tensor comparison.
This assertion concerns two arbitrary derived objects and contains no root-line
comparison, tensor-power induction, pullback, or purity map.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), tensor map; the scalar/tensor
balancing subargument of lem-pur-finite-smooth-ordinary-twist-cocycle.
(blueprint: lem-pur-quotient-scalar-tensor-composition).

Proof: choose flat-term K-flat resolutions P and Q of K and L. Ordinary scalar
extension preserves these properties, so all three scalar comparisons and their
successive composite are computed on these representatives. Transpose the ordinary
scalar associator through extension/restriction: its normalization is the identity
composition of restrictions. On homogeneous pure tensors the two displayed maps
send c tensor (b tensor (p tensor q)) to the same balanced tensor of the two scalar
images. Tensor balancing identifies the distributions of b and c between the two
factors. The signed total maps preserve each pair of degrees, so the signs agree
and this is an equality of chain maps. Sheafification and localization preserve it.
The defining representative normalizations of tensorIso and of the adjunction
associator identify this equality with the displayed square. Finally naturality
transports the equality along the resolution isomorphisms to K and L. This includes
identity quotients, zero coefficient rings, empty schemes and unbounded complexes;
no quotient is assumed flat. -/
theorem quotientScalarTensorComp
    (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (K L : DerivedCategoryModule (coefficient ell r) T) :
    (ordinaryScalar (FiniteReduction.quotient ell hnm) T).map
        ((ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hmr) T).hom.app
          (K, L)) ≫
      (ExceptionalCoefficients.tensorIso (FiniteReduction.quotient ell hnm) T).hom.app
        ((ordinaryScalar (FiniteReduction.quotient ell hmr) T).obj K,
          (ordinaryScalar (FiniteReduction.quotient ell hmr) T).obj L) ≫
      ((derivedTensor (ModuleCat.{u + 1} (coefficient ell n)) T).map
        ((ordinaryAssociator T ell hmr hnm).hom.app K)).app
          ((ordinaryScalar (FiniteReduction.quotient ell hnm) T).obj
            ((ordinaryScalar (FiniteReduction.quotient ell hmr) T).obj L)) ≫
      ((derivedTensor (ModuleCat.{u + 1} (coefficient ell n)) T).obj
        ((ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T).obj K)).map
          ((ordinaryAssociator T ell hmr hnm).hom.app L) =
    (ordinaryAssociator T ell hmr hnm).hom.app
        (((derivedTensor (ModuleCat.{u + 1} (coefficient ell r)) T).obj K).obj L) ≫
      (ExceptionalCoefficients.tensorIso
        (FiniteReduction.quotient ell (hnm.trans hmr)) T).hom.app (K, L) := by
  have hcomp : FiniteReduction.quotient ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) :=
    RingHom.ext (fun x ↦
      congrArg (fun y : ZMod (ell ^ n) ↦
        (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} ell n))
        (DFunLike.congr_fun
          (Subsingleton.elim
            (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
            ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
              (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))
  have h := ExceptionalCoefficients.scalarTensor_comp
    (FiniteReduction.quotient ell hmr) (FiniteReduction.quotient ell hnm)
    (FiniteReduction.quotient ell (hnm.trans hmr)) hcomp T K L
  simpa only [ordinaryScalar, ordinaryAssociator, ExceptionalCoefficients.quotientAssociator,
    Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj,
    coefficient, scalarExtension, Category.assoc] using h.symm

end AlgebraicGeometry.Etale.FiniteSmoothPurity
