/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Images

/-! # Comparing extended ideal tensor products with categorical images

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality;
Modules Tag 01CD. The general image identification below is the representation step.
(blueprint: lem-sc-ideal-tensor-image-comparison).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The image of an adjoint ideal inclusion, multiplied by an invertible module, agrees
with the extended ideal tensor product, compatibly with any linear comparison of the
ambient modules and any change of pullback adjunction.

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality;
Modules Tag 01CD, pullback of tensor products.
(blueprint: lem-sc-ideal-tensor-image-comparison).

Proof: write a₀ for the canonical adjunction and c for its comparison with adj.
For the canonical adjoint ideal map φ₀, on affine opens U = Spec B contained in the
preimage of V = Spec A the pullback sections are B ⊗[A] I(V), since I is quasi-coherent.
The adjunction equation sends b ⊗ a to b f♯(a). Its image is precisely I(V)B, the ideal
of I.comap f on U (ideal_comap_appLE). Changing the adjunction gives
φ = c_I.hom ≫ φ₀, hence the same image because c_I is an isomorphism. These affine
calculations commute with restriction and identify image φ with (I.comap f).toModules
compatibly with their inclusions into the unit module. No flatness is needed: this
computes an image, without asserting that B ⊗[A] I(V) maps injectively to B.
Write K = I.comap f. Tensoring either ideal inclusion with an invertible module is
monic (mono_whiskerRight). In particular multiplication μP is monic, so its source
maps isomorphically onto image μP. The module N₁ is invertible via e. Under the ideal
image identification, tensor the identity of K.toModules with the linear isomorphism
h = e.inv ≫ (c.app N).hom. Naturality of the left unitor shows that this tensor map
commutes with multiplication into P and N₁, with ambient map h. Compose it with the
inverse of the monic image corestriction to μP. This is an isomorphism of sheaves;
evaluation on the top open gives q and the displayed equality. Monicity of μ₁ also
shows that this equality uniquely determines q. -/
theorem ideal_tensor_image_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (N : Y.Modules) (P : X.Modules) [P.IsInvertible]
    (adj : tensorPullback f ⊣ pushforward f)
    (e : (tensorPullback f).obj N ≅ P) :
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    let μP := image.ι φ ▷ P ≫ (λ_ P).hom
    let N₁ := (tensorPullback f).obj N
    let μ₁ := (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
    ∃ q : Γ(image μP, ⊤) ≃+ Γ((I.comap f).toModules ⊗ N₁, ⊤),
      ∀ t, μ₁.app ⊤ (q t) =
        (c.app N).hom.app ⊤ (e.inv.app ⊤ ((image.ι μP).app ⊤ t)) := by sorry

end AlgebraicGeometry.Scheme.Modules
