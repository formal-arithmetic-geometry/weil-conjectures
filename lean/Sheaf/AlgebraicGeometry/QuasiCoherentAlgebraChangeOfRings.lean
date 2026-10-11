/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Change of rings between quasi-coherent algebras

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Schemes, Lemma 01I8 (1)
and Section 01LA (blueprint: lem-weil-pbc-quasi-coherent-algebra-change-of-rings).

The quasi-coherent `𝒪_Y`-algebras are the shared form `B C : Y.CommAlgebraSheaf`
(`= Under Y.sheaf`, def-weil-pbc-comm-algebra-sheaf) with `B.toModule.IsQuasicoherent`;
`φ : B ⟶ C` in `Under Y.sheaf` is a morphism of `𝒪_Y`-algebras, so `C.hom = B.hom ≫ φ.right`.
`B`-modules are `SheafOfModules` over `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj B.right`
and their underlying `𝒪_Y`-modules are obtained by scalar restriction along `B.hom`. Change of
rings uses the recorded sheafification construction, whose section tensor products
have the scalar factor first (`C(W) ⊗[B(W)] P(W)`). This is the usual tensor product
`P(W) ⊗[B(W)] C(W)` under the canonical symmetry, with the same sheafification map.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- Change of rings between quasi-coherent algebras preserves quasi-coherence of the
underlying structure-sheaf module, and the sheafification map is bijective on affine opens.
Source: Stacks Project, Morphisms, proof of Lemma 01SB; Schemes, Lemma 01I8 (1), Section 01LA
(blueprint: lem-weil-pbc-quasi-coherent-algebra-change-of-rings).

Proof:
1. The underlying `O_Y`-module of the change of rings is the `O_Y`-module sheafification
   of the section tensor product, by uniqueness of the extended action and the universal
   property of `def-weil-presheaf-modules-sheafification` (Sheaves, Tag 0089).
2. Set `S = P ⊗[O_Y] C`. It is quasi-coherent and its affine sections are the section
   tensor products by `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
   The two `B`-actions, on `P` and on `C` through `φ`, extend uniquely to `S` by
   `def-weil-presheaf-modules-sheafification`, with a linear sheafification map.
3. Form `F = B ⊗[O_Y] S`, also quasi-coherent with the affine section formula by the
   same tensor-product lemma. The two actions induce `a₁, a₂ : F → S`; set `δ = a₁ - a₂`.
4. Its cokernel `T'` is quasi-coherent; on affine opens the quotient map is surjective
   with kernel the image of `δ`, by `lem-weil-pbc-quasi-coherent-module-cokernel-image`.
5. Algebraically, `P(W) ⊗[B(W)] C(W)` is the quotient of `P(W) ⊗[O_Y(W)] C(W)`
   by the relations `bp ⊗ c - p ⊗ φ(b)c`. This follows from the balanced universal
   property: the quotient and the tensor product map inversely on pure tensors.
   The affine formulas of steps 2 and 3 identify this relation submodule with the
   image of `δ`. Step 4 gives a bijection from the section tensor product to `T'(W)`.
6. The quotient maps induce inverse maps between the change of rings and `T'`:
   factor first through the balanced tensor product and then through sheafification;
   in the opposite direction both `B`-actions agree after changing rings, so the map
   from `S` kills `δ` and factors through its cokernel. The composites are identities
   by the sheafification universal property and the epimorphic cokernel map.
7. Transfer quasi-coherence across this isomorphism (`pqf-def-coherent`). On affine
   opens its composite with the sheafification map is the bijection of step 5;
   consequently the original sheafification map is bijective as well. -/
theorem quasiCoherent_algebra_changeOfRings (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (hB : B.toModule.IsQuasicoherent) (hC : C.toModule.IsQuasicoherent)
    (hP : ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P).IsQuasicoherent) :
    ((SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)).IsQuasicoherent ∧
    ∀ (W : Y.Opens), IsAffineOpen W →
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
