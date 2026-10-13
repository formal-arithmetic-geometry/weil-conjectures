/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Scalar extension of a finite-support product

Source: Stacks Project, more-algebra.tex, Lemma 0A6A (lemma-base-change-RHom).
(blueprint: lem-pc-ring-extension-finite-support-product)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Scalar extension of a limiting fan with only finitely many nonzero factors is
again a limiting fan, with projections normalized on pure tensors.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, finite-product computation;
algebra.tex, tensor products and finite direct sums.
(blueprint: lem-pc-ring-extension-finite-support-product).

Proof: evaluate at the unique object. On the bottom-topology one-object site,
sheafification is an isomorphism and evaluation identifies module sheaves with modules.
Delete the zero factors outside [a,b] from the limiting product: maps into those factors
are unique, so restriction to the interval and extension by zero are inverse universal
properties. The interval is finite, including when a>b. Tensor product with B commutes
with its finite product, by the finite-direct-sum formula TensorProduct.piRight.
Transport the resulting limiting fan back to module sheaves and along hF. The
projections are the scalar extensions of the original projections transported by hF;
the tensor-product formula and naturality of the sheafification unit give the displayed
formula. No claim about F.map is needed, and no flatness hypothesis is used. -/
theorem ringExtension_finiteSupport_product
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : ℤ → RingSiteModules A) (T : RingSiteModules A) (π : ∀ p, T ⟶ M p)
    (hπ : IsLimit (Fan.mk T π))
    (hb : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (M p)) :
    ∃ ρ : ∀ p, F.obj T ⟶ F.obj (M p),
      Nonempty (IsLimit (Fan.mk (F.obj T) ρ)) ∧
      ∀ (p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : T.val.obj U),
        (ρ p).val.app U (ringExtensionPure φ F hF T U b x) =
          ringExtensionPure φ F hF (M p) U b ((π p).val.app U x) := by
  sorry

end CategoryTheory
