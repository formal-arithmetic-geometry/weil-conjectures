/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewiseEquation

/-!
# Inverse to degreewise currying

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-degreewise-iso)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- There is one reverse map inverse to every forward map with the currying equation.
Source: Stacks Project, Tag 0A90, inverse construction 
(blueprint: lem-sc-hom-tensor-degreewise-iso).

Proof: Restrict a localized map from each total-degree coproduct to its summands.
Apply the localized tensor-Hom adjunction to curry the K and L inputs successively.
Combine the q components by the inner Hom product universal property and then the
p components by the outer Hom product universal property. Restriction naturality
of currying gives a sheaf morphism in the reverse direction. To check the first
composite, project to p and q and evaluate at x and y; the assumed equation and
the tensor-Hom inverse laws give the identity. For the second composite, project
to total degree, restrict to a summand, and check on pure tensors before
sheafification; the same inverse laws give the identity. Product and coproduct
extensionality, and the sheafification adjunction, establish the two identities,
so the original morphism is an isomorphism. The reverse map is constructed
independently of a forward map;
the inverse calculations apply to every map satisfying the evaluation equation. -/
theorem homTensorDegreewise_inverse (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ a, HomTensorDegreewiseEquation R K L M n a → a ≫ b = 𝟙 _ ∧ b ≫ a = 𝟙 _ := by sorry

end CategoryTheory
