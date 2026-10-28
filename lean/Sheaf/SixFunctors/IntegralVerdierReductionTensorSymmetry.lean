/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.SixFunctors.IntegralVerdierModels

/-! # Signed symmetry of the normalized integral reduction tensor comparison

Source: Stacks 06YL, 06YU and 07A4; the signed-swap calculation in the second
paragraph of the proof of `thm-coef-integral-verdier`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

/-- The normalized coefficient tensor comparison preserves signed interchange.
This concerns tensor and scalar reduction alone, with no dualizing object, internal
Hom comparison, evaluation, or double-dual morphism.

Source: Stacks 06YL, 06YU and 07A4; the tensor interchange calculation in
`thm-coef-integral-verdier`, second proof paragraph.
(blueprint: lem-sf-integral-verdier-reduction-tensor-symmetry).

Proof: resolve the two inputs by K-flat complexes with flat terms. The reduction
counits on these representatives are isomorphisms. Use the representative equations
of the source and finite signed symmetries and the normalization of the reduction
presentation. On the summand of bidegree (i,j), both paths send the scalar-unit
pure tensor x tensor y to (-1)^(ij) times the scalar-unit tensor y tensor x.
The scalar extension units generate their extended modules, the sheafified tensor
is generated locally by pure tensors, and the total tensor is the direct sum of
these summands. Consequently the chain maps agree. The representative comparison
squares identify their derived images with the desired two composites. Finally
naturality of both signed symmetries and of mu transports the equality along the
representing isomorphisms to every pair of derived objects. The formula also holds
for zero objects and empty schemes, since the same generator calculation applies. -/
theorem reduction_tensor_symmetry
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (n : ℕ) (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (t : SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) m.target)
    (ht : ∀ (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      m.target.tensor.map (Prod.mkHom f g) ≫ (t.swap K' L').hom =
        (t.swap K L).hom ≫ m.target.tensor.map (Prod.mkHom g f))
    (K L : Ambient l E X) :
    m.mu.inv.app (K, L) ≫
        (scalarReductionDerivedExtension l E X n).map (s.swap K L).hom =
      (t.swap ((scalarReductionDerivedExtension l E X n).obj K)
        ((scalarReductionDerivedExtension l E X n).obj L)).hom ≫ m.mu.inv.app (L, K) := by
  sorry

end WeilConjectures.IntegralVerdier
