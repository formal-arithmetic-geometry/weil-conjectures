/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.SixFunctors.IntegralVerdierModels

/-! # Normalized bidual comparison for constant-ring realization

Source: Stacks Project, Tags 00YV, 06YL, 08J9 and 08JA; the coefficient-realization
step of finite intrinsic Verdier biduality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- The canonical constant-ring realization identifies the normalized evaluation
transposes, up to the two closed-Hom comparisons and the input isomorphism.
This is a statement about arbitrary objects and finite commutative rings; it has no
constructibility, Tor, finite-field, exceptional-functor, or biduality assumption.

Source: the realization step of lem-sf-finite-intrinsic-verdier-biduality;
Stacks Project, Tags 00YV, 06YL, 08J9 and 08JA
(blueprint: lem-sf-finite-intrinsic-bidual-comparison).

Proof: extend fixed scalar actions along the locally bijective constant-scalar unit.
On module sheaves the resulting exact equivalence preserves the tensor product:
the tensorator sends the pair of scalar-unit images of x and y to the scalar-unit
image of x tensor y. Its inverse is fixed by the same generators. Apply this
comparison termwise on K-flat resolutions and totalize. The Koszul swap commutes
with it on each homogeneous pair, including the sign (-1)^(ij). Local generation
and the localization universal property extend these equations to derived objects.
The tensor-Hom adjunction and full faithfulness of the equivalence then give the
closed comparison F RHom(K,W) isomorphic to RHom(F K,F W). Postcompose in the
second input with w, and precompose in the first input with i inverse, to obtain
the dual comparison at K. Apply the closed comparison once more at RHom(K,W).
Compose it with the inverse of the Hom map induced contravariantly by the first
dual comparison. This gives c. To check the displayed equation, untranspose it.
The source pairing is uniquely normalized by the descended Koszul symmetry and
the tensor-Hom identity. The fields a.evaluation and s.representative give the
same signed Hom-complex evaluation after realization. Thus the two untransposed
maps agree on K-flat tests and K-injective targets, and hence in the derived
category. Naturality in the first tensor input, expressed by he, and symmetry
naturality hs give the final conjugation by i. Transposition is injective.
Zero rings, zero objects and empty sites satisfy the same generator equations;
no nonzero or perfectness condition is used. -/
theorem finiteIntrinsicBidualComparison
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (hs : ∀ (K L K' L' : proEtaleDerivedCategory X B)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : proEtaleDerivedCategory X B) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (W K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (h : ProEtale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X W)
    (ω M : proEtaleDerivedCategory X B)
    (w : (sfIntrinsicDerivedEquivalence X B).functor.obj W ≅ ω)
    (i : (sfIntrinsicDerivedEquivalence X B).functor.obj K ≅ M) :
    ∃ c : (sfIntrinsicDerivedEquivalence X B).functor.obj
        ((dualityDoubleFunctor MonoidalClosed.internalHom W).obj K) ≅
          (IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).obj
            (op ((IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).obj (op M, ω)), ω),
      i.hom ≫ delta X a s ω M =
        (sfIntrinsicDerivedEquivalence X B).functor.map
          (ProEtale.AmbientDualityPairing.bidualityMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X h K) ≫ c.hom := by
  sorry

end WeilConjectures.IntegralVerdier
