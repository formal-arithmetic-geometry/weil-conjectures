/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorSymmetryExtension

/-! # Signed tensor realization for finite constant coefficients

Source: Stacks Project, Tags 00YV, 06YL and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- The constructed constant-coefficient tensor comparison intertwines the
specified signed interchanges. This assertion involves neither internal Hom nor
evaluation nor double duals; its tensor comparison is already constructed.

Source: steps 1 and 2 of lem-sf-finite-intrinsic-bidual-comparison; Stacks Project,
Tags 00YV, 06YL and 0FPT
(blueprint: lem-sf-finite-intrinsic-tensor-symmetry).

Proof: restrict a.representative to the flat-term K-flat class using
finiteIntrinsicTensorModel. The comparison finiteScalarTensorRealization has its
specified representative normalization: conjugating by the exact realization's
localization factors identifies it with finiteScalarTotalTensorIso. On ordinary
module sheaves this comparison sends scalar-unit pure tensors to the same pure
tensors. On the (p,q) summand of total complexes, both swaps reverse the two
sections with the scalar (-1)^(pq). Thus the square commutes on homogeneous pure
tensors. Sheafification's adjunction and local generation give the chain-map
identity. The representative equation of s identifies the intrinsic swap with
the image of this chain swap. The normalization hb identifies the inverse of b
with the same signed fixed-scalar swap, since this swap is involutive. The
normalization of finiteScalarTensorRealization consequently proves the square
on flat-term K-flat representatives. Its naturality, hs and the naturality of b
make both sides natural transformations on derived pairs. The fully faithful
restriction to resolving representatives (finiteScalarRepresentativesFullyFaithful)
then gives the equation on all pairs. Empty sites, zero rings and zero objects
satisfy the same generator equations; no perfectness condition is used. -/
theorem finiteIntrinsicTensorSymmetry
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (hs : ∀ (K L K' L' : proEtaleDerivedCategory X B)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (b : CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) ≅
      (CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (.up ℤ)) K L).hom) :
    ∀ K L,
      (finiteIntrinsicTensorRealization X B a).hom.app (K, L) ≫
          (sfIntrinsicDerivedEquivalence X B).functor.map ((b.inv.app L).app K) =
        (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj K)
          ((sfIntrinsicDerivedEquivalence X B).functor.obj L)).hom ≫
            (finiteIntrinsicTensorRealization X B a).hom.app (L, K) := by
  apply finiteIntrinsicTensorSymmetry_extension X B a s hs b hb
  intro P Q hP hQ
  exact finiteIntrinsicTensorSymmetry_resolving X B a s hs b hb P Q hP hQ

end WeilConjectures.IntegralVerdier
