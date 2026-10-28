/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.SixFunctors.FiniteIntrinsicTensorRealization
public import Sheaf.Paper.FiniteScalarTensorResolution

/-! # Resolving representative part of finite intrinsic tensor symmetry

This is the flat-term K-flat representative calculation used by the intrinsic
symmetry theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- The signed tensor square commutes on the chosen flat-term K-flat representatives.

Source: the first two proof steps of
`lem-sf-finite-intrinsic-tensor-symmetry`; Stacks Project, Tags 00YV, 06YL and 0FPT.
The proof is the normalized pure-tensor calculation: finite scalar representative
normalization identifies the realization with the total tensor model, and the
representative equation of `s` and the `hb` normalization identify both swaps.
(blueprint: lem-sf-finite-intrinsic-tensor-symmetry-resolving).
-/
theorem finiteIntrinsicTensorSymmetry_resolving
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
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (.up ℤ)) K L).hom)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (sfIntrinsicDerivedEquivalence X B).functor.map
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
    (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj P))
      ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj Q))).hom ≫
      (finiteIntrinsicTensorRealization X B a).hom.app
        (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) := by
  sorry

end WeilConjectures.IntegralVerdier
