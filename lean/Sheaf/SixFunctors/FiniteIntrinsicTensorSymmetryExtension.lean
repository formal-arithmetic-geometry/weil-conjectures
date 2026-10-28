/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.SixFunctors.FiniteIntrinsicTensorRealization
public import Sheaf.Paper.FiniteScalarTensorResolution
public import Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetryResolving

/-! # Extension of finite intrinsic tensor symmetry from resolving representatives

This module records the localization and fully faithful extension step separately
from the representative calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- A natural tensor square which holds on flat-term K-flat representatives holds
on every pair in the derived category.

Source: the third proof step of `lem-sf-finite-intrinsic-tensor-symmetry`; Stacks
Project, Tags 04VK and 07A4. The proof uses the naturality assumptions and the
fully faithful restriction to resolving representatives.
(blueprint: lem-sf-finite-intrinsic-tensor-symmetry-extension).
-/
theorem finiteIntrinsicTensorSymmetry_extension
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
    (hres : ∀ (P Q : CochainComplex
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ℤ),
      ∀ (hP : finiteScalarFlatRepresentatives X B P)
        (hQ : finiteScalarFlatRepresentatives X B Q),
      (finiteIntrinsicTensorRealization X B a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (sfIntrinsicDerivedEquivalence X B).functor.map
          ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
      (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj P))
        ((sfIntrinsicDerivedEquivalence X B).functor.obj (DerivedCategory.Q.obj Q))).hom ≫
        (finiteIntrinsicTensorRealization X B a).hom.app
          (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P)) :
    ∀ K L,
      (finiteIntrinsicTensorRealization X B a).hom.app (K, L) ≫
          (sfIntrinsicDerivedEquivalence X B).functor.map ((b.inv.app L).app K) =
        (s.swap ((sfIntrinsicDerivedEquivalence X B).functor.obj K)
          ((sfIntrinsicDerivedEquivalence X B).functor.obj L)).hom ≫
            (finiteIntrinsicTensorRealization X B a).hom.app (L, K) := by
  sorry

end WeilConjectures.IntegralVerdier
