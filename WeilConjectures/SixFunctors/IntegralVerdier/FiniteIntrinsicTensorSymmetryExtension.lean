/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorSymmetryResolving

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

-- Preserve the published binders, including the unused normalization and resolution proofs.
set_option linter.unusedVariables false in
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
  let D := DerivedCategory (Sheaf (ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
  let F := (sfIntrinsicDerivedEquivalence X B).functor
  let T := CategoryTheory.MonoidalCategory.curriedTensor D
  let r := finiteIntrinsicTensorRealization X B a
  let swap := CategoryTheory.Prod.swap D D
  let σ : F.prod F ⋙ a.tensor ⟶ swap ⋙ F.prod F ⋙ a.tensor :=
    { app := fun Z ↦ (s.swap (F.obj Z.1) (F.obj Z.2)).hom
      naturality := by
        intro Z W f
        exact hs _ _ _ _ (F.map f.1) (F.map f.2) }
  let τ : Functor.uncurry.obj T ⟶ swap ⋙ Functor.uncurry.obj T :=
    Functor.uncurry.map ((flipFunctor D D D).map b.inv) ≫
      (Functor.uncurryObjFlip T).hom
  have hτ (K L : D) : τ.app (K, L) = (b.inv.app L).app K := by
    change (b.inv.app L).app K ≫ 𝟙 _ = _
    exact Category.comp_id _
  let α := r.hom ≫ Functor.whiskerRight τ F
  let β := σ ≫ Functor.whiskerLeft swap r.hom
  let P := finiteScalarFlatRepresentatives X B
  let W := (Functor.whiskeringLeft
    (P.FullSubcategory × P.FullSubcategory) (D × D)
    (proEtaleDerivedCategory X B)).obj
      (((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)))
  obtain ⟨ff⟩ := finiteScalarRepresentativesFullyFaithful X B
  have hW : W.map α = W.map β := by
    ext Z
    change r.hom.app (DerivedCategory.Q.obj Z.1.obj, DerivedCategory.Q.obj Z.2.obj) ≫
      F.map (τ.app (DerivedCategory.Q.obj Z.1.obj, DerivedCategory.Q.obj Z.2.obj)) =
      (s.swap (F.obj (DerivedCategory.Q.obj Z.1.obj))
        (F.obj (DerivedCategory.Q.obj Z.2.obj))).hom ≫
          r.hom.app (DerivedCategory.Q.obj Z.2.obj, DerivedCategory.Q.obj Z.1.obj)
    rw [hτ]
    exact hres Z.1.obj Z.2.obj Z.1.property Z.2.property
  have h : α = β := ff.map_injective hW
  intro K L
  have hKL := congr_app h (K, L)
  change r.hom.app (K, L) ≫ F.map (τ.app (K, L)) =
    (s.swap (F.obj K) (F.obj L)).hom ≫ r.hom.app (L, K) at hKL
  rw [hτ] at hKL
  exact hKL

end WeilConjectures.IntegralVerdier
