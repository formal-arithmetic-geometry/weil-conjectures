/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.SingleFunctorLaxMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.SingleDualPairing.SingleDualPairing

/-!
# Finite projective tensor--Hom in the condensed Poincare setting

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
lem-pod-finite-projective-tensor-hom.md and its proof; Stacks Project, Tags 08JH and 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom).

The ordinary dual is the existing internal Hom into the module unit. The canonical
map is specified in the statement by degree-zero evaluation and tensor--Hom transposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The transpose of an exact evaluation tensored with an object is invertible.
This is the closed-category factorization through the internal dual. -/
private theorem isIso_curry_condensedPairing_tensor {C : Type*} [Category* C]
    [MonoidalCategory C] [MonoidalClosed C] (X D N : C) [ExactPairing D X] :
    IsIso (curry ((α_ X D N).inv ≫ ε_ D X ▷ N ≫ (λ_ N).hom)) := by
  have heq : curry ((α_ X D N).inv ≫ ε_ D X ▷ N ≫ (λ_ N).hom) =
      curry (ε_ D X) ▷ N ≫ ihomUnitTensorToIhom X N := by
    rw [ihomUnitTensorToIhom, ← curry_natural_left]
    congr 1
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      whiskerLeft_curry_ihom_ev_app]
  rw [heq]
  have := isIso_ihomUnitTensorToIhom D X N
  infer_instance

set_option maxHeartbeats 1000000 in
-- Specializing closed tensor identities unfolds large condensed-module instances.
/-- The ordinary dual of a finite locally projective coefficient module, tensored
with a bounded constructible finite-Tor complex, computes derived internal Hom.
The canonical comparison is natural contravariantly in the module and covariantly
in the complex; ordinary evaluation into the double dual is invertible as well.

Source: current blueprint lem-pod-finite-projective-tensor-hom and its proof;
Stacks Project, Tags 08JH and 08JJ (blueprint: lem-pod-finite-projective-tensor-hom).

Proof:
1. The conventions give the actual pulled-back condensed ring on the small pro-etale
site. The existing finite-locally-projective dualizability theorem proves duality
for finite powers of the unit, then their retracts, and detects the invertibility
of the canonical evaluation on the covering sieves. This includes rank zero.
2. The ordinary internal dual of P therefore has an exact pairing with P whose
evaluation is the ordinary internal-Hom counit. Ordinary biduality is invertible.
Both objects of the pairing are flat, so their degree-zero complexes are K-flat.
3. The existing degree-zero exact-pairing theorem maps this pairing through the
strong monoidal localization on flat objects. Its derived evaluation is exactly
the tensor comparison followed by ordinary evaluation and the unit comparison,
as specified below. The displayed transpose factors as the invertible transpose
of this evaluation tensored with N, followed by the invertible internal-dual
tensor-Hom comparison. Hence it is an isomorphism for every N in the ambient
category, in particular for every bounded constructible finite-Tor N.
4. Naturality of ordinary evaluation and of the prescribed lax tensorator gives
the evaluation square in P. Currying it gives contravariant P-naturality. Curry
naturality on the target, associator naturality and whisker exchange give the
covariant N-naturality square. -/
theorem condensedPoincareFiniteProjectiveTensorHom
    (S : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :
    let Λ := (S.presentation c).obj S.ell
    let M := supportModules Λ S.X
    let F := DerivedCategory.singleFunctor M 0
    let dual : M → M := fun P ↦ (ihom P).obj (𝟙_ M)
    let evaluation : ∀ P : M, F.obj P ⊗ F.obj (dual P) ⟶ 𝟙_ (DerivedCategory M) :=
      fun P ↦ DerivedCategory.singleFunctorTensorComparison P (dual P) ≫
        F.map ((ihom.ev P).app (𝟙_ M)) ≫ (DerivedCategory.singleFunctorObjUnitIso M).hom
    let comparison : ∀ (P : M) (N : DerivedCategory M),
        ((derivedTensor Λ S.X).obj (F.obj (dual P))).obj N ⟶
          ((derivedHom Λ S.X).obj (op (F.obj P))).obj N :=
      fun P N ↦ curry ((α_ (F.obj P) (F.obj (dual P)) N).inv ≫
        evaluation P ▷ N ≫ (λ_ N).hom)
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P →
      ∀ N : S.ctf c S.X, IsIso (comparison P N.obj)) ∧
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P → IsIso (toIhomIhomUnit P)) ∧
    (∀ (P P' : M), IsFiniteLocallyProjective Λ S.X P →
      IsFiniteLocallyProjective Λ S.X P' → ∀ (f : P ⟶ P') (N : S.ctf c S.X),
        F.map ((pre f).app (𝟙_ M)) ▷ N.obj ≫ comparison P N.obj =
          comparison P' N.obj ≫ (pre (F.map f)).app N.obj) ∧
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P →
      ∀ (N N' : S.ctf c S.X) (g : N ⟶ N'),
        F.obj (dual P) ◁ g.hom ≫ comparison P N'.obj =
          comparison P N.obj ≫ (ihom (F.obj P)).map g.hom) := by
  let Λ := (S.presentation c).obj S.ell
  let M := supportModules Λ S.X
  let F := DerivedCategory.singleFunctor M 0
  let dual : M → M := fun P ↦ (ihom P).obj (𝟙_ M)
  let evaluation : ∀ P : M, F.obj P ⊗ F.obj (dual P) ⟶ 𝟙_ (DerivedCategory M) :=
    fun P ↦ DerivedCategory.singleFunctorTensorComparison P (dual P) ≫
      F.map ((ihom.ev P).app (𝟙_ M)) ≫ (DerivedCategory.singleFunctorObjUnitIso M).hom
  let comparison : ∀ (P : M) (N : DerivedCategory M),
      ((derivedTensor Λ S.X).obj (F.obj (dual P))).obj N ⟶
        ((derivedHom Λ S.X).obj (op (F.obj P))).obj N :=
    fun P N ↦ curry ((α_ (F.obj P) (F.obj (dual P)) N).inv ≫
      evaluation P ▷ N ≫ (λ_ N).hom)
  change
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P →
      ∀ N : S.ctf c S.X, IsIso (comparison P N.obj)) ∧
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P → IsIso (toIhomIhomUnit P)) ∧
    (∀ (P P' : M), IsFiniteLocallyProjective Λ S.X P →
      IsFiniteLocallyProjective Λ S.X P' → ∀ (f : P ⟶ P') (N : S.ctf c S.X),
        F.map ((pre f).app (𝟙_ M)) ▷ N.obj ≫ comparison P N.obj =
          comparison P' N.obj ≫ (pre (F.map f)).app N.obj) ∧
    (∀ (P : M), IsFiniteLocallyProjective Λ S.X P →
      ∀ (N N' : S.ctf c S.X) (g : N ⟶ N'),
        F.obj (dual P) ◁ g.hom ≫ comparison P N'.obj =
          comparison P N.obj ≫ (ihom (F.obj P)).map g.hom)
  have ev_nat {P P' : M} (f : P ⟶ P') :
      F.obj P ◁ F.map ((pre f).app (𝟙_ M)) ≫ evaluation P =
        F.map f ▷ F.obj (dual P') ≫ evaluation P' := by
    obtain ⟨m, hm, _⟩ := DerivedCategory.exists_singleFunctorLaxMonoidal (A := M)
    let := m
    dsimp only [evaluation]
    rw [← hm, ← hm, ← Category.assoc, Functor.LaxMonoidal.μ_natural_right]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, id_tensor_pre_app_comp_ev, F.map_comp]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP N
    obtain ⟨hd⟩ := finiteLocallyProjective_isDualizable Λ S.X P hP
    let := hd
    let : ExactPairing Pᘁ P := BraidedCategory.exactPairing_swap P Pᘁ
    have : IsIso (ihomUnitTensorToIhom P P) := isIso_ihomUnitTensorToIhom Pᘁ P P
    let := exactPairingOfIsIso P
    obtain ⟨ep, he⟩ := DerivedCategory.SingleDualPairing.singleFunctor_exactPairing P (dual P)
    let := ep
    have hev : evaluation P = ε_ (F.obj (dual P)) (F.obj P) := he.symm
    change IsIso (curry _)
    rw [hev]
    exact isIso_curry_condensedPairing_tensor _ _ _
  · intro P hP
    exact MonoidalClosed.isIso_toIhomIhomUnit_of_isDualizable
      (finiteLocallyProjective_isDualizable Λ S.X P hP)
  · intro P P' _ _ f N
    dsimp only [comparison]
    rw [← curry_natural_left, curry_pre_app]
    congr 1
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      ev_nat f, comp_whiskerRight_assoc, ← associator_inv_naturality_left_assoc]
    -- The remaining tensor object is definitionally the derivedTensor object.
    rfl
  · intro P _ N N' g
    dsimp only [comparison]
    rw [← curry_natural_left, ← curry_natural_right]
    congr 1
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    simp

end WeilConjectures
