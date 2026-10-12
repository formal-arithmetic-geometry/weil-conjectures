/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.DerivedTensorTransitivity

/-!
# Scalar actions and the balanced derived tensor comparison

Source: Stacks Project, Section 06Y5, Lemma 06Y6 and the comparison-map construction
(blueprint: lem-pc-derived-tensor-action-naturality).

The target of `c` is the K-flat model `P ⊗_A (A ⊗_R R')` of the second derived tensor.
The mixed tensor definition already incorporates the associativity identification.
Module structures are passed explicitly, so the signature has no local notation or instances.
-/

@[expose] public section

set_option autoImplicit false

universe u wA wR

open CategoryTheory
open scoped TensorProduct

namespace DerivedCategory

/-- Scalar compatibility, naturality and the comparison map for balanced tensor models.
Source: Stacks Project, Section 06Y5 and Lemma 06Y6
(blueprint: lem-pc-derived-tensor-action-naturality).

Proof:
1. Use `lem-pc-balanced-derived-tensor-model` to obtain the bifunctor `T`, its comparison
   `α`, and the canonical model isomorphisms. Multiplication in the first factor gives the
   endomorphism of `M`; multiplication in the second factor gives the ring action `ρ`.
2. By clauses (2) and (3) of `lem-pc-derived-tensor-second-factor-functor`, canonical
   comparisons commute with both coefficient actions and are natural in `M`. The tensor
   product universal property gives the cohomology module structures; transport through
   `e` gives the balanced model structures. Comparisons of two models factor through their
   common derived object and are therefore linear on cohomology.
3. The comparison morphism is represented by `P ⊗_R F → P ⊗_R R'`, identified with
   `P ⊗_A (A ⊗_R R')`. This is clause (2) of `lem-pc-derived-tensor-transitivity` with
   `C = A ⊗_R R'`, the target model `P ⊗_A C`, and the identity map. It commutes with
   multiplication by every `b`, and is already `A`-linear, hence is tensor-product-linear
   on cohomology. The preceding canonical comparisons give independence of choices. -/
theorem exists_derivedTensor_action_naturality
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    ∃ T : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A),
    ∃ α : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
    Q ⋙ T.obj (Q.obj M) ⟶ (ModuleCat.mixedTotalTensor (algebraMap R A)).obj M ⋙ Q,
    (∀ M, (T.obj (Q.obj M)).IsLeftDerivedFunctor (α M)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))) ∧
    (∀ M F, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    IsIso ((α M).app F)) ∧
    (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N)
    (F : CochainComplex (ModuleCat.{u} R) ℤ),
    (T.map (Q.map g)).app (Q.obj F) ≫ (α N).app F =
    (α M).app F ≫ Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).map g).app F)) ∧
    (∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ M),
    QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
    ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (f : F ⟶ ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))),
    QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    ∃! e : Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F) ≅ (T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))),
    (α P).app F ≫ e.hom =
    (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
    (∃ ρ : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ, R' →+* End ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R')))),
    (∀ M b, ρ M b = (T.obj (Q.obj M)).map (Q.map ((CochainComplex.singleFunctor (ModuleCat.{u}
      R) (0 : ℤ)).map (ModuleCat.ofHom (LinearMap.mulLeft R b))))) ∧
    (∀ M (a : A) (b : R'), Commute (ρ M b) ((T.map (Q.map (a • 𝟙 M))).app (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))) ∧
    ∃ m : ∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ), Module (A ⊗[R] R')
      ((homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (∀ M i (a : A) (b : R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))))),
    (m M i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) (x) = a •
      ((homologyFunctor (ModuleCat.{u} A) i).map (ρ M b)).hom x) ∧
    (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N) (i : ℤ)
    (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    ((homologyFunctor (ModuleCat.{u} A) i).map ((T.map (Q.map g)).app (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))).hom
      ((m M i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) =
    (m N i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map ((T.map (Q.map g)).app (Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))).hom x)) ∧
    ∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ M),
    QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
    ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (f : F ⟶ ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))),
    QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    ∃ e : Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F) ≅ (T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))),
    ((α P).app F ≫ e.hom = (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
    (∀ a : A, Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).map (a • 𝟙 P)).app F) ≫
      e.hom =
    e.hom ≫ (T.map (Q.map (a • 𝟙 M))).app (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u}
      R) (0 : ℤ)).obj (ModuleCat.of R R')))) ∧
    ∃ n : ∀ i : ℤ, Module (A ⊗[R] R') ((homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F))),
    (∀ i (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F))),
    ((homologyFunctor (ModuleCat.{u} A) i).map (e.hom)).hom ((n
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) = (m M
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map (e.hom)).hom x)) ∧
    ∃ c : (T.obj (Q.obj M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 :
      ℤ)).obj (ModuleCat.of R R'))) ⟶ Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj
      P).obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R
      R'))),
    (e.hom ≫ c = Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).map f)) ∧
    (∀ b : R', ρ M b ≫ c = c ≫ Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).map
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).map (ModuleCat.ofHom
      (LinearMap.mulLeft R b))))) ∧
    ∃ p : ∀ i : ℤ, Module (A ⊗[R] R') ((homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (∀ i (a : A) (b : R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (p i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) (x) = a •
      ((homologyFunctor (ModuleCat.{u} A) i).map (Q.map (((ModuleCat.mixedTotalTensor
      (algebraMap R A)).obj P).map ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).map
      (ModuleCat.ofHom (LinearMap.mulLeft R b)))))).hom x) ∧
    ∀ i (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R
      R'))))),
    ((homologyFunctor (ModuleCat.{u} A) i).map (c)).hom ((m M
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) = (p
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map (c)).hom x)) :=
  sorry

end DerivedCategory
