/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.ConstantKoszulQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend

/-! # Finite realization of constant Koszul augmentation cones
Source: Stacks Project, Tags 099M, 093M and 0A0E.
(blueprint: lem-r1-constant-koszul-coefficient-cone-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)


/-- Exact realization identifies the finite algebraic augmentation cones, including
all strict transition maps. No arbitrary complex, pro-zero or derived limit occurs.
Source: Stacks Project, Tag 099M, with Tags 093M and 0A0E.
(blueprint: lem-r1-constant-koszul-coefficient-cone-comparison).

Proof: the supplied exact functor, regular module and quotient isomorphisms fix the
coefficient realization. Exterior scalar realization identifies the realized
exterior complex with the actual dual Koszul tower, naturally for the diagonals.
Tensor the source with the coefficient complex and insert the left unitor. Identify
the reduction of the coefficient complex with its finite quotient in degree zero.
The unit equation for v, projected to level n and degree zero, says that this finite
map is the realized quotient augmentation: precomposition by the degree-zero Koszul
unit is invertible. All other target degrees are zero. The source comparisons are
natural; epimorphy of each realized augmentation forces target naturality. Apply
additiveConeFamilyComparison to obtain the strict cone isomorphisms. Empty lists,
zero rings and the unit ideal require no change to these universal properties. -/
theorem constantKoszulCoefficientConeComparison
    (b : Bool)
    (E : ModuleCat.{u} A ⥤ Mod (coefficients J A I b)) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (c : SheafOfModules.unit (siteModuleRings (coefficients J A I b)) ≅
      E.obj (ModuleCat.of A A))
    (q : ∀ n : ℕ, E.obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ≅
      (res (finiteMap J A I b n)).obj
        (SheafOfModules.unit (siteModuleRings (finite J A I n))))
    (hs : ∀ x : A, c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
      ringedKoszulScalar (coefficients J A I b) (algebraSection (baseMap J A I b) x) ≫
        c.hom)
    (hq : ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ (q n).hom =
      (SheafOfModules.unitHomEquiv
        ((res (finiteMap J A I b n)).obj
          (SheafOfModules.unit (siteModuleRings (finite J A I n))))).symm
        ⟨fun V ↦ (1 : (finite J A I n).obj.obj V),
          fun f ↦ map_one ((finite J A I n).obj.map f).hom⟩)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (εA : ∀ n : ℕ, ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))))
    (tA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (htA : ∀ n m h k, (tA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n))))))
    (hqA : ∀ n m h,
      ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ ≫ (qA n m h).f 0 =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat) :
    let O := coefficients J A I b
    let U := ringedSiteRingComplex O
    ∀ (v : (ringedKoszulTensorTowerFunctor O r
        (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj U ⟶
      ((reductionTower J A I b).mapHomologicalComplex (.up ℤ)).obj U)
      (_hv : ringedKoszulLimitUnit O r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) U ≫
          (ordinaryLimit O).map v = ordinaryUnit J A I b U),
    ∃ e : ∀ n : ℕ,
        (E.mapHomologicalComplex (.up ℤ)).obj
          (HomologicalComplex.homotopyCofiber
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
          (CochainComplex.mappingCone v).asFunctor.obj (op n),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫ (CochainComplex.mappingCone v).asFunctor.map
          (homOfLE h).op := by sorry

end CategoryTheory.ConstantCompletion
