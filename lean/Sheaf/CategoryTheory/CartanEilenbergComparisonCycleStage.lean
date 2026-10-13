/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource

/-! # The cycle stage of a Cartan–Eilenberg comparison

Source: Stacks Project, Tags 015I and 015K, with the lifting property of Tag 013P(2).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Extend an augmented incoming boundary comparison to the cycles, without choosing
an object-column or outgoing-boundary comparison. The augmentation equation is written after
inclusion into the target object column, so no identification of single-complex cycles is needed.

Source: Stacks Project, Tags 015I, 015K and 013P(2);
(blueprint: lem-weil-pbc-ce-comparison-cycle-stage).

Proof: The resolution-complex sequence boundary → cycles → homology is short exact.
Its degreewise exactness follows from exact evaluation, and remains exact under F.
Identify the single-bicomplex boundary, cycles and homology with single complexes on those
objects of K and L; these identifications are natural for the augmentations and u.
The supplied boundary square becomes the boundary augmentation square after cancelling the
epimorphism K^{p-1} → B^p(K), preserved by F. Lift the homology augmentation into the
termwise injective homology column of J through the source homology augmentation using
Tag 013P(2); the latter is a monomorphic quasi-isomorphism, by its given quasi-isomorphism
and nonnegative indexing. Apply the exact-source horseshoe morphism theorem to the
boundary/cycles/homology sequence with the prescribed boundary map and this homology map.
Its middle map is y. Compose its augmentation square with the cycle inclusion to obtain
the first displayed equation. Compose its incoming square with the epimorphism from
I^{p-1} to the incoming boundary and then the target cycle inclusion. The image
factorization and toCycles_i identity give the second displayed equation. -/
theorem exists_cartanEilenberg_comparison_cycle_stage
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIres :
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJinj' : ∀ n : ℕ,
      Injective ((J.cycles p).X n) ∧
      Injective ((image (J.d (p - 1) p)).X n) ∧
      Injective ((J.homology p).X n))
    (hJres :
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (b : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (image (I.d (p - 1) p)) ⟶ image (J.d (p - 1) p))
    (hb : F.map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X (p - 1))).inv ≫
          (eI.f (p - 1)).f 0 ≫ (factorThruImage (I.d (p - 1) p)).f 0) ≫ b.f 0 =
      u.f (p - 1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X (p - 1))).inv ≫
          (eJ.f (p - 1)).f 0 ≫ (factorThruImage (J.d (p - 1) p)).f 0) :
    ∃ y : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.cycles p) ⟶ J.cycles p,
      (F.map ((HomologicalComplex.cyclesMap eI p).f 0) ≫ y.f 0 ≫
          (J.iCycles p).f 0 =
        F.map
          ((((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K).iCycles p |>.f 0) ≫
          F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
          u.f p ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0) ∧
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.toCycles (p - 1) p) ≫
          y ≫ J.iCycles p =
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (factorThruImage (I.d (p - 1) p)) ≫ b ≫ image.ι (J.d (p - 1) p) := by sorry

end CategoryTheory
