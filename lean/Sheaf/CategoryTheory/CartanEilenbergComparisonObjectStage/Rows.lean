/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmented cycle/object/image rows

Source: Stacks Project, Tags 015I and 015K, the second alternating short exact row.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The kernel/object/image row of a bicomplex in horizontal degree `p`.
Source: Stacks Project, Tag 015I, the cycle/object/outgoing-boundary row. -/
noncomputable def cartanEilenbergCycleObjectRow
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ)) (p : ℤ) :
    ShortComplex (CochainComplex A ℕ) :=
  ShortComplex.mk (I.iCycles p) (factorThruImage (I.d p (p + 1))) (by
    rw [← cancel_mono (image.ι (I.d p (p + 1))), Category.assoc,
      image.fac, HomologicalComplex.iCycles_d, zero_comp])

/-- A row of augmented resolutions, with its short exact base row.
Source: Stacks Project, Tags 015I and 015K. No injectivity is included in this data. -/
structure CartanEilenbergAugmentedRow
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (R : ShortComplex (CochainComplex B ℕ)) where
  /-- The row of objects being resolved. -/
  base : ShortComplex B
  /-- Exactness of the base row. -/
  base_shortExact : base.ShortExact
  /-- The three augmentations and their row squares. -/
  augmentation : base.map (CochainComplex.single₀ B) ⟶ R
  /-- Exactness of the first augmented column. -/
  quasiIso₁ : QuasiIso augmentation.τ₁
  /-- Exactness of the middle augmented column. -/
  quasiIso₂ : QuasiIso augmentation.τ₂
  /-- Exactness of the last augmented column. -/
  quasiIso₃ : QuasiIso augmentation.τ₃

/-- Present the cycle/object/outgoing-image rows as augmented short exact rows,
with the degree-zero identifications needed to transport a base complex map.
This statement constructs rows and identifies augmentations; it constructs no
comparison map between the resolution columns and assumes no injectivity.

Source: Stacks Project, Tags 015I and 015K, alternating short exact rows and their
naturality (blueprint: lem-weil-pbc-ce-comparison-augmented-rows).

Proof: In the abelian category of resolution complexes the cycle inclusion is the
kernel of the outgoing differential, and its factorization through its image is an
epimorphism. Thus the cycle/object/image row is short exact. Evaluation is exact,
and the exact additive functor F preserves these short exact rows. Apply the same
construction to the single-degree-zero bicomplexes on K and L. Their rows are the
single complexes on cycles, objects, and outgoing images of K and L: the single
functor is exact, so its kernel and image comparison maps are isomorphisms. The
isomorphism between applying F to a single complex and the single complex on F
identifies the source base row with F of the row for K. Transport eI and eJ along
these isomorphisms to obtain the two augmentation morphisms. Their components
are quasi-isomorphisms by the six assumed quasi-isomorphisms, exactness of F,
and invariance under isomorphisms. The map on the base rows is induced by u on
cycles, objects and outgoing images. Its two squares follow respectively from
cyclesMap_i and naturality of factorThruImage. Evaluating the transported cycle
augmentation in degree zero gives the first equation. Evaluating the cycle
naturality square gives the second. Evaluating the middle augmentation and its
naturality square gives the last two equations. These identifications are valid
also for zero objects and zero differentials; no epimorphism or monomorphism of
u, and no injectivity or comparison choices, are used. -/
theorem exists_cartanEilenberg_comparison_augmented_rows
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (u : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L) (p : ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIcol : QuasiIso (eI.f p))
    (hIcycles : QuasiIso (HomologicalComplex.cyclesMap eI p))
    (hIout : QuasiIso
      (image.map (Arrow.homMk' (eI.f p) (eI.f (p + 1)) (eI.comm p (p + 1)))))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJcol : QuasiIso (eJ.f p))
    (hJcycles : QuasiIso (HomologicalComplex.cyclesMap eJ p))
    (hJout : QuasiIso
      (image.map (Arrow.homMk' (eJ.f p) (eJ.f (p + 1)) (eJ.comm p (p + 1))))) :
    ∃ (a : CartanEilenbergAugmentedRow ((cartanEilenbergCycleObjectRow I p).map
        (F.mapHomologicalComplex (ComplexShape.up ℕ))))
      (b : CartanEilenbergAugmentedRow (cartanEilenbergCycleObjectRow J p))
      (f : a.base ⟶ b.base)
      (δ : ((CochainComplex.single₀ B).obj a.base.X₁).X 0 ≅
        F.obj (((((CochainComplex.single₀ A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).cycles p).X 0))
      (γ : F.obj (K.X p) ≅ ((CochainComplex.single₀ B).obj a.base.X₂).X 0),
      a.augmentation.τ₁.f 0 = δ.hom ≫ F.map ((HomologicalComplex.cyclesMap eI p).f 0) ∧
      ((CochainComplex.single₀ B).map f.τ₁).f 0 ≫ b.augmentation.τ₁.f 0 ≫
        (J.iCycles p).f 0 =
        δ.hom ≫ F.map
          (((((CochainComplex.single₀ A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles p).f 0) ≫
          F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).hom ≫
          u.f p ≫ (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X p)).inv ≫ (eJ.f p).f 0 ∧
      F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
        (eI.f p).f 0) = γ.hom ≫ a.augmentation.τ₂.f 0 ∧
      γ.hom ≫ ((CochainComplex.single₀ B).map f.τ₂).f 0 ≫ b.augmentation.τ₂.f 0 =
        u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
          (eJ.f p).f 0 := by sorry

end CategoryTheory
