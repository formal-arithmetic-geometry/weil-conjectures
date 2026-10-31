/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedProjectionScalarSquare

/-! # Boundary composites for the condensed scalar projection cocycle -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u u₀ u₁ u₂ v₀ v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- The source boundary s = mu followed by q tensor 1 of the scalar projection square.
Source: latest blueprint projection-formula compatibility; boundary data of the scalar cocycle
(blueprint: def-sf-condensed-scalar-projection-cocycle-data). -/
def condensedProjectionScalarSource {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a Y).obj
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K ⊗ L) ⟶
      (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
          ((scalarSixChange a X).obj K) ⊗ (scalarSixChange a Y).obj L :=
  (scalarSixTensorIso a Y
      ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K) L).hom ≫
    ((scalarCompactSupportMap a c.i c.g).app K ▷ (scalarSixChange a Y).obj L)

/-- The inner boundary d = mu followed by 1 tensor c of the scalar projection square.
Source: latest blueprint projection-formula compatibility; boundary data of the scalar cocycle
(blueprint: def-sf-condensed-scalar-projection-cocycle-data). -/
def condensedProjectionScalarInner {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a X).obj (K ⊗ (upperStar Λ.X f).leftDerivedFunctor.obj L) ⟶
      (scalarSixChange a X).obj K ⊗
        (upperStar Λ'.X f).leftDerivedFunctor.obj ((scalarSixChange a Y).obj L) :=
  (scalarSixTensorIso a X K ((upperStar Λ.X f).leftDerivedFunctor.obj L)).hom ≫
    ((scalarSixChange a X).obj K ◁ (condensedScalarPullbackIso a f).hom.app L)

/-- The target boundary t = q followed by F'(d) of the scalar projection square.
Source: latest blueprint projection-formula compatibility; boundary data of the scalar cocycle
(blueprint: def-sf-condensed-scalar-projection-cocycle-data). -/
def condensedProjectionScalarTarget {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a Y).obj ((rightDerivedLowerShriekOfCompactification Λ.X c).obj
        (K ⊗ (upperStar Λ.X f).leftDerivedFunctor.obj L)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
        ((scalarSixChange a X).obj K ⊗
          (upperStar Λ'.X f).leftDerivedFunctor.obj ((scalarSixChange a Y).obj L)) :=
  (scalarCompactSupportMap a c.i c.g).app
      (K ⊗ (upperStar Λ.X f).leftDerivedFunctor.obj L) ≫
    (rightDerivedLowerShriekOfCompactification Λ'.X c).map
      (condensedProjectionScalarInner a f K L)

/-- Monoidality written with inverse tensorators of a composite.
Proof: precompose by the invertible composite tensorator and cancel.
Source: Mathlib monoidal natural transformation tensor axiom
(blueprint: lem-sf-scalar-inverse-tensor-cocycle). -/
theorem condensedScalarInverseTensorTower
    {C : Type u₀} {D : Type u₁} {E : Type u₂}
    [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (A : C ⥤ D) (B : D ⥤ E) (H : C ⥤ E)
    [A.Monoidal] [B.Monoidal] [H.Monoidal]
    (t : A ⋙ B ⟶ H) [NatTrans.IsMonoidal t] (U V : C) :
    t.app (U ⊗ V) ≫ OplaxMonoidal.δ H U V =
      B.map (OplaxMonoidal.δ A U V) ≫
        OplaxMonoidal.δ B (A.obj U) (A.obj V) ≫ (t.app U ⊗ₘ t.app V) := by
  apply (cancel_epi (LaxMonoidal.μ (A ⋙ B) U V)).mp
  rw [NatTrans.IsMonoidal.tensor_assoc]
  simp only [Monoidal.μ_δ, Category.comp_id]
  simp only [LaxMonoidal.comp_μ, Category.assoc, ← Functor.map_comp_assoc,
    Monoidal.μ_δ, B.map_id, Category.id_comp, Monoidal.μ_δ_assoc]

/-- A coefficient tower square transported along three presentation isomorphisms.
Proof: use naturality at the initial presentation map, cancel the two middle
presentation maps, apply the original tower square, and use naturality at the
final presentation map.
Source: categorical transport of the blueprint scalar cocycle
(blueprint: lem-sf-scalar-cocycle-presentation-transport). -/
theorem condensedScalarCocyclePresentationTransport
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (A₀₁ : C₀ ⥤ C₁) (A₁₂ : C₁ ⥤ C₂) (A₀₂ : C₀ ⥤ C₂)
    (B₀₁ : D₀ ⥤ D₁) (B₁₂ : D₁ ⥤ D₂) (B₀₂ : D₀ ⥤ D₂)
    (F₀ G₀ : C₀ ⥤ D₀) (F₁ G₁ : C₁ ⥤ D₁) (F₂ G₂ : C₂ ⥤ D₂)
    (e₀ : G₀ ≅ F₀) (e₁ : G₁ ≅ F₁) (e₂ : G₂ ≅ F₂)
    (t₀₁ : F₀ ⋙ B₀₁ ≅ A₀₁ ⋙ F₁)
    (t₁₂ : F₁ ⋙ B₁₂ ≅ A₁₂ ⋙ F₂)
    (t₀₂ : F₀ ⋙ B₀₂ ≅ A₀₂ ⋙ F₂)
    (s : A₀₁ ⋙ A₁₂ ≅ A₀₂) (t : B₀₁ ⋙ B₁₂ ≅ B₀₂)
    (h : ∀ K, t.hom.app (F₀.obj K) ≫ t₀₂.hom.app K =
      B₁₂.map (t₀₁.hom.app K) ≫ t₁₂.hom.app (A₀₁.obj K) ≫ F₂.map (s.hom.app K))
    (K : C₀) :
    t.hom.app (G₀.obj K) ≫
      (Functor.isoWhiskerRight e₀ B₀₂ ≪≫ t₀₂ ≪≫
        Functor.isoWhiskerLeft A₀₂ e₂.symm).hom.app K =
      B₁₂.map ((Functor.isoWhiskerRight e₀ B₀₁ ≪≫ t₀₁ ≪≫
        Functor.isoWhiskerLeft A₀₁ e₁.symm).hom.app K) ≫
      (Functor.isoWhiskerRight e₁ B₁₂ ≪≫ t₁₂ ≪≫
        Functor.isoWhiskerLeft A₁₂ e₂.symm).hom.app (A₀₁.obj K) ≫
      G₂.map (s.hom.app K) := by
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← t.hom.naturality_assoc (e₀.hom.app K)]
  simp only [Functor.comp_map]
  rw [reassoc_of% h K]
  rw [← B₁₂.map_comp_assoc (e₁.inv.app (A₀₁.obj K)) (e₁.hom.app (A₀₁.obj K)),
    Iso.inv_hom_id_app, B₁₂.map_id, Category.id_comp]
  rw [e₂.inv.naturality]


end AlgebraicGeometry.ProEtale.CondensedRing
