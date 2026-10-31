/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteScalarUnderlying

/-! # The normalized inverse scalar comparison on unit germs -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

private theorem scalarModuleSmallLimits (R : Type (u + 1)) [Ring R] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

attribute [local instance] scalarModuleSmallLimits

/-- The inverse comparison sends a unit tensor of a normalized germ to the normalized
extended germ. Source: Stacks 0DV5 (3), base change of coefficients in
`cor-galois-lisse-representations`. (blueprint: new-w8-galois-scalar-inverse-germ).

Proof: expand the four inverse factors of the underlying comparison. Naturality of the
scalar adjunction unit moves the fibre normalization inside the unit tensor. Cancel
that normalization against its inverse. Apply the supplied scalar-stalk germ identity,
and then naturality of the germ map for the underlying sheaf comparison. -/
theorem galois_finite_scalar_inverse_germ
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ Y} {G : Type u} [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G)
    {R S : Type (u + 1)} [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S)
    (B : LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S)
    (α : B ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f)
    (σ : (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R) ⋙
      ModuleCat.ringExtendScalars.{u + 1, u + 1} f ≅
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f ⋙
        (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} S))
    (hσ : ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
      (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj (op U)),
      σ.hom.app F ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).unit.app _
        ((pointSmallEtale y).toPresheafFiber U x F.obj s)) =
      (pointSmallEtale y).toPresheafFiber U x
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).obj
        ((toSheafify Y.smallEtaleTopology
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
          ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).unit.app _ s)))
    (F : LisseModuleSheafCategory Y R) (U : Y.Etale)
    (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)) :
    ((galoisFiniteScalarUnderlying d R S f B α σ).inv.app F)
      ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).unit.app _
        ((d.τ R).inv.app F ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s))) =
    (d.τ S).inv.app (B.obj F)
      ((pointSmallEtale y).toPresheafFiber U x (B.obj F).obj.obj
        ((α.inv.app F).hom.app (op U)
          ((toSheafify Y.smallEtaleTopology
            (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
            ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).unit.app _ s)))) := by
  let p := pointSmallEtale y
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  have hmap {M N : ModuleCat.{u + 1} R} (φ : M ⟶ N) (m : M) :
      E.map φ (adj.unit.app M m) = adj.unit.app N (φ m) :=
    (congrArg (fun k ↦ k m) (adj.unit.naturality φ)).symm
  change (d.τ S).inv.app (B.obj F)
    (p.sheafFiber.map (α.inv.app F)
      (σ.hom.app F.obj (E.map ((d.τ R).hom.app F)
        (adj.unit.app _ ((d.τ R).inv.app F (p.toPresheafFiber U x F.obj.obj s)))))) = _
  rw [hmap]
  have ht := ConcreteCategory.congr_hom ((d.τ R).inv_hom_id_app F)
    (p.toPresheafFiber U x F.obj.obj s)
  change (d.τ R).hom.app F
      ((d.τ R).inv.app F (p.toPresheafFiber U x F.obj.obj s)) =
    p.toPresheafFiber U x F.obj.obj s at ht
  rw [ht]
  erw [hσ]
  congr 1
  exact p.toPresheafFiber_naturality_apply (α.inv.app F).hom U x _

end AlgebraicGeometry.Scheme
