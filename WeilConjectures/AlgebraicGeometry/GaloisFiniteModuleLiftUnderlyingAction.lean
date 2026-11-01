/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftTransport

/-! # Module stalk comparison transport -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

private theorem cast_action
    {G : Type u} [Group G] [TopologicalSpace G]
    {X Y : ContAction FintypeCat.{u} G} (hXY : X = Y) (g : G) (x : X.obj.V) :
    cast (congrArg (fun Z : ContAction FintypeCat.{u} G ↦ Z.obj.V.obj) hXY)
        ((X.obj.ρ g).hom x) =
      (Y.obj.ρ g).hom
        (cast (congrArg (fun Z : ContAction FintypeCat.{u} G ↦ Z.obj.V.obj) hXY) x) := by
  subst Y
  rfl

set_option linter.unusedVariables false in
/-- The explicit comparison is equivariant for the representation action.  This is
the transport calculation for `εaction`, the underlying comparison `i`, and the
functor equality defining the internal-module transport.
Proof: expand the comparison into the three transport factors, apply the action
component of `εaction`, then use the action preservation of the finite-module
forget comparison and the internal-module equivalence; the remaining casts are
transported along the functor equality and `hL`.
Source: Stacks Project, Tag 0DV5 (3), proof; node `new-e4-galois-finite-module-lift`,
proof step 2.
(blueprint: new-c7-galois-finite-module-lift-underlying-action). -/
theorem galoisFiniteModuleLiftUnderlyingComparison_action
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (εaction : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G))
    (h : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj))
    (hL : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      ((L R).functor.obj ((lisseToModuleObject Y R).obj F)).X =
        galoisUnderlyingFLC R F.obj (h R F)) :
    ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R) (g : G)
      (z : ((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.V),
      galoisFiniteModuleLiftUnderlyingComparison G E L ε εaction R F (h R F)
          (hL R F) (((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.ρ g z) =
        ⟨((E.functor.obj (galoisUnderlyingFLC R F.obj (h R F))).obj.ρ g).hom
          ((galoisFiniteModuleLiftUnderlyingComparison G E L ε εaction R F (h R F)
            (hL R F) z).down)⟩ := by
  intro R _ _ F g z
  let A := lisseToModuleObject Y R
  let K := galoisFiniteModuleLiftInternalEquivalence G E R
  let M := galoisFiniteModuleLiftFiniteEquivalence G R
  let B := K.functor.obj ((L R).functor.obj (A.obj F))
  let C := M.functor.obj B
  let α := Classical.choice (εaction R)
  let i := galoisFiniteModuleLiftUnderlyingForgetIso G R
  let hKf := (Classical.choose_spec (equivalence_induces_internalModules R E).2.2).1
  let hKB : B.X = E.functor.obj ((L R).functor.obj (A.obj F)).X :=
    congrArg (fun H ↦ H.obj ((L R).functor.obj (A.obj F))) hKf
  let hTarget : B.X = E.functor.obj (galoisUnderlyingFLC R F.obj (h R F)) :=
    hKB.trans (congrArg (fun X : Y.FLC ↦ E.functor.obj X) (hL R F))
  have hα :
      ((α.hom.app C).hom.hom (((ε R).functor.obj C).obj.ρ g z)).down =
        C.obj.obj.ρ g (((α.hom.app C).hom.hom z).down) := by
    exact congrArg (fun f ↦ (f.hom z).down) ((α.hom.app C).comm g)
  have hi :
      (i.inv.app B).hom.hom
          (C.obj.obj.ρ g (((α.hom.app C).hom.hom z).down)) =
        (B.X.obj.ρ g).hom
          ((i.inv.app B).hom.hom (((α.hom.app C).hom.hom z).down)) := by
    exact congrArg (fun f ↦ f.hom (((α.hom.app C).hom.hom z).down))
      ((i.inv.app B).comm g)
  apply ULift.ext
  change cast (congrArg (fun X : ContAction FintypeCat.{u} G ↦ X.obj.V.obj) hTarget)
      ((i.inv.app B).hom.hom
        (((α.hom.app C).hom.hom (((ε R).functor.obj C).obj.ρ g z)).down)) =
    ((E.functor.obj (galoisUnderlyingFLC R F.obj (h R F))).obj.ρ g).hom
      (cast (congrArg (fun X : ContAction FintypeCat.{u} G ↦ X.obj.V.obj) hTarget)
        ((i.inv.app B).hom.hom (((α.hom.app C).hom.hom z).down)))
  rw [hα, hi]
  exact cast_action hTarget g _


end AlgebraicGeometry.Scheme
