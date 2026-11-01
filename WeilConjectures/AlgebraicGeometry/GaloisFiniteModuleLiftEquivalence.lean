/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftTransport
public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftStalkComparison
public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftUnderlyingAction

/-! # Finite module transport and normalized stalk comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

/-- The module-valued stalk comparison selected from the explicit candidate.  Its
underlying component is fixed by `galoisFiniteModuleLiftUnderlyingStalkComparison`,
so this definition does not choose an unrelated witness. -/
noncomputable def galoisFiniteModuleLiftTauM
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (κ : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) ≃
        (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F.obj)))
    (κgerm : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R) (U : Y.Etale)
      (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)),
      κ R F ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x
          (galoisUnderlyingSetSheaf R F.obj).obj s)
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (Lops : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (A : LambdaModuleObject Y R),
      let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
      let X : Y.FLC := ⟨A.sheaf, A.isFLC⟩
      ((L R).functor.obj A).X = X ∧
      HEq ((L R).functor.obj A).add
        (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add)) ∧
      HEq ((L R).functor.obj A).zero
        (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero)) ∧
      HEq ((L R).functor.obj A).neg (I.preimage (X := X) (Y := X) A.str.neg) ∧
      ∀ r, HEq (((L R).functor.obj A).smul r)
        (I.preimage (X := X) (Y := X) (A.str.smul r)))
    (Lmaps : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (A B : LambdaModuleObject Y R) (f : A ⟶ B),
      HEq (((L R).functor.map f).val).hom f.hom)
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
        galoisUnderlyingFLC R F.obj (h R F))
    (R : Type (u + 1)) [Ring R] [Finite R] :
      (galoisFiniteModuleLiftEquivalence G E L ε R).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R) :=
  Classical.choose (galoisFiniteModuleLiftStalkComparison_exists y G E τ κ κgerm
    L Lops Lmaps ε εaction h hL R)

/-- The explicit equivalence and the remaining module-valued stalk transport step.

Proof: for each finite ring, use `lisseToModuleObject_isIso_of_categories` and compose
its equivalence with `L`. The definition above transports the resulting internal module
through `E` using `equivalence_induces_internalModules`, then uses
`internalModules_finiteContAction` and the supplied `ε`. The remaining theorem states the
module-valued stalk transport for this fixed equivalence: its carrier predicate is fixed
to `galoisUnderlyingFLC`, and its maps `hκ` and `hq` identify the stalk comparison and
the transported action. The action component below proves the final evaluation identity
from those two equations and `hτ`.
Source: Stacks Project, Tag 0DV5 (3), and node `new-e4-galois-finite-module-lift`.
(blueprint: new-c7-galois-finite-module-lift-equivalence). -/
theorem galois_finite_module_lift_equivalence
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (_η : Φ.functor ⋙ ObjectProperty.ι _ ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
      FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u})
    (τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u} ≅
      ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
    (_hτ : ∀ (F : Y.FLC) (g : G) (z : ULift.{u + 1} (E.functor.obj F).obj.V),
      τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
        (γ g).hom.app F (τ.hom.app F z))
    (κ : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R),
      (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) ≃
        (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf R F.obj)))
    (κgerm : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (F : LisseModuleSheafCategory Y R)
      (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)),
      κ R F ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F.obj).obj s)
    (L : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      LambdaModuleObject Y R ≌ InternalModule R Y.FLC)
    (Lops : ∀ (R : Type (u + 1)) [Ring R] [Finite R] (A : LambdaModuleObject Y R),
      let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
      let X : Y.FLC := ⟨A.sheaf, A.isFLC⟩
      ((L R).functor.obj A).X = X ∧
      HEq ((L R).functor.obj A).add
        (I.preimage (X := X ⨯ X) (Y := X) (prodComparison I X X ≫ A.str.add)) ∧
      HEq ((L R).functor.obj A).zero
        (I.preimage (X := ⊤_ Y.FLC) (Y := X) (terminalComparison I ≫ A.str.zero)) ∧
      HEq ((L R).functor.obj A).neg (I.preimage (X := X) (Y := X) A.str.neg) ∧
      ∀ r, HEq (((L R).functor.obj A).smul r)
        (I.preimage (X := X) (Y := X) (A.str.smul r)))
    (_Lmaps : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (A B : LambdaModuleObject Y R) (f : A ⟶ B),
      HEq (((L R).functor.map f).val).hom f.hom)
    (ε : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (εaction : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      Nonempty ((ε R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
        ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
          (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G))  :
    let e : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
        LisseModuleSheafCategory Y R ≌ galoisFiniteRepresentations R G :=
      fun R _ _ ↦ galoisFiniteModuleLiftEquivalence G E L ε R
    ∃ (τM : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
        (e R).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R))
      (h : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
        ∀ (F : LisseModuleSheafCategory Y R),
          IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj))
      (q : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
        (F : LisseModuleSheafCategory Y R),
        ((e R).functor.obj F).obj.V →
          ULift.{u + 1} (E.functor.obj
            (galoisUnderlyingFLC R F.obj (h R F))).obj.V)
      (_hκ : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
        (F : LisseModuleSheafCategory Y R)
        (z : ((e R).functor.obj F).obj.V),
        κ R F ((τM R).hom.app F z) =
          τ.hom.app (galoisUnderlyingFLC R F.obj (h R F)) (q R F z))
      (_hq : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
        (F : LisseModuleSheafCategory Y R) (g : G)
        (z : ((e R).functor.obj F).obj.V),
        q R F (((e R).functor.obj F).obj.ρ g z) =
          ⟨((E.functor.obj (galoisUnderlyingFLC R F.obj (h R F))).obj.ρ g).hom
            (q R F z).down⟩), True := by
  dsimp only
  let h : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj) :=
    fun R _ _ F ↦ (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F.obj).mp F.property
  let hL : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      ((L R).functor.obj ((lisseToModuleObject Y R).obj F)).X =
        galoisUnderlyingFLC R F.obj (h R F) := by
    intro R _ _ F
    let A := (lisseToModuleObject Y R).obj F
    have hx := (Lops R A).1
    have hsub : (⟨A.sheaf, A.isFLC⟩ : Y.FLC) =
        galoisUnderlyingFLC R F.obj (h R F) := by
      apply ObjectProperty.FullSubcategory.ext
      rfl
    exact hx.trans hsub
  have ht := galoisFiniteModuleLiftStalkComparison_exists y G E τ κ κgerm
    L Lops _Lmaps ε εaction h hL
  let τM : ∀ (R : Type (u + 1)) [Ring R] [Finite R],
      (galoisFiniteModuleLiftEquivalence G E L ε R).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R) :=
    fun R _ _ ↦ galoisFiniteModuleLiftTauM y G E τ κ κgerm
      L Lops _Lmaps ε εaction h hL R
  let q : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      (F : LisseModuleSheafCategory Y R),
      ((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.V →
        ULift.{u + 1} (E.functor.obj
          (galoisUnderlyingFLC R F.obj (h R F))).obj.V :=
    fun R _ _ F ↦ galoisFiniteModuleLiftUnderlyingComparison G E L ε εaction R F
      (h R F) (hL R F)
  refine ⟨τM, h, q, ?_, ?_, trivial⟩
  · intro R _ _ F z
    change κ R F ((galoisFiniteModuleLiftTauM y G E τ κ κgerm
      L Lops _Lmaps ε εaction h hL R).hom.app F z) =
      τ.hom.app (galoisUnderlyingFLC R F.obj (h R F))
        (galoisFiniteModuleLiftUnderlyingComparison G E L ε εaction R F
          (h R F) (hL R F) z)
    have hz := Classical.choose_spec (ht R) F z
    rw [show ((galoisFiniteModuleLiftTauM y G E τ κ κgerm
      L Lops _Lmaps ε εaction h hL R).hom.app F) z =
        galoisFiniteModuleLiftUnderlyingStalkComparison y G E τ κ L ε εaction R F
          (h R F) (hL R F) z from hz]
    exact (κ R F).apply_symm_apply _
  · intro R _ _ F g z
    exact galoisFiniteModuleLiftUnderlyingComparison_action y G E τ L ε εaction h hL R F g z

end AlgebraicGeometry.Scheme
