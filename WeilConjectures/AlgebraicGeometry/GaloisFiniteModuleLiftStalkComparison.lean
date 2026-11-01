/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFiniteModuleLiftTransport
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Module stalk comparison transport -/

@[expose] public section

set_option autoImplicit false

universe u r c v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

private theorem comparison_linear
    {R : Type r} [Ring R]
    {C : Type c} [Category.{v} C] [HasFiniteProducts C]
    (A : InternalModule R C) (U V : C ⥤ Type w) [PreservesFiniteProducts U]
    (τ : U ≅ V) (M N : ModuleCat.{w} R)
    (m : U.obj A.X ≃ M) (n : V.obj A.X ≃ N)
    (hmadd : ∀ (T : C) (a b : T ⟶ A.X) (t : U.obj T),
      m (U.map (prod.lift a b ≫ A.add) t) = m (U.map a t) + m (U.map b t))
    (hmsmul : ∀ (r : R) (t : U.obj A.X),
      m (U.map (A.smul r) t) = r • m t)
    (hnadd : ∀ (T : C) (a b : T ⟶ A.X) (t : V.obj T),
      n (V.map (prod.lift a b ≫ A.add) t) = n (V.map a t) + n (V.map b t))
    (hnsmul : ∀ (r : R) (t : V.obj A.X),
      n (V.map (A.smul r) t) = r • n t) :
    (∀ x y : M, n (τ.hom.app A.X (m.symm (x + y))) =
      n (τ.hom.app A.X (m.symm x)) + n (τ.hom.app A.X (m.symm y))) ∧
    (∀ (r : R) (x : M), n (τ.hom.app A.X (m.symm (r • x))) =
      r • n (τ.hom.app A.X (m.symm x))) := by
  have hnatur {X Z : C} (f : X ⟶ Z) (t : U.obj X) :
      τ.hom.app Z (U.map f t) = V.map f (τ.hom.app X t) :=
    ConcreteCategory.congr_hom (τ.hom.naturality f) t
  constructor
  · intro x y
    let e := PreservesLimitPair.iso U A.X A.X ≪≫ Types.binaryProductIso _ _
    let t := e.inv (m.symm x, m.symm y)
    have ht₁ : U.map (prod.fst : A.X ⨯ A.X ⟶ A.X) t = m.symm x := by
      have h : e.inv ≫ U.map prod.fst =
          (↾(fun p : U.obj A.X × U.obj A.X ↦ p.1) :
            U.obj A.X × U.obj A.X ⟶ U.obj A.X) := by
        simp [e, Category.assoc, PreservesLimitPair.iso_inv_fst]
      exact congrArg (fun f : U.obj A.X × U.obj A.X ⟶ U.obj A.X ↦
        f (m.symm x, m.symm y)) h
    have ht₂ : U.map (prod.snd : A.X ⨯ A.X ⟶ A.X) t = m.symm y := by
      have h : e.inv ≫ U.map prod.snd =
          (↾(fun p : U.obj A.X × U.obj A.X ↦ p.2) :
            U.obj A.X × U.obj A.X ⟶ U.obj A.X) := by
        simp [e, Category.assoc, PreservesLimitPair.iso_inv_snd]
      exact congrArg (fun f : U.obj A.X × U.obj A.X ⟶ U.obj A.X ↦
        f (m.symm x, m.symm y)) h
    have ht : m.symm (x + y) = U.map (A.add) t := by
      apply m.injective
      simpa [ht₁, ht₂] using (hmadd (A.X ⨯ A.X) prod.fst prod.snd t).symm
    rw [ht, hnatur]
    have h := hnadd (A.X ⨯ A.X) prod.fst prod.snd (τ.hom.app _ t)
    simpa only [prod.lift_fst_snd, Category.id_comp, ← hnatur, ht₁, ht₂] using h
  · intro r x
    have ht : m.symm (r • x) = U.map (A.smul r) (m.symm x) := by
      apply m.injective
      simpa using (hmsmul r (m.symm x)).symm
    rw [ht, hnatur, hnsmul]

private theorem stalk_operations
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (κ : (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) ≃
      (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F))))
    (hgerm : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
      (s : F.obj.obj (op U)),
      κ ((pointSmallEtale y).toPresheafFiber U x F.obj s) =
        (pointSmallEtale y).toPresheafFiber U x
          (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F)).obj s) :
    (∀ (T : Sheaf Y.smallEtaleTopology (Type (u + 1)))
      (a b : T ⟶ ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F))
      (t : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj T),
      κ.symm ((pointSmallEtale y).sheafFiber.map
        (prod.lift a b ≫ (underlyingModuleObjectStruct F).add) t) =
      κ.symm ((pointSmallEtale y).sheafFiber.map a t) +
        κ.symm ((pointSmallEtale y).sheafFiber.map b t)) ∧
    (∀ (r : R) (t : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
      (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F))),
      κ.symm ((pointSmallEtale y).sheafFiber.map
        ((underlyingModuleObjectStruct F).smul r) t) = r • κ.symm t) := by
  let p := pointSmallEtale y
  have hs := (existsUnique_moduleObjectStruct_isUnderlying F).exists.choose_spec
  change (underlyingModuleObjectStruct F).IsUnderlying F at hs
  have hg (U : Y.Etale) (x : p.fiber.obj U) (s : F.obj.obj (op U)) :
      κ.symm (p.toPresheafFiber U x ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F).obj s) =
        p.toPresheafFiber U x F.obj s := by
    rw [← hgerm, Equiv.symm_apply_apply]
  constructor
  · intro T a b t
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := T.obj) t
    change κ.symm (p.presheafFiber.map
      (prod.lift a b ≫ (underlyingModuleObjectStruct F).add).hom
      (p.toPresheafFiber U x T.obj s)) = _
    rw [p.toPresheafFiber_naturality_apply]
    change κ.symm (p.toPresheafFiber U x ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F).obj
      ((underlyingModuleObjectStruct F).add.hom.app (op U)
        ((prod.lift a b).hom.app (op U) s))) = _
    rw [hs.1]
    have hfst := congrArg (fun f ↦ f.hom.app (op U) s) (prod.lift_fst a b)
    have hsnd := congrArg (fun f ↦ f.hom.app (op U) s) (prod.lift_snd a b)
    change (prod.fst : ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F) ⨯
        ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F) ⟶ _).hom.app (op U)
      ((prod.lift a b).hom.app (op U) s) = a.hom.app (op U) s at hfst
    change (prod.snd : ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F) ⨯
        ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F) ⟶ _).hom.app (op U)
      ((prod.lift a b).hom.app (op U) s) = b.hom.app (op U) s at hsnd
    rw [hfst, hsnd]
    change _ = κ.symm (p.presheafFiber.map a.hom
      (p.toPresheafFiber U x T.obj s)) +
        κ.symm (p.presheafFiber.map b.hom (p.toPresheafFiber U x T.obj s))
    erw [p.toPresheafFiber_naturality_apply, p.toPresheafFiber_naturality_apply,
      hg, hg, hg, map_add]
    rfl
  · intro r t
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
      (P := (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F)).obj) t
    change κ.symm (p.presheafFiber.map
      ((underlyingModuleObjectStruct F).smul r).hom
      (p.toPresheafFiber U x ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F).obj s)) = _
    rw [p.toPresheafFiber_naturality_apply, hs.2.2.2, hg, hg, map_smul]

private theorem cast_binary
    {C : Type c} [Category.{v} C] [HasFiniteProducts C]
    {X Z : C} (h : X = Z) (a : X ⨯ X ⟶ X) (b : Z ⨯ Z ⟶ Z) (hab : HEq a b) :
    a ≫ eqToHom h = prod.map (eqToHom h) (eqToHom h) ≫ b := by
  cases h
  cases hab
  simp

private theorem cast_unary
    {C : Type c} [Category.{v} C]
    {X Z : C} (h : X = Z) (a : X ⟶ X) (b : Z ⟶ Z) (hab : HEq a b) :
    a ≫ eqToHom h = eqToHom h ≫ b := by
  cases h
  cases hab
  simp

private theorem stalk_internal_operations
    {Y : Scheme.{u}} [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (R : Type (u + 1)) [Ring R]
    (F : LisseModuleSheafCategory Y R)
    (hF : IsLisseEtaleSheafOfSets (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj)))
    (A : InternalModule R Y.FLC)
    (hX : A.X = (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC))
    (ha : HEq A.add
      ((ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))).preimage
        (X := (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC) ⨯
          (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC))
        (Y := (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC))
        (prodComparison (ObjectProperty.ι _) _ _ ≫ (underlyingModuleObjectStruct F.obj).add)))
    (hs : ∀ r, HEq (A.smul r)
      ((ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))).preimage
        (X := (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC))
        (Y := (⟨(sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj, hF⟩ : Y.FLC))
        ((underlyingModuleObjectStruct F.obj).smul r)))
    (κ : (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F.obj) ≃
      (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj))))
    (hgerm : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U)
      (s : F.obj.obj.obj (op U)),
      κ ((pointSmallEtale y).toPresheafFiber U x F.obj.obj s) =
        (pointSmallEtale y).toPresheafFiber U x
          (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F.obj)).obj s) :
    let V := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))
    let n := ((V.mapIso (eqToIso hX)).toEquiv).trans κ.symm
    (∀ (T : Y.FLC) (a b : T ⟶ A.X) (t : V.obj T),
      n (V.map (prod.lift a b ≫ A.add) t) = n (V.map a t) + n (V.map b t)) ∧
    (∀ (r : R) (t : V.obj A.X), n (V.map (A.smul r) t) = r • n t) := by
  let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let p := pointSmallEtale y
  obtain ⟨hadd, hsmul⟩ := stalk_operations y R F.obj κ hgerm
  dsimp only
  constructor
  · intro T a b t
    have he := cast_binary hX A.add _ ha
    have hh : I.map (prod.lift a b ≫ A.add ≫ eqToHom hX) =
        prod.lift (I.map (a ≫ eqToHom hX)) (I.map (b ≫ eqToHom hX)) ≫
          (underlyingModuleObjectStruct F.obj).add := by
      rw [he, ← Category.assoc, prod.lift_map]
      erw [I.map_comp, I.map_preimage]
      rw [← Category.assoc]
      congr 1
      apply prod.hom_ext
      · simp only [I, Category.assoc, prodComparison_fst, ← Functor.map_comp, prod.lift_fst]
      · simp only [I, Category.assoc, prodComparison_snd, ← Functor.map_comp, prod.lift_snd]
    change κ.symm (p.sheafFiber.map (I.map (eqToHom hX))
      (p.sheafFiber.map (I.map (prod.lift a b ≫ A.add)) t)) = _
    rw [← types_comp_apply, ← Functor.map_comp, ← I.map_comp, Category.assoc, hh]
    erw [hadd]
    simp only [Functor.map_comp, types_comp_apply, I.map_comp]
    rfl
  · intro r t
    have he := cast_unary hX (A.smul r) _ (hs r)
    have hh : I.map (A.smul r ≫ eqToHom hX) =
        I.map (eqToHom hX) ≫ (underlyingModuleObjectStruct F.obj).smul r := by
      rw [he, I.map_comp, I.map_preimage]
    change κ.symm (p.sheafFiber.map (I.map (eqToHom hX))
      (p.sheafFiber.map (I.map (A.smul r)) t)) = _
    rw [← types_comp_apply, ← Functor.map_comp, ← I.map_comp, hh,
      Functor.map_comp, types_comp_apply]
    exact hsmul r _

private theorem map_pair_inverse
    {C : Type c} [Category.{v} C] [HasFiniteProducts C]
    {D : Type w} [Category D] [HasFiniteProducts D]
    (E : C ⥤ D) [PreservesFiniteProducts E]
    {T X : C} (a b : T ⟶ X) :
    prod.lift (E.map a) (E.map b) ≫ inv (prodComparison E X X) =
      E.map (prod.lift a b) := by
  apply (cancel_mono (prodComparison E X X)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext <;> simp [prodComparison, ← E.map_comp]

private theorem action_cast
    {G : Type u} [Group G] [TopologicalSpace G]
    {X Z : ContAction FintypeCat.{u} G} (h : X = Z) (x : X.obj.V) :
    (eqToHom h).hom.hom x = cast (congrArg (fun W ↦ W.obj.V.obj) h) x := by
  cases h
  rfl

private theorem source_internal_operations
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
    (R : Type (u + 1)) [Ring R] [Finite R]
    (A : InternalModule R Y.FLC)
    (ε : FiniteContinuousModule.{u + 1, u, u} R G ≌ galoisFiniteRepresentations R G)
    (α : ε.functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ≅
      ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} R).mapAction G) :
    let K := galoisFiniteModuleLiftInternalEquivalence G E R
    let B := K.functor.obj A
    let M := galoisFiniteModuleLiftFiniteEquivalence G R
    let C := M.functor.obj B
    let U := E.functor ⋙ forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
    let hX : B.X = E.functor.obj A.X := congrArg (fun H ↦ H.obj A)
      (Classical.choose_spec (equivalence_induces_internalModules R E).2.2).1
    let hc := congrArg (fun X : ContAction FintypeCat.{u} G ↦ X.obj.V.obj) hX
    ∃ m : U.obj A.X ≃ (ε.functor.obj C).obj.V,
      (∀ (T : Y.FLC) (a b : T ⟶ A.X) (t : U.obj T),
        m (U.map (prod.lift a b ≫ A.add) t) = m (U.map a t) + m (U.map b t)) ∧
      (∀ (r : R) (t : U.obj A.X), m (U.map (A.smul r) t) = r • m t) ∧
      ∀ z, m.symm z =
        ⟨cast hc ((galoisFiniteModuleLiftUnderlyingForgetIso G R).inv.app B |>.hom.hom
          ((α.hom.app C).hom.hom z).down)⟩ := by
  dsimp only
  let K := galoisFiniteModuleLiftInternalEquivalence G E R
  let B := K.functor.obj A
  let M := galoisFiniteModuleLiftFiniteEquivalence G R
  let C := M.functor.obj B
  let hX : B.X = E.functor.obj A.X := congrArg (fun H ↦ H.obj A)
    (Classical.choose_spec (equivalence_induces_internalModules R E).2.2).1
  let hc := congrArg (fun X : ContAction FintypeCat.{u} G ↦ X.obj.V.obj) hX
  let i := galoisFiniteModuleLiftUnderlyingForgetIso G R
  let ie : B.X.obj.V ≃ C.obj.obj.V :=
    ((Action.forget (Type u) G).mapIso (i.app B)).toEquiv
  let j := ((Action.forget (ModuleCat.{u + 1} R) G).mapIso (α.app C)).toLinearEquiv.symm
  let m : ULift.{u + 1} (E.functor.obj A.X).obj.V ≃ (ε.functor.obj C).obj.V :=
    Equiv.ulift.trans (Equiv.cast hc.symm) |>.trans ie |>.trans Equiv.ulift.symm |>.trans
      j.toEquiv
  have m_apply (t : ULift.{u + 1} (E.functor.obj A.X).obj.V) :
      m t = j ⟨ie (cast hc.symm t.down)⟩ := rfl
  have hK := (Classical.choose_spec (equivalence_induces_internalModules R E).2.2).2.1 A
  have hi := Classical.choose_spec
    ((Classical.choose_spec (internalModules_finiteContAction R G)).2.2)
  refine ⟨m, ?_, ?_, ?_⟩
  · intro T a b t
    change ULift.{u + 1} (E.functor.obj T).obj.V at t
    let a' : E.functor.obj T ⟶ B.X := E.functor.map a ≫ eqToHom hX.symm
    let b' : E.functor.obj T ⟶ B.X := E.functor.map b ≫ eqToHom hX.symm
    have he := cast_binary hX B.add _ hK.1
    have hh : (prod.lift a' b' ≫ B.add) ≫ eqToHom hX =
        E.functor.map (prod.lift a b ≫ A.add) := by
      rw [Category.assoc, he, ← Category.assoc, prod.lift_map]
      simp only [a', b', Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
      rw [← Category.assoc, map_pair_inverse, ← E.functor.map_comp]
    have hv : cast hc.symm ((E.functor.map (prod.lift a b ≫ A.add)).hom.hom t.down) =
        (prod.lift a' b' ≫ B.add).hom.hom t.down := by
      apply (Equiv.cast hc).injective
      simp only [Equiv.cast_apply, cast_cast, cast_eq]
      erw [← action_cast hX]
      exact (congrArg (fun f ↦ f.hom.hom t.down) hh).symm
    have hval (f : T ⟶ A.X) :
        cast hc.symm ((E.functor.map f).hom.hom t.down) =
          (E.functor.map f ≫ eqToHom hX.symm).hom.hom t.down := by
      change cast hc.symm ((E.functor.map f).hom.hom t.down) =
        (eqToHom hX.symm).hom.hom ((E.functor.map f).hom.hom t.down)
      erw [action_cast]
    change j ⟨ie (cast hc.symm
      ((E.functor.map (prod.lift a b ≫ A.add)).hom.hom t.down))⟩ =
        j ⟨ie (cast hc.symm ((E.functor.map a).hom.hom t.down))⟩ +
          j ⟨ie (cast hc.symm ((E.functor.map b).hom.hom t.down))⟩
    rw [hv, hval, hval, ← map_add]
    congr 1
    exact congrArg ULift.up (hi B (E.functor.obj T) a' b' t.down).1
  · intro r t
    change ULift.{u + 1} (E.functor.obj A.X).obj.V at t
    have he := cast_unary hX (B.smul r) _ (hK.2.2.2 r)
    have hh : B.smul r ≫ eqToHom hX = eqToHom hX ≫ E.functor.map (A.smul r) := he
    have hv : cast hc.symm ((E.functor.map (A.smul r)).hom.hom t.down) =
        (B.smul r).hom.hom (cast hc.symm t.down) := by
      apply (Equiv.cast hc).injective
      simp only [Equiv.cast_apply, cast_cast, cast_eq]
      have h := congrArg (fun f ↦ f.hom.hom (cast hc.symm t.down)) hh
      change (eqToHom hX).hom.hom ((B.smul r).hom.hom (cast hc.symm t.down)) =
        (E.functor.map (A.smul r)).hom.hom
          ((eqToHom hX).hom.hom (cast hc.symm t.down)) at h
      simpa only [action_cast, cast_cast, cast_eq] using h.symm
    change j ⟨ie (cast hc.symm ((E.functor.map (A.smul r)).hom.hom t.down))⟩ =
      r • j ⟨ie (cast hc.symm t.down)⟩
    rw [hv, ← map_smul]
    congr 1
    have h := (hi B B.X (𝟙 B.X) (𝟙 B.X) (cast hc.symm t.down)).2.2.2 r
    simp only [Category.id_comp] at h
    change ie ((B.smul r).hom.hom (cast hc.symm t.down)) =
      r • ie (cast hc.symm t.down) at h
    exact congrArg ULift.up h
  · intro z
    rfl

private theorem flc_hom_heq
    {Y : Scheme.{u}} {X Z X' Z' : Y.FLC} (hx : X = X') (hz : Z = Z')
    (f : X ⟶ Z) (g : X' ⟶ Z') (h : HEq f.hom g.hom) : HEq f g := by
  subst X'
  subst Z'
  exact heq_of_eq (ObjectProperty.hom_ext _ (eq_of_heq h))

private theorem stalk_equiv_natural
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    {F H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : F ⟶ H)
    (κF : (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) ≃
      (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F))))
    (κH : (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} R)).obj H) ≃
      (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
        (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj H))))
    (hF : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj (op U)),
      κF ((pointSmallEtale y).toPresheafFiber U x F.obj s) =
        (pointSmallEtale y).toPresheafFiber U x (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F)).obj s)
    (hH : ∀ (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (s : H.obj.obj (op U)),
      κH ((pointSmallEtale y).toPresheafFiber U x H.obj s) =
        (pointSmallEtale y).toPresheafFiber U x (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj H)).obj s)
    (t : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
      (((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F))) :
    κH.symm ((pointSmallEtale y).sheafFiber.map ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f) t) =
      (pointSmallEtale y).sheafFiber.map f (κF.symm t) := by
  let p := pointSmallEtale y
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F).obj) t
  change κH.symm (p.presheafFiber.map ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f).hom
    (p.toPresheafFiber U x ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F).obj s)) = _
  rw [p.toPresheafFiber_naturality_apply, ← hF, Equiv.symm_apply_apply]
  rw [← hH, Equiv.symm_apply_apply]
  exact (p.toPresheafFiber_naturality_apply f.hom U x s).symm

private theorem ulift_action_cast
    {G : Type u} [Group G] [TopologicalSpace G]
    {X Z : ContAction FintypeCat.{u} G} (h : X = Z) (x : ULift.{u + 1} X.obj.V) :
    ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}).map
        (eqToHom h)) x = ⟨cast (congrArg (fun W ↦ W.obj.V.obj) h) x.down⟩ := by
  cases h
  rfl

/-- The fixed stalk candidate upgrades to a natural isomorphism of modules.
The normalization assumptions `Lops` and `Lmaps` are the ones already present
in the parent finite-module lift: carrier equality alone does not identify
operations or maps of an arbitrary equivalence `L`.

Proof: the operation formulas for internal-module transport, followed by the
forget-comparison of `internalModules_finiteContAction` and the linear action
isomorphism `εaction`, identify the source operations with those of the
internal module in FLC. Every element of the target stalk is a germ, so
`κgerm` and the sectionwise characterization of `underlyingModuleObjectStruct`
identify its operations with the module-stalk operations and show that `κ`
is natural. Preservation of binary products and naturality of `τ` at the
projections and addition prove additivity; naturality at the scalar maps
proves scalar compatibility. Whiskering the supplied comparisons gives a
natural isomorphism of underlying sets whose components are exactly the
prescribed candidate. The operation calculation upgrades its bijective
components to linear equivalences, hence to a natural isomorphism in
`ModuleCat`. Additivity also gives preservation of zero and negation.
Source: Stacks Project, Tag 0DV5 (3), proof: endow the underlying sets with
the existing extra structure.
(blueprint: new-c7-galois-finite-module-lift-stalk-comparison). -/
theorem galoisFiniteModuleLiftStalkComparison_exists
    {Y : Scheme.{u}} [ConnectedSpace Y] [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (E : Y.FLC ≌ ContAction FintypeCat.{u} G)
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
        galoisUnderlyingFLC R F.obj (h R F)) :
    ∀ (R : Type (u + 1)) [Ring R] [Finite R], ∃ τM :
      (galoisFiniteModuleLiftEquivalence G E L ε R).functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ≅
        ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber
          (A := ModuleCat.{u + 1} R),
      ∀ (F : LisseModuleSheafCategory Y R) (z :
        ((galoisFiniteModuleLiftEquivalence G E L ε R).functor.obj F).obj.V),
        (τM.hom.app F) z =
          galoisFiniteModuleLiftUnderlyingStalkComparison y G E τ κ L ε εaction R F
            (h R F) (hL R F) z := by
  classical
  intro R _ _
  let A := lisseToModuleObject Y R
  let K := galoisFiniteModuleLiftInternalEquivalence G E R
  let M := galoisFiniteModuleLiftFiniteEquivalence G R
  let Fc := A ⋙ (L R).functor ⋙ K.functor
  let Fd := Fc ⋙ M.functor
  let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let D : LisseModuleSheafCategory Y R ⥤ Y.FLC :=
    ObjectProperty.lift (IsLisseEtaleSheafOfSets (T := Y))
      (ObjectProperty.ι _ ⋙ sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R)))
      (fun F ↦ by
        change IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj)
        exact h R F)
  let Q := forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
    CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  let U := E.functor ⋙ Q
  let V := I ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1))
  let Src := (galoisFiniteModuleLiftEquivalence G E L ε R).functor ⋙ ObjectProperty.ι _ ⋙
    forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)
  let Tgt : LisseModuleSheafCategory Y R ⥤ ModuleCat.{u + 1} R :=
    ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber
  have hD : A ⋙ (L R).functor ⋙ InternalModule.forget R Y.FLC = D := by
    apply Functor.hext (fun F ↦ by
      change ((L R).functor.obj (A.obj F)).X = galoisUnderlyingFLC R F.obj (h R F)
      exact hL R F)
    intro F H f
    exact flc_hom_heq (hL R F) (hL R H) _ _
      (Lmaps R (A.obj F) (A.obj H) (A.map f))
  have hK := (Classical.choose_spec (equivalence_induces_internalModules R E).2.2).1
  have hO : Fc ⋙ InternalModule.forget R (ContAction FintypeCat.{u} G) =
      D ⋙ E.functor := by
    change (A ⋙ (L R).functor) ⋙ (K.functor ⋙ InternalModule.forget R _) = _
    erw [hK]
    change (A ⋙ (L R).functor ⋙ InternalModule.forget R Y.FLC) ⋙ E.functor = _
    rw [hD]
  let α := Classical.choice (εaction R)
  let i := galoisFiniteModuleLiftUnderlyingForgetIso G R
  let β₀ := Functor.isoWhiskerRight (Functor.isoWhiskerLeft Fd α)
    (Action.forget (ModuleCat.{u + 1} R) G ⋙ CategoryTheory.forget _)
  let β₁ := Functor.isoWhiskerRight (Functor.isoWhiskerLeft Fc i)
    (Action.forget (Type u) G ⋙ uliftFunctor.{u + 1, u})
  let β₂ := Functor.isoWhiskerRight (eqToIso hO) Q
  let κT : D ⋙ V ≅ Tgt ⋙ CategoryTheory.forget _ :=
    NatIso.ofComponents (fun F ↦ (κ R F).symm.toIso) (by
      intro F H f
      ext t
      exact stalk_equiv_natural y R f.hom (κ R F) (κ R H)
        (κgerm R F) (κgerm R H) t)
  let β : Src ⋙ CategoryTheory.forget _ ≅ Tgt ⋙ CategoryTheory.forget _ :=
    β₀ ≪≫ β₁.symm ≪≫ β₂ ≪≫ Functor.isoWhiskerLeft D τ ≪≫ κT
  have hβ (F : LisseModuleSheafCategory Y R) (z : Src.obj F) :
      β.hom.app F z = galoisFiniteModuleLiftUnderlyingStalkComparison y G E τ κ
        L ε εaction R F (h R F) (hL R F) z := by
    let B := Fc.obj F
    let C := Fd.obj F
    change (κ R F).symm (τ.hom.app (D.obj F)
      (Q.map ((eqToIso hO).hom.app F)
        ⟨(i.inv.app B).hom.hom ((α.hom.app C).hom.hom z).down⟩)) = _
    rw [eqToIso.hom, eqToHom_app, ulift_action_cast]
    rfl
  have : AB5OfSize.{u, u} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : PreservesFiniteProducts U :=
    ⟨fun n ↦ preservesLimitsOfShape_of_natIso τ.symm⟩
  have hlinear (F : LisseModuleSheafCategory Y R) :
      (∀ x z : Src.obj F, β.hom.app F (x + z) = β.hom.app F x + β.hom.app F z) ∧
      (∀ (r : R) (z : Src.obj F), β.hom.app F (r • z) = r • β.hom.app F z) := by
    let AF := (L R).functor.obj (A.obj F)
    let B := Fc.obj F
    let C := Fd.obj F
    let hKB : B.X = E.functor.obj AF.X :=
      congrArg (fun H ↦ H.obj AF) hK
    obtain ⟨m, hmadd, hmsmul, hm⟩ := source_internal_operations G E R AF (ε R) α
    have hOps := Lops R (A.obj F)
    have ha : HEq AF.add
        (I.preimage (X := D.obj F ⨯ D.obj F) (Y := D.obj F)
          (prodComparison I (D.obj F) (D.obj F) ≫
            (underlyingModuleObjectStruct F.obj).add)) := hOps.2.1
    have hs : ∀ r, HEq (AF.smul r)
        (I.preimage (X := D.obj F) (Y := D.obj F)
          ((underlyingModuleObjectStruct F.obj).smul r)) := hOps.2.2.2.2
    obtain ⟨hnadd, hnsmul⟩ := stalk_internal_operations y R F (h R F) AF (hL R F)
      ha hs (κ R F) (κgerm R F)
    let n := ((V.mapIso (eqToIso (hL R F))).toEquiv).trans (κ R F).symm
    have hl := comparison_linear AF U V τ (Src.obj F) (Tgt.obj F) m n
      hmadd hmsmul hnadd hnsmul
    have hm' (z : Src.obj F) : m.symm z = Q.map (eqToHom hKB)
        ⟨(i.inv.app B).hom.hom ((α.hom.app C).hom.hom z).down⟩ := by
      rw [ulift_action_cast]
      exact hm z
    have hcomp (z : Src.obj F) : n (τ.hom.app AF.X (m.symm z)) = β.hom.app F z := by
      rw [hm', hβ]
      change (κ R F).symm (V.map (eqToHom (hL R F))
        (τ.hom.app AF.X (Q.map (eqToHom hKB)
          ⟨(i.inv.app B).hom.hom ((α.hom.app C).hom.hom z).down⟩))) = _
      erw [← types_comp_apply,
        ← ConcreteCategory.congr_hom (τ.hom.naturality (eqToHom (hL R F)))]
      change (κ R F).symm (τ.hom.app (D.obj F)
        (Q.map (E.functor.map (eqToHom (hL R F))) (Q.map (eqToHom hKB)
          ⟨(i.inv.app B).hom.hom ((α.hom.app C).hom.hom z).down⟩))) = _
      erw [← types_comp_apply (Q.map (eqToHom hKB)), ← Q.map_comp,
        eqToHom_map, eqToHom_trans, ulift_action_cast]
      rfl
    constructor
    · intro x z
      rw [← hcomp, ← hcomp, ← hcomp]
      exact hl.1 x z
    · intro r z
      rw [← hcomp, ← hcomp]
      exact hl.2 r z
  let e (F : LisseModuleSheafCategory Y R) : Src.obj F ≃ₗ[R] Tgt.obj F :=
    { (β.app F).toEquiv with
      map_add' := (hlinear F).1
      map_smul' := (hlinear F).2 }
  refine ⟨NatIso.ofComponents (fun F ↦ (e F).toModuleIso) ?_, ?_⟩
  · intro F H f
    ext z
    exact ConcreteCategory.congr_hom (β.hom.naturality f) z
  · intro F z
    exact hβ F z

#print axioms galoisFiniteModuleLiftStalkComparison_exists

end AlgebraicGeometry.Scheme
