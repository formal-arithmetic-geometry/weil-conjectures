/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit

/-! # Coefficient compatibility for a constituent of compact-support refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local instance] fieldSheafAbelian
attribute [local instance] fieldSheafGrothendieck
attribute [local instance] fieldSheafBigColimits
attribute [local instance] fieldSheafCoequalizers
attribute [local instance] fieldSheafMonoidalPreadditive
attribute [local instance] fieldModuleAbelian
attribute [local instance] fieldModuleGrothendieck
attribute [local instance] fieldModuleKInjectiveResolutions
attribute [local instance] fieldModuleDerivedCategory
attribute [local instance] fieldModuleColimits
attribute [local instance] fieldModuleBigColimits
attribute [local instance] fieldSheafFlatResolution
attribute [local instance] fieldModuleFlatResolution
attribute [local instance] fieldModuleCountableCoproducts
attribute [local instance] fieldModuleIntegerColimits
attribute [local instance] fieldModuleIntegerExactColimits
attribute [local instance] fieldTensorColimits
attribute [local instance] fieldTensorColimitsRight
attribute [local instance] fieldGradedTensor
attribute [local instance] fieldGradedFour
attribute [local instance] fieldGradedLeft
attribute [local instance] fieldGradedRight
attribute [local instance] fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible] condensedScalar condensedPushScalar condensedOpenScalar
  CondensedRing.lowerStar CondensedRing.upperStar CondensedRing.openImmersionLowerShriek
  fieldPushComp fieldProperOpen

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] [FlatCoefficientMap a]

private theorem restriction_coefficient_mate
    {CA DA EA CB DB EB : Type*}
    [Category* CA] [Category* DA] [Category* EA]
    [Category* CB] [Category* DB] [Category* EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : ∀ N, kB.hom.app (Q₂.obj N) ≫ U₁B.map (lv.hom.app N) ≫
        l₁.hom.app (FA.obj N) = l₂.hom.app N ≫ QX.map (kA.hom.app N))
    (M : DA) :
    U₂B.map (χ.app M) ≫ kB.hom.app (RB.obj (Q₁.obj M)) ≫
        U₁B.map (adjB.counit.app (Q₁.obj M)) ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (kA.hom.app (RA.obj M)) ≫
        QX.map (U₁A.map (adjA.counit.app M)) := by
  rw [reassoc_of% kB.hom.naturality (χ.app M)]
  rw [← U₁B.map_comp_assoc, hc, U₁B.map_comp]
  simp only [Category.assoc]
  have hn := l₁.hom.naturality (adjA.counit.app M)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [hn]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun z ↦ z ≫ QX.map (U₁A.map (adjA.counit.app M))) (hk (RA.obj M))

-- Naturality of restriction and the two open-unit transposes imply the coefficient square.

private theorem coefficient_refinement_of_restriction
    {CA DA EA CB DB EB : Type*}
    [Category* CA] [Category* DA] [Category* EA]
    [Category* CB] [Category* DB] [Category* EB]
    {J₁A : CA ⥤ DA} {J₂A : CA ⥤ EA}
    {U₁A : DA ⥤ CA} {U₂A : EA ⥤ CA}
    {J₁B : CB ⥤ DB} {J₂B : CB ⥤ EB}
    {U₁B : DB ⥤ CB} {U₂B : EB ⥤ CB}
    (a₁A : J₁A ⊣ U₁A) (a₂A : J₂A ⊣ U₂A)
    (a₁B : J₁B ⊣ U₁B) (a₂B : J₂B ⊣ U₂B)
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (tA : RA ⋙ U₂A ⟶ U₁A) (tB : RB ⋙ U₂B ⟶ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hχ : ∀ M, U₂B.map (χ.app M) ≫ tB.app (Q₁.obj M) ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (tA.app M))
    (K : CA) (αA : J₂A.obj K ⟶ RA.obj (J₁A.obj K))
    (αB : J₂B.obj (QX.obj K) ⟶ RB.obj (J₁B.obj (QX.obj K)))
    (b₁ : Q₁.obj (J₁A.obj K) ≅ J₁B.obj (QX.obj K))
    (b₂ : Q₂.obj (J₂A.obj K) ≅ J₂B.obj (QX.obj K))
    (hb₁ : a₁B.unit.app (QX.obj K) ≫ U₁B.map b₁.inv =
      QX.map (a₁A.unit.app K) ≫ l₁.inv.app (J₁A.obj K))
    (hb₂ : a₂B.unit.app (QX.obj K) ≫ U₂B.map b₂.inv =
      QX.map (a₂A.unit.app K) ≫ l₂.inv.app (J₂A.obj K))
    (hA : a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K) = a₁A.unit.app K)
    (hB : a₂B.homEquiv _ _ αB ≫ tB.app (J₁B.obj (QX.obj K)) =
      a₁B.unit.app (QX.obj K))
    [hmono : Mono (tB.app (J₁B.obj (QX.obj K)))] :
    Q₂.map αA ≫ χ.app (J₁A.obj K) ≫ RB.map b₁.hom = b₂.hom ≫ αB := by
  apply (cancel_epi b₂.inv).mp
  apply (a₂B.homEquiv _ _).injective
  apply (cancel_mono (tB.app (J₁B.obj (QX.obj K)))).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hB]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hb₂]
  simp only [Category.assoc]
  have hn := tB.naturality b₁.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  have hc := hχ (J₁A.obj K)
  have hc' : U₂B.map (χ.app (J₁A.obj K)) ≫ tB.app (Q₁.obj (J₁A.obj K)) =
      l₂.hom.app (RA.obj (J₁A.obj K)) ≫ QX.map (tA.app (J₁A.obj K)) ≫
        l₁.inv.app (J₁A.obj K) := by
    simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] using
      congrArg (fun z ↦ z ≫ l₁.inv.app (J₁A.obj K)) hc
  rw [reassoc_of% hc']
  rw [reassoc_of% l₂.hom.naturality αA]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← QX.map_comp_assoc, ← QX.map_comp_assoc]
  change QX.map (a₂A.homEquiv _ _ αA ≫ tA.app (J₁A.obj K)) ≫ _ = _
  rw [hA]
  rw [← reassoc_of% hb₁]
  rw [← U₁B.map_comp, Iso.inv_hom_id, U₁B.map_id, Category.comp_id]


-- Proof-term congruence for the inherited proof-irrelevant instance parameters.

private theorem derivedCategory_obj_eq (C : Type v₁) [Category.{v₂} C] [Abelian C]
    [LocallySmall.{v₃} C] [Abelian.HasKInjectiveResolutions C] :
    @DerivedCategory C _ _ (HasDerivedCategory.ofHasKInjectiveResolutions.{v₃} C) =
      CategoryTheory.Quotient (Localization.Construction.relations
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))) := by
  unfold DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
    HasDerivedCategory.standard
  rfl

private meta def instanceCongrHEq
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a ← Lean.instantiateMVars a
      let b ← Lean.instantiateMVars b
      let a := a.consumeMData
      let b := b.consumeMData
      if a.isFVar then
        if let some v := (← a.fvarId!.getDecl).value? then
          return ← instanceCongrHEq cache pairs n v b
      if b.isFVar then
        if let some v := (← b.fvarId!.getDecl).value? then
          return ← instanceCongrHEq cache pairs n a v
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' =>
          if (e'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
              e'.isAppOfArity ``CategoryTheory.Functor.map 8) &&
              (e'.getArg! 4).isAppOfArity ``CategoryTheory.Functor.id 2 then
            e'.getAppArgs.back!
          else e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← instanceCongrHEq cache pairs n type type'
          let htype ← instanceCongrToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← instanceCongrHEq cache (pairs.push (x, y, hxy)) n
                  (body.instantiate1 x) (body'.instantiate1 y)
                let h ← Lean.Meta.mkLambdaFVars #[x, y, hxy] h
                Lean.Meta.mkAppM ``Function.hfunext #[htype, h]
      let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let fn := e.getAppFn
        let .proj typeName index major := fn | return e
        let info := Lean.getStructureInfo (← Lean.getEnv) typeName
        let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
        return Lean.mkAppN p e.getAppArgs
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      let af := a.getAppFn.consumeMData
      let bf := b.getAppFn.consumeMData
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if af.isConstOf ``DerivedCategory && bf.isConstOf ``CategoryTheory.Quotient then
        let levels := (← Lean.getConstInfo ``DerivedCategory).levelParams.zip af.constLevels!
        let ls := (← Lean.getConstInfo ``derivedCategory_obj_eq).levelParams.map fun name ↦
          if name == `v₁ then (levels.lookup `u).get!
          else if name == `v₂ then (levels.lookup `v).get!
          else (levels.lookup `w).get!
        let h ← Lean.Meta.mkAppOptM' (Lean.mkConst ``derivedCategory_obj_eq ls)
          #[some aa[0]!, some aa[1]!, some aa[2]!, none, none]
        let some (_, left, right) := (← Lean.Meta.inferType h).eq? |
          throwError "expected derived-object equality"
        let ha ← instanceCongrHEq cache pairs n a left
        let hb ← instanceCongrHEq cache pairs n right b
        let h ← Lean.Meta.mkAppM ``heq_of_eq #[h]
        let h ← Lean.Meta.mkAppM ``HEq.trans #[ha, h]
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, hb]
      if bf.isConstOf ``DerivedCategory && af.isConstOf ``CategoryTheory.Quotient then
        let h ← instanceCongrHEq cache pairs n b a
        return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if af.isConstOf ``CategoryTheory.Preadditive.mk &&
          bf.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Preadditive.mk &&
          af.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if af.isConstOf ``CategoryTheory.Functor.mk &&
          bf.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Functor.mk &&
          af.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      let sameHead ← if af == bf then pure true else
        if af.isConst && bf.isConst && af.constName! == bf.constName! then
          Lean.Meta.isDefEq af bf
        else pure false
      if sameHead && aa.size ≥ 4 && ba.size ≥ 4 &&
          (af.isConstOf ``CategoryTheory.Functor.obj ||
            af.isConstOf ``CategoryTheory.Functor.map ||
            af.isConstOf ``CategoryTheory.NatTrans.app) then
        let sameDomain ← Lean.Meta.isDefEq aa[0]! ba[0]!
        let sameCodomain ← Lean.Meta.isDefEq aa[2]! ba[2]!
        if !sameDomain || !sameCodomain then
          let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
            let some e' ← Lean.Meta.withTransparency .instances
                (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
            let some f ← Lean.Meta.withTransparency .all
                (Lean.Meta.reduceProj? e'.getAppFn) | return none
            let e'' := Lean.mkAppN f e'.getAppArgs
            if e'' == e then return none
            return some e''
          if let some a' ← reduceComponent a then
            return ← instanceCongrHEq cache pairs n a' b
          if let some b' ← reduceComponent b then
            return ← instanceCongrHEq cache pairs n a b'
      if !sameHead || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a b'
        let reduceProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          if e''.getAppFn.isProj then
            let .proj typeName index major := e''.getAppFn | return none
            let info := Lean.getStructureInfo (← Lean.getEnv) typeName
            let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
            let e''' := Lean.mkAppN p e''.getAppArgs
            if e''' == e then return none
          return some e''
        if ← isProjection af then
          if let some a' ← reduceProjection a then
            return ← instanceCongrHEq cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← instanceCongrHEq cache pairs n a b'
        throwError "different congruence heads: {a} versus {b}"
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor := args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      let build : Lean.MetaM Lean.Expr := do
        let mut first := 0
        while first < aa.size && aa[first]! == ba[first]! do
          first := first + 1
        let f := Lean.mkAppN af (aa.extract 0 first)
        let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
        let mut args := #[]
        for i in [first:aa.size] do
          let h ← instanceCongrHEq cache pairs n aa[i]! ba[i]!
          let h ← if ct.argKinds[i - first]! == .eq then
            instanceCongrToEq h else pure h
          args := args.push aa[i]! |>.push ba[i]! |>.push h
        return Lean.mkAppN ct.proof args
      try build catch err =>
        -- Equal applications can expose their functor parameters differently.
        -- Reduce a component projection before trying to compare those parameters.
        let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          return some e''
        if let some a' ← reduceComponent a then
          return ← instanceCongrHEq cache pairs n a' b
        if let some b' ← reduceComponent b then
          return ← instanceCongrHEq cache pairs n a b'
        throw err
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private theorem cancel_map_iso {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {M N : C} {A : D} (b : M ≅ N)
    (x : A ⟶ F.obj M) (y : A ⟶ F.obj N) (h : x ≫ F.map b.hom = y) :
    y ≫ F.map b.inv = x := by
  rw [← h, Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

private theorem invert_three_sides {C : Type*} [Category* C]
    {A B D E H : C} (l : A ≅ B) (p : D ≅ E) (q : E ≅ H)
    (x : A ⟶ D) (y : B ⟶ H) (h : x ≫ p.hom ≫ q.hom = l.hom ≫ y) :
    y ≫ q.inv ≫ p.inv = l.inv ≫ x := by
  apply (cancel_epi l.hom).mp
  simp only [← Category.assoc, l.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem open_scalar_unit {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    (fieldOpenAdjunction Λ' j).unit.app ((condensedScalar a U).obj K) ≫
        (fieldDerivedUpperStar Λ' j).map ((condensedOpenScalar a j).inv.app K) =
      (condensedScalar a U).map ((fieldOpenAdjunction Λ j).unit.app K) ≫
        (CondensedRing.derivedPullIso a j).hom.app
          ((fieldDerivedOpenShriek Λ j).obj K) := by
  have ho : condensedOpenScalar a j = CondensedRing.derivedOpenImmersionShriekIso a j := by
    unfold condensedOpenScalar CondensedRing.derivedOpenImmersionShriekIso
    rfl
  have hm : (fieldOpenAdjunction Λ j).IsMateSquare (fieldOpenAdjunction Λ' j)
      (condensedOpenScalar a j) (CondensedRing.derivedPullIso a j) := by
    unfold fieldOpenAdjunction
    rw [ho]
    exact CondensedRing.isMateSquare_derivedOpenImmersionShriekIso_derivedPullIso a j
  apply cancel_map_iso (fieldDerivedUpperStar Λ' j) ((condensedOpenScalar a j).app K)
  have h := NatTrans.SquareCompatible.unit hm K
  simpa only [Functor.id_obj, Functor.comp_obj, Functor.pasteSquareIso_hom_app,
    Functor.idSquareIso_hom_app, Category.id_comp, Category.assoc, Iso.app_hom,
    fieldDerivedOpenShriek] using h

private theorem proper_scalar_counit {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1})
      (condensedRingObj Λ c.Z))) :
    (fieldDerivedUpperStar Λ' r.hom).map ((condensedPushScalar a r.hom).app M) ≫
        (fieldDerivedAdjunction Λ' r.hom).counit.app ((condensedScalar a c.Z).obj M) =
      (CondensedRing.derivedPullIso a r.hom).inv.app
          ((fieldDerivedLowerStar Λ r.hom).obj M) ≫
        (condensedScalar a c.Z).map ((fieldDerivedAdjunction Λ r.hom).counit.app M) := by
  have h := mateEquiv_counit (fieldDerivedAdjunction Λ r.hom)
    (fieldDerivedAdjunction Λ' r.hom)
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedPullIso a r.hom).inv) M
  rw [← CondensedRing.derivedPushHom_eq_mateEquiv] at h
  simp only [condensedPushScalar, condensedScalarAdjunction,
    CondensedRing.derivedPushHom, TwoSquare.mk, Iso.symm_hom, condensedScalar,
    fieldDerivedAdjunction, fieldDerivedUpperStar, fieldDerivedLowerStar,
    Functor.comp_obj, Functor.id_obj, CategoryTheory.catToReflQuiver] at h ⊢
  convert! h using 1

private theorem pull_scalar_comp {U V W : Scheme.{u}} (i : U ⟶ V) (v : V ⟶ W)
    (j : U ⟶ W) (hij : i ≫ v = j)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))) :
    ((eqToIso (congrArg (fieldDerivedUpperStar Λ') hij.symm) ≪≫
      fieldDerivedPullComp Λ' i v).hom.app ((condensedScalar a W).obj N)) ≫
        (fieldDerivedUpperStar Λ' i).map ((CondensedRing.derivedPullIso a v).inv.app N) ≫
        (CondensedRing.derivedPullIso a i).inv.app
          ((fieldDerivedUpperStar Λ v).obj N) =
      (CondensedRing.derivedPullIso a j).inv.app N ≫
        (condensedScalar a U).map
          ((eqToIso (congrArg (fieldDerivedUpperStar Λ) hij.symm) ≪≫
            fieldDerivedPullComp Λ i v).hom.app N) := by
  subst j
  simp only [eqToIso_refl, Iso.trans_hom, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Category.id_comp]
  have h := CondensedRing.squareCompatible_leftDerivedUpperStarComp a i v N
  simp only [Functor.pasteSquareIso_hom_app, Functor.comp_obj] at h
  exact invert_three_sides ((CondensedRing.derivedPullIso a (i ≫ v)).app N)
    ((CondensedRing.derivedPullIso a i).app ((fieldDerivedUpperStar Λ v).obj N))
    ((fieldDerivedUpperStar Λ' i).mapIso ((CondensedRing.derivedPullIso a v).app N))
    ((condensedScalar a U).map ((fieldDerivedPullComp Λ i v).hom.app N))
    ((fieldDerivedPullComp Λ' i v).hom.app ((condensedScalar a W).obj N)) h

-- The restriction transformation before specializing its input to an open extension.

private def restrictionNat {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : E ⥤ D} {R : D ⥤ E} (ad : F ⊣ R) (V : D ⥤ C) (U : E ⥤ C)
    (k : U ≅ F ⋙ V) : R ⋙ U ⟶ V where
  app M := k.hom.app (R.obj M) ≫ V.map (ad.counit.app M)
  naturality {M N} z := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [reassoc_of% k.hom.naturality (R.map z), ← V.map_comp,
      Adjunction.counit_naturality, V.map_comp]
    exact (Category.assoc _ _ _).symm

private theorem counitRestrictionNat_app_eq
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) {F : E ⥤ D} {R : D ⥤ E} (ad : F ⊣ R)
    (V : D ⥤ C) (U : E ⥤ C) (α : U ≅ F ⋙ V) (K : C) :
    (counitRestrictionNat J ad V U α).app K =
      (restrictionNat ad V U α).app (J.obj K) := rfl

private theorem restriction_wrapper {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    fieldProperOpenRestriction Λ r K = (fieldProperOpenRestrictionNat Λ r).app K := rfl

private theorem restrictionNat_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    fieldProperOpenRestrictionNat Λ r = counitRestrictionNat
      (fieldDerivedOpenShriek Λ c.i) (fieldDerivedAdjunction Λ r.hom)
      (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
      (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
        fieldDerivedPullComp Λ c.i r.hom) := rfl

private theorem restriction_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    fieldProperOpenRestriction Λ r K =
      (restrictionNat (fieldDerivedAdjunction Λ r.hom)
        (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
        (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
          fieldDerivedPullComp Λ c.i r.hom)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K) := by
  calc
    fieldProperOpenRestriction Λ r K =
        (fieldProperOpenRestrictionNat Λ r).app K := restriction_wrapper r K
    _ = (counitRestrictionNat
        (fieldDerivedOpenShriek Λ c.i) (fieldDerivedAdjunction Λ r.hom)
        (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
        (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
          fieldDerivedPullComp Λ c.i r.hom)).app K :=
      congrArg (fun t ↦ t.app K) (restrictionNat_eq r)
    _ = _ := counitRestrictionNat_app_eq
      (fieldDerivedOpenShriek Λ c.i) (fieldDerivedAdjunction Λ r.hom)
      (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
      (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
        fieldDerivedPullComp Λ c.i r.hom) K

private theorem lift_normalization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
      (restrictionNat (fieldDerivedAdjunction Λ r.hom)
        (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
        (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
          fieldDerivedPullComp Λ c.i r.hom)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K.obj) =
        (fieldOpenAdjunction Λ c.i).unit.app K.obj := by
  have h := congrArg
    (fun z ↦ (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫ z)
    (restriction_component r K.obj)
  exact h.symm.trans (fieldProperOpen_spec Λ r K)

private def restrictionTransform {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    fieldDerivedLowerStar Λ r.hom ⋙ fieldDerivedUpperStar Λ d.i ⟶
      fieldDerivedUpperStar Λ c.i :=
  restrictionNat (fieldDerivedAdjunction Λ r.hom)
    (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
    (eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
      fieldDerivedPullComp Λ c.i r.hom)

private theorem restriction_scalar_compat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1})
      (condensedRingObj Λ c.Z))) :
    (fieldDerivedUpperStar Λ' d.i).map ((condensedPushScalar a r.hom).app M) ≫
      (restrictionTransform (Λ := Λ') r).app ((condensedScalar a c.Z).obj M) ≫
        (CondensedRing.derivedPullIso a c.i).inv.app M =
      (CondensedRing.derivedPullIso a d.i).inv.app
        ((fieldDerivedLowerStar Λ r.hom).obj M) ≫
      (condensedScalar a X).map ((restrictionTransform (Λ := Λ) r).app M) := by
  let kA := eqToIso (congrArg (fieldDerivedUpperStar Λ) r.i_hom.symm) ≪≫
    fieldDerivedPullComp Λ c.i r.hom
  let kB := eqToIso (congrArg (fieldDerivedUpperStar Λ') r.i_hom.symm) ≪≫
    fieldDerivedPullComp Λ' c.i r.hom
  have hh := restriction_coefficient_mate
    (fieldDerivedAdjunction Λ r.hom) (fieldDerivedAdjunction Λ' r.hom)
    (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
    (fieldDerivedUpperStar Λ' c.i) (fieldDerivedUpperStar Λ' d.i)
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a d.Z)
    kA kB (CondensedRing.derivedPullIso a c.i).symm
    (CondensedRing.derivedPullIso a d.i).symm
    (CondensedRing.derivedPullIso a r.hom).symm (condensedPushScalar a r.hom)
    (proper_scalar_counit a r) (pull_scalar_comp a c.i r.hom d.i r.i_hom) M
  simp only [restrictionTransform, restrictionNat, kA, kB, Functor.comp_obj,
    Functor.comp_map, Category.assoc, Iso.symm_hom, Functor.map_comp] at hh ⊢
  exact_instance_congr hh

private theorem transform_mono {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Mono ((restrictionTransform (Λ := Λ) r).app
      ((fieldDerivedOpenShriek Λ c.i).obj K)) := by
  have hc := condensedOpen_restrictedCounit_isIso Λ r K
  have : IsIso ((fieldDerivedUpperStar Λ c.i).map
      ((fieldDerivedAdjunction Λ r.hom).counit.app
        ((fieldDerivedOpenShriek Λ c.i).obj K))) := hc
  dsimp only [restrictionTransform, restrictionNat]
  infer_instance

private theorem transform_normalization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
      (restrictionTransform (Λ := Λ) r).app
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj) =
      (fieldOpenAdjunction Λ c.i).unit.app K.obj := by
  exact_instance_congr (lift_normalization r K)

-- These proof-valued definitions retain the inferred instance arguments at each stage.
-- Explicit congruence supplies the proof arguments without expanding the localization.

private def scalar_lift_adjunctions {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (_r : c.Refinement d) :=
  coefficient_refinement_of_restriction
    (CA := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (DA := DerivedCategory (Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1})
      (condensedRingObj Λ c.Z)))
    (EA := DerivedCategory (Mod (Sheaf (ProEt.topology d.Z) Ab.{u + 1})
      (condensedRingObj Λ d.Z)))
    (CB := DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)))
    (DB := DerivedCategory (Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1})
      (condensedRingObj Λ' c.Z)))
    (EB := DerivedCategory (Mod (Sheaf (ProEt.topology d.Z) Ab.{u + 1})
      (condensedRingObj Λ' d.Z)))
    (fieldOpenAdjunction Λ c.i) (fieldOpenAdjunction Λ d.i)
    (fieldOpenAdjunction Λ' c.i) (fieldOpenAdjunction Λ' d.i)

private def scalar_lift_principle {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :=
  scalar_lift_adjunctions (Λ := Λ) (Λ' := Λ') r
    (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ' r.hom)
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a d.Z)
    (restrictionTransform (Λ := Λ) r) (restrictionTransform (Λ := Λ') r)
    (CondensedRing.derivedPullIso a c.i).symm
    (CondensedRing.derivedPullIso a d.i).symm (condensedPushScalar a r.hom)
    (fun M ↦ by exact_instance_congr (restriction_scalar_compat a r M))

private def open_scalar_components {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :=
  let K' : BoundedConstructible (condensedRingObj Λ' X) := ⟨_, hK⟩
  scalar_lift_principle a r
    K.obj (fieldProperOpen Λ r K) (fieldProperOpen Λ' r K')
    ((condensedOpenScalar a c.i).app K.obj) ((condensedOpenScalar a d.i).app K.obj)

private def open_scalar_refinement_raw {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :=
  let K' : BoundedConstructible (condensedRingObj Λ' X) := ⟨_, hK⟩
  open_scalar_components a r K hK
    (by exact_instance_congr (open_scalar_unit a c.i K.obj))
    (by exact_instance_congr (open_scalar_unit a d.i K.obj))
    (by exact_instance_congr (transform_normalization r K))
    (by exact_instance_congr (transform_normalization r K'))
    (hmono := by exact_instance_congr (transform_mono (Λ := Λ') r K'.obj))

private theorem open_scalar_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedScalar a d.Z).map (fieldProperOpen Λ r K) ≫
        (condensedPushScalar a r.hom).app
          ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
        (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor.map
          ((condensedOpenScalar a c.i).hom.app K.obj) =
      (condensedOpenScalar a d.i).hom.app K.obj ≫
        fieldProperOpen Λ' r ⟨(condensedScalar a X).obj K.obj, hK⟩ := by
  have h := open_scalar_refinement_raw a r K hK
  simp only [Iso.app_hom] at h
  exact_instance_congr h

private theorem open_scalar_refinement_map {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
      ((condensedScalar a d.Z).map (fieldProperOpen Λ r K) ≫
        (condensedPushScalar a r.hom).app
          ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
        (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor.map
          ((condensedOpenScalar a c.i).hom.app K.obj)) =
      (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
        ((condensedOpenScalar a d.i).hom.app K.obj) ≫
      (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
        (fieldProperOpen Λ' r ⟨(condensedScalar a X).obj K.obj, hK⟩) := by
  have h := congrArg ((CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map)
      (open_scalar_refinement a r K hK)
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem projection_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (condensedProjection a c).app K =
      (condensedPushScalar a c.g).app
          ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K) ≫
        (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor.map
          ((condensedOpenScalar a c.i).hom.app K) := by
  simp only [condensedProjection, pasteScalar, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id]

private theorem refinement_app_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldRefinement Λ r).app K = fieldRefinementApp Λ r K := rfl

private theorem refinementApp_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    fieldRefinementApp Λ r K = (fieldRefinementNat Λ r).app K := rfl

private theorem refinementNat_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    fieldRefinementNat Λ r = assembleLiftNat
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i)
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i)
      (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ d.g)
      (fieldDerivedLowerStar Λ c.g) (fieldProperOpenNat Λ r)
      ((fieldPushComp Λ r.hom d.g).hom ≫
        eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)) := rfl

private theorem properOpenNat_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldProperOpenNat Λ r).app K = fieldProperOpen Λ r K := rfl

private theorem assembleLiftNat_subcategory_app
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    (A : ObjectProperty C) (F : C ⥤ D) (G : C ⥤ E)
    (P : E ⥤ D) (R : D ⥤ H) (S : E ⥤ H)
    (lift : A.ι ⋙ F ⟶ (A.ι ⋙ G) ⋙ P) (cmp : P ⋙ R ⟶ S)
    (K : A.FullSubcategory) :
    (assembleLiftNat (A.ι ⋙ F) (A.ι ⋙ G) P R S lift cmp).app K =
      R.map (lift.app K) ≫ cmp.app (G.obj K.obj) := rfl

private theorem refinementNat_app_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldRefinementNat Λ r).app K = (assembleLiftNat
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i)
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i)
      (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ d.g)
      (fieldDerivedLowerStar Λ c.g) (fieldProperOpenNat Λ r)
      ((fieldPushComp Λ r.hom d.g).hom ≫
        eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g))).app K :=
  congrArg (fun t ↦ t.app K) (refinementNat_eq r)

private theorem assembled_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (assembleLiftNat
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i)
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i)
      (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ d.g)
      (fieldDerivedLowerStar Λ c.g) (fieldProperOpenNat Λ r)
      ((fieldPushComp Λ r.hom d.g).hom ≫
        eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g))).app K =
      (fieldDerivedLowerStar Λ d.g).map ((fieldProperOpenNat Λ r).app K) ≫
        ((fieldPushComp Λ r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K.obj) := by
  exact_instance_congr assembleLiftNat_subcategory_app
    (boundedConstructible (condensedRingObj Λ X))
    (fieldDerivedOpenShriek Λ d.i) (fieldDerivedOpenShriek Λ c.i)
    (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ d.g)
    (fieldDerivedLowerStar Λ c.g) (fieldProperOpenNat Λ r)
    ((fieldPushComp Λ r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)) K

private theorem lifted_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldDerivedLowerStar Λ d.g).map ((fieldProperOpenNat Λ r).app K) ≫
        ((fieldPushComp Λ r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K.obj) =
      (fieldDerivedLowerStar Λ d.g).map (fieldProperOpen Λ r K) ≫
        ((fieldPushComp Λ r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K.obj) :=
  congrArg (fun z ↦ (fieldDerivedLowerStar Λ d.g).map z ≫
    ((fieldPushComp Λ r.hom d.g).hom ≫
      eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)).app
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj)) (properOpenNat_app r K)

private theorem refinement_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldRefinement Λ r).app K =
      (fieldDerivedLowerStar Λ d.g).map (fieldProperOpen Λ r K) ≫
        ((fieldPushComp Λ r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ) r.hom_g)).app
            ((fieldDerivedOpenShriek Λ c.i).obj K.obj) := by
  exact (refinement_app_eq r K).trans ((refinementApp_eq r K).trans
    ((refinementNat_app_eq r K).trans ((assembled_component r K).trans
      (lifted_component r K))))

private theorem paste_components {C : Type*} [Category* C]
    {A B D E F : C} (p : A ⟶ B) (x : B ⟶ E) (y : B ⟶ D) (z : D ⟶ E)
    (t : E ⟶ F) (q : A ⟶ D) (r : D ⟶ F)
    (hx : x = y ≫ z) (hq : q = p ≫ y) (hr : r = z ≫ t) :
    p ≫ x ≫ t = q ≫ r := by
  rw [hx, hq, hr]
  simp only [Category.assoc]

/-- Pasting coefficient compatibility of the normalized proper/open lift.

Source: the proper/open coefficient mate argument of compact-support realization
Steps 15--16 (blueprint: lem-pur-condensed-proper-open-scalar).

Proof: compare the normalized lift after scalar extension with the normalized
lift for the scalar-extended bounded constructible object. Precompose the former
with the inverse open scalar comparison for `d.i` and transpose under the open
adjunction with coefficients `Λ'`. The open scalar mate equation carries the
original open unit to the new open unit. The proper scalar mate equation carries
the original proper counit to the new proper counit. Restriction of coefficients
commutes with the pullback composition comparison associated to `r.i_hom`.
Consequently the transpose, followed by `fieldProperOpenRestriction Λ' r`, is
the new open unit. Uniqueness of the normalized lift at
`⟨(condensedScalar a X).obj K.obj, hK⟩` identifies it with the chosen new lift.
Cancel the inverse open comparison. This proves that the three morphisms inside
the proper direct image in the displayed left side equal the open comparison
for `d.i` followed by the new normalized lift. Apply the proper direct image to
that equality, precompose with the proper scalar mate for `d.g`, and postcompose
with the specified target pushforward compositor. Functoriality separates the
two factors inside that image. The first resulting factor is the component of
`condensedProjection a d`; the second is the component of `fieldRefinement Λ' r`
at the scalar-extended object, by their definitions. Associativity gives the
claimed equality. No invertibility of a proper scalar comparison is assumed. -/
theorem fieldProperOpen_scalar_pasting {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedPushScalar a d.g).app
          ((CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj) ≫
        (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
          ((condensedScalar a d.Z).map (fieldProperOpen Λ r K) ≫
            (condensedPushScalar a r.hom).app
              ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
            (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor.map
              ((condensedOpenScalar a c.i).hom.app K.obj)) ≫
        ((fieldPushComp Λ' r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)).app
            ((CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory.obj
              ((condensedScalar a X).obj K.obj)) =
      (condensedProjection a d).app K.obj ≫
        (fieldRefinement Λ' r).app ⟨(condensedScalar a X).obj K.obj, hK⟩ := by
  let K' : BoundedConstructible (condensedRingObj Λ' X) := ⟨_, hK⟩
  let p := (condensedPushScalar a d.g).app
    ((CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj)
  let R := (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor
  let y := R.map ((condensedOpenScalar a d.i).hom.app K.obj)
  let z := R.map (fieldProperOpen Λ' r K')
  let t := ((fieldPushComp Λ' r.hom d.g).hom ≫
    eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)).app
      ((CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory.obj
        ((condensedScalar a X).obj K.obj))
  let q := (condensedProjection a d).app K.obj
  let r' := (fieldRefinement Λ' r).app K'
  have hq : q = p ≫ y := by
    exact_instance_congr (projection_component a d K.obj)
  have hr : r' = z ≫ t := by
    exact_instance_congr (refinement_component (Λ := Λ') r K')
  have h := paste_components p _ y z t q r'
    (open_scalar_refinement_map a r K hK) hq hr
  exact_instance_congr h

end WeilConjectures.CompactSupportCondensedRealization
