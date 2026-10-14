/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import Sheaf.AlgebraicGeometry.HigherDirectImageOverCoherence
import Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity
import Sheaf.AlgebraicGeometry.SmallEtaleAffineColimitDetection

/-! # Descent of base-change source images

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-source-image-limit-descent)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)

attribute [local irreducible] lowerStarPlusTransition upperStarComp
  Functor.mapDerivedCategoryPlusSingleFunctor upperStar lowerStar
  Functor.mapDerivedCategoryPlusHomologyFunctorIso

/-- Exact inverse image commutes with bounded-below homology. -/
private noncomputable def sourceSheafIso :
    (baseChangeSourceFunctor Λ p g q).obj F ≅
      ((p)^*[ModuleCat.{u + 1} Λ]).obj (higherDirectImage Λ g q F) :=
  ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app
    (R+((g)_*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm

private noncomputable abbrev sourceIso (U : Over T) :=
  sourceSheafIso Λ p (U.hom ≫ g) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)

omit [CommRing Λ] [IsAffine S] in
/-- Naturality transports two successive maps through a functor isomorphism. -/
private theorem conjugate_map_comp
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    (H : C₁ ⥤ C₂) (P : C₂ ⥤ C₄) (D : C₁ ⥤ C₃) (G : C₃ ⥤ C₄)
    (e : H ⋙ P ≅ D ⋙ G) {A B C : C₁} (m : A ⟶ B) (n : B ⟶ C) :
    G.map (D.map m) ≫ G.map (D.map n) =
      (e.inv.app A ≫ P.map (H.map m ≫ H.map n)) ≫ e.hom.app C := by
  rw [← G.map_comp, ← D.map_comp, ← H.map_comp]
  apply (Iso.comp_inv_eq (e.app C)).1
  exact e.inv.naturality (m ≫ n)

-- Construct this standard theorem application explicitly; Lean's kernel checks it.
private meta def sourceToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- Adapt the kernel-checked congruence method of HigherDirectImageOverMapCoefficient.
-- Build congruence proofs before reducing the large derived-category objects.
private meta def sourceCongrProofs
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := (← Lean.instantiateMVars a).consumeMData
      let b := (← Lean.instantiateMVars b).consumeMData
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' => e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← sourceCongrProofs cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← sourceCongrProofs cache pairs n type type'
          let htype ← sourceToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← sourceCongrProofs cache (pairs.push (x, y, hxy)) n
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
        return ← sourceCongrProofs cache pairs n a' b'
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        let unfoldFunctor (f : Lean.Expr) : Lean.MetaM Lean.Expr := do
          if f.isAppOf ``baseChangeSourceFunctor || f.isAppOf ``baseChangeTargetFunctor then
            return (← Lean.Meta.unfoldDefinition? f (ignoreTransparency := true)).getD f
          return f
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor ← unfoldFunctor args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        if e.isAppOf ``CategoryTheory.Functor.map && args.size ≥ 4 then
          let functor ← unfoldFunctor args[args.size - 4]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let f ← Lean.Meta.mkAppM ``CategoryTheory.Functor.map
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.map #[fs.back!, f]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← sourceCongrProofs cache pairs n a' b'
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
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
      if af != bf || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← sourceCongrProofs cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← sourceCongrProofs cache pairs n a b'
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
            return ← sourceCongrProofs cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← sourceCongrProofs cache pairs n a b'
        throwError "different congruence heads: {a} versus {b}"
      let mut first := 0
      while first < aa.size && aa[first]! == ba[first]! do
        first := first + 1
      let f := Lean.mkAppN af (aa.extract 0 first)
      let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
      let mut args := #[]
      for i in [first:aa.size] do
        let h ← sourceCongrProofs cache pairs n aa[i]! ba[i]!
        let h ← if ct.argKinds[i - first]! == .eq then
          sourceToEq h else pure h
        args := args.push aa[i]! |>.push ba[i]! |>.push h
      return Lean.mkAppN ct.proof args
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private meta def sourceStructuralExact
    (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target := (← Lean.Meta.whnf (← goal.getType)).consumeMData
    let some (_, lhs, rhs) := target.eq? | throwError "expected equality: {target}"
    let proofType ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
    let some (_, lhs', rhs') := proofType.consumeMData.eq?
      | throwError "expected equality proof: {proofType}"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let hl ← Lean.Meta.withTransparency .reducible (sourceCongrProofs cache #[] 200 lhs lhs')
    let hr ← Lean.Meta.withTransparency .reducible (sourceCongrProofs cache #[] 200 rhs' rhs)
    let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
    goal.assign (← sourceToEq hh)

set_option backward.isDefEq.respectTransparency true in
omit [IsAffine S] in
/-- Base change with coefficient comparison, conjugated by the homology isomorphism. -/
private theorem source_square_sheaf
    {T' Y Y' : Scheme.{u}} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p) (π : T' ⟶ T) (g' : T' ⟶ S) (w : π ≫ g = g')
    {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq' : IsPullback e' h' g' p)
    (a : Y' ⟶ Y) (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (G : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (α : (((π)^*[ModuleCat.{u + 1} Λ]).obj F) ⟶ G) :
    baseChangeHomologyMap Λ sq q F ≫
        baseChangeTargetTransition Λ e h q π a e' h' wa wh F ≫
        (baseChangeTargetFunctor Λ e' h' q).map α =
      (sourceSheafIso Λ p g q F).hom ≫
        ((p)^*[ModuleCat.{u + 1} Λ]).map
          (higherDirectImageTransition Λ π g g' w q F ≫
            (DerivedCategory.Plus.homologyFunctor _ q).map
              (R+((g')_*[ModuleCat.{u + 1} Λ]).map
                ((DerivedCategory.Plus.singleFunctor _ 0).map α))) ≫
        (sourceSheafIso Λ p g' q G).inv ≫
        baseChangeHomologyMap Λ sq' q G := by
  subst g'
  have result := conjugate_map_comp (DerivedCategory.Plus.homologyFunctor _ q)
    ((p)^*[ModuleCat.{u + 1} Λ]) D+((p)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.homologyFunctor _ q)
    (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q)
    (lowerStarPlusTransition Λ π g (π ≫ g) rfl
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))
    (R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map α))
  simp only [Category.assoc] at result
  have hconj : baseChangeSourceTransition Λ p g q π F ≫
      (baseChangeSourceFunctor Λ p (π ≫ g) q).map α =
    (sourceSheafIso Λ p g q F).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map
        (higherDirectImageTransition Λ π g (π ≫ g) rfl q F ≫
          (DerivedCategory.Plus.homologyFunctor _ q).map
            (R+((π ≫ g)_*[ModuleCat.{u + 1} Λ]).map
              ((DerivedCategory.Plus.singleFunctor _ 0).map α))) ≫
      (sourceSheafIso Λ p (π ≫ g) q G).inv := by
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let proof := (← Lean.Meta.getLocalDeclFromUserName `result).toExpr
        sourceStructuralExact proof
  rw [← Category.assoc,
    baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sq q π sq' a wa wh F,
    Category.assoc, baseChangeHomologyMap_naturality, ← Category.assoc, hconj]
  exact congrArg (fun f ↦ (sourceSheafIso Λ p g q F).hom ≫ f)
    (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency true in
omit [IsAffine S] in
/-- Apply the compatibility square to geometric stalks. -/
private theorem source_square {U V : Over T} (φ : U ⟶ V) :
    baseChangeStalkMap Λ p g q F x V ≫ baseChangeTargetStalkMap Λ p g q F x φ =
      (X.uliftPointSmallEtale x).sheafFiber.map
        ((sourceIso Λ p g q F V).hom ≫
          ((p)^*[ModuleCat.{u + 1} Λ]).map (higherDirectImageOverMap Λ g F q φ) ≫
          (sourceIso Λ p g q F U).inv) ≫ baseChangeStalkMap Λ p g q F x U := by
  simp only [baseChangeStalkMap, baseChangeTargetStalkMap, ← Functor.map_comp]
  congr 1
  exact source_square_sheaf Λ p (V.hom ≫ g) q
    (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
    (IsPullback.of_hasPullback (V.hom ≫ g) p) φ.left (U.hom ≫ g)
    (by rw [← Category.assoc, Over.w]) (IsPullback.of_hasPullback (U.hom ≫ g) p)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
    ((upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom (Over.w φ).symm).inv.app F)

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

set_option backward.isDefEq.respectTransparency true in
/-- The image under base change of a source element at the limit comes from a stage.

Source: Stacks Tag 09Z1, applied to the source side in Tag 0F07 condition (2).
(blueprint: lem-sbc-source-image-limit-descent)

Proof: The maps from the qcqs stages to the affine scheme S are qcqs. The limit is qcqs
and its projections are affine. Apply higher-direct-image continuity to the sheaves
pulled back from F on the stages, and then apply the exact inverse image along p and the
geometric stalk functor at x. These two left adjoints preserve colimits; inverse image
is exact and hence commutes with degree-q homology. Thus every element of the source
stalk at the limit is the restriction of a source element at some stage. In negative
degrees both source stalks vanish, so choose any stage and its zero element. Apply the
base-change map to a representative of the given element. Compatibility of base change
with restriction, followed by naturality for the inverse-image composition isomorphism,
identifies its restriction with the base-change image at the limit. This proves the
asserted equality; no injectivity or nonzero hypothesis is needed.
-/
theorem baseChange_source_image_limit_descent (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c))
    (η : baseChangeSourceStalk Λ p g q F x c.pt) :
    ∃ (i : I) (ηi : baseChangeSourceStalk Λ p g q F x (D.obj i)),
      (baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom
        ((baseChangeStalkMap Λ p g q F x (D.obj i)).hom ηi) =
          (baseChangeStalkMap Λ p g q F x c.pt).hom η := by
  classical
  let E := D ⋙ Over.forget T
  let cE := (Over.forget T).mapCone c
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f).left)
  have : ∀ i : I, CompactSpace (E.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit E cE hc
  let i₀ : I := Classical.choice (IsCofiltered.nonempty (C := I))
  have : IsAffineHom (c.π.app i₀).left := isAffineHom_π_app E cE hc i₀
  have : QuasiSeparatedSpace c.pt.left :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀).left
  have : ∀ i : I, QuasiCompact ((D.obj i).hom ≫ g) := fun i ↦ inferInstance
  have : ∀ i : I, QuasiSeparated ((D.obj i).hom ≫ g) := fun i ↦ inferInstance
  have : QuasiCompact (c.pt.hom ≫ g) := inferInstance
  have : QuasiSeparated (c.pt.hom ≫ g) := inferInstance
  let t := fun {U V : Over T} (φ : U ⟶ V) ↦ higherDirectImageOverMap Λ g F q φ
  obtain ⟨hid, hcomp⟩ := higher_image_over_transition_coherence Λ g F q
  let K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    { obj := fun i ↦ higherDirectImage Λ ((D.obj i.unop).hom ≫ g) q
        ((((D.obj i.unop).hom)^*[ModuleCat.{u + 1} Λ]).obj F)
      map := fun f ↦ t (D.map f.unop)
      map_id := fun i ↦ by
        change t (D.map (𝟙 i.unop)) = 𝟙 _
        rw [D.map_id]
        exact hid _
      map_comp := fun f h ↦ by
        change t (D.map (h.unop ≫ f.unop)) = t (D.map f.unop) ≫ t (D.map h.unop)
        rw [D.map_comp]
        exact hcomp _ _ }
  let B : Cocone K :=
    { pt := higherDirectImage Λ (c.pt.hom ≫ g) q
        (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
      ι :=
        { app := fun i ↦ t (c.π.app i.unop)
          naturality := fun i j f ↦ by
            change t (D.map f.unop) ≫ t (c.π.app j.unop) = t (c.π.app i.unop) ≫ 𝟙 _
            rw [← hcomp, c.w, Category.comp_id] } }
  have hB : Nonempty (IsColimit B) :=
    nonempty_isColimit_of_affine_etale Λ S K B (fun V ↦
      nonempty_isColimit_higher_image_affine Λ g F q D c hc K
        (fun _ ↦ Iso.refl _) (fun _ ↦ by
          simp only [K, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
          rfl)
        B (Iso.refl _) (fun _ ↦ by
          simp only [B, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
          exact (Category.comp_id _).symm) V)
  let L := (p)^*[ModuleCat.{u + 1} Λ] ⋙
    (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hC : IsColimit (L.mapCocone B) := isColimitOfPreserves L hB.some
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
      (forget (ModuleCat.{u + 1} Λ))
  let fiber := (X.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let ec := fiber.mapIso (sourceIso Λ p g q F c.pt)
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep (K ⋙ L) hC (ec.hom.hom η)
  let ei := fiber.mapIso (sourceIso Λ p g q F (D.obj i.unop))
  refine ⟨i.unop, ei.inv.hom y, ?_⟩
  have hs : (fiber.map ((sourceIso Λ p g q F (D.obj i.unop)).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map (t (c.π.app i.unop)) ≫
      (sourceIso Λ p g q F c.pt).inv)).hom (ei.inv.hom y) = η := by
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    change (fiber.map (sourceIso Λ p g q F c.pt).inv).hom
      ((L.map (t (c.π.app i.unop))).hom (ei.hom.hom (ei.inv.hom y))) = η
    have hei : ei.hom.hom (ei.inv.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
    rw [hei]
    change (L.map (t (c.π.app i.unop))).hom y = ec.hom.hom η at hy
    rw [hy]
    change ec.inv.hom (ec.hom.hom η) = η
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  have hw := congrArg (fun f ↦ f.hom (ei.inv.hom y))
    (source_square Λ p g q F x (c.π.app i.unop))
  dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
  change _ = (baseChangeStalkMap Λ p g q F x c.pt).hom
    ((fiber.map ((sourceIso Λ p g q F (D.obj i.unop)).hom ≫
      ((p)^*[ModuleCat.{u + 1} Λ]).map (t (c.π.app i.unop)) ≫
      (sourceIso Λ p g q F c.pt).inv)).hom (ei.inv.hom y)) at hw
  rw [hs] at hw
  exact hw

end AlgebraicGeometry.Etale
