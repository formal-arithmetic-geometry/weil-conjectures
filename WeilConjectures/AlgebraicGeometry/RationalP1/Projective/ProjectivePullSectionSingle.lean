/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Logic.Function.Basic
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

private theorem map_inverse_comp {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) {X Y Z W : C} (a : X ⟶ Y) (b : Y ⟶ X)
    (hb : a ≫ b = 𝟙 X) (p : X ⟶ Z) (q : Z ⟶ W) :
    S.map a ≫ S.map (b ≫ p ≫ q) = S.map p ≫ S.map q := by
  rw [← S.map_comp, ← Category.assoc a b, hb, Category.id_comp, S.map_comp]

private theorem section_single_of_comparisons {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) {A B I J : D} {X Y Z W : C}
    (m : A ≅ B) (u : B ⟶ I) (v : I ⟶ S.obj Y)
    (t : A ⟶ J) (i : J ⟶ S.obj W) (c : A ⟶ S.obj X) (d : J ⟶ S.obj Z)
    (b : X ≅ Y) (q : X ⟶ Z) (r : Z ⟶ W)
    (hm : m.hom ≫ u ≫ v = c ≫ S.map b.hom)
    (hi : i = d ≫ S.map r) (ht : t ≫ d = c ≫ S.map q) :
    m.inv ≫ t ≫ i = u ≫ v ≫ S.map (b.inv ≫ q ≫ r) := by
  rw [hi, reassoc_of% ht]
  apply m.inv_comp_eq.2
  symm
  rw [reassoc_of% hm]
  exact congrArg (fun a ↦ c ≫ a) (map_inverse_comp S b.hom b.inv b.hom_inv_id q r)

private theorem section_iso_component_of_comparisons
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {H F I : D ⥤ D} (m : H ≅ F) (t : H ≅ I) (i : I ≅ 𝟭 D)
    {H₀ F₀ I₀ : C ⥤ C} (b : H₀ ≅ F₀) (q : H₀ ≅ I₀) (r : I₀ ≅ 𝟭 C)
    (s : F ≅ 𝟭 D) (hs : s = m.symm ≪≫ t ≪≫ i)
    (M : C) {B : D} (u : F.obj (S.obj M) ⟶ B) (v : B ⟶ S.obj (F₀.obj M))
    (c : H.obj (S.obj M) ⟶ S.obj (H₀.obj M))
    (d : I.obj (S.obj M) ⟶ S.obj (I₀.obj M))
    (hm : m.hom.app (S.obj M) ≫ u ≫ v = c ≫ S.map (b.hom.app M))
    (hi : i.hom.app (S.obj M) = d ≫ S.map (r.hom.app M))
    (ht : t.hom.app (S.obj M) ≫ d = c ≫ S.map (q.hom.app M)) :
    s.hom.app (S.obj M) = u ≫ v ≫ S.map ((b.symm ≪≫ q ≪≫ r).hom.app M) := by
  rw [hs]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  exact section_single_of_comparisons S (m.app (S.obj M)) u v
    (t.hom.app (S.obj M)) (i.hom.app (S.obj M)) c d (b.app M)
    (q.hom.app M) (r.hom.app M) hm hi ht

private theorem comp_single_of_comparisons {C : Type*} [Category C]
    {A B C₁ D E : C} (n : A ⟶ B) (m : B ⟶ C₁) (u : C₁ ⟶ D) (v : D ⟶ E)
    (c : B ⟶ E) (r : A ⟶ E) (hm : m ≫ u ≫ v = c) (hn : n ≫ c = r) :
    (n ≫ m) ≫ u ≫ v = r := by
  rw [Category.assoc, hm, hn]

private theorem leftDerived_id_single (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 C) (M : C) :
    (Functor.leftDerivedFunctorIdIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
      F.singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  change (Functor.leftDerivedFunctorNatIso F e).hom.app
      ((DerivedCategory.singleFunctor C 0).obj M) ≫
    (𝟭 C).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      ((DerivedCategory.singleFunctor C 0).obj M) ≫
    (Functor.mapDerivedCategoryIdIso C).hom.app
      ((DerivedCategory.singleFunctor C 0).obj M) = _
  rw [SheafExactDegreeZero.derived_id_single]
  exact Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj F (𝟭 C) e M

private theorem pull_id_single (Y : Scheme.{u})
    (M : Modules Λ (ProjectiveLine Y)) :
    (CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y)).hom.app
      ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y)))).hom.app M ≫
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        ((CondensedRing.upperStarId Λ (ProjectiveLine Y)).hom.app M) := by
  exact leftDerived_id_single (CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y)))
    (CondensedRing.upperStarId Λ (ProjectiveLine Y)) M

private theorem pull_transport_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (eqToIso (congrArg
        (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h)).hom.app
      ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) ≫
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y)))).hom.app M =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y ≫ f))).hom.app M ≫
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        ((CondensedRing.upperStarCongr Λ h).hom.app M) := by
  generalize diagonalImmersion Y ≫ f = g at h ⊢
  cases h
  simp only [CondensedRing.upperStarCongr, Functor.comp_obj, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app]
  rw [(DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map_id
    ((CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y))).obj M), Category.comp_id]
  exact Category.id_comp
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y)))).hom.app M)

private theorem pull_comp_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (M : Modules Λ (ProjectiveLine Y)) :
    (CondensedRing.leftDerivedUpperStarComp Λ
        (diagonalImmersion Y) f).hom.app
      ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) ≫
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
        ((Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar Λ f)).hom.app M) ≫
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
          ((CondensedRing.upperStar Λ f).obj M) =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y ≫ f))).hom.app M ≫
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        ((CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).hom.app M) := by
  have hc := Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ (diagonalImmersion Y)) M
  have hn := Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar Λ (diagonalImmersion Y ≫ f))
    (CondensedRing.upperStar Λ f ⋙ CondensedRing.upperStar Λ (diagonalImmersion Y))
    (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f) M
  exact comp_single_of_comparisons _ _ _ _ _ _ hc hn

private theorem section_diagonal_abelian_eq (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian X =
      (CategoryTheory.sheafIsAbelian :
        Abelian (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) := by
  rfl

private theorem sectionPiEq {α β : Sort u} {P : α → Sort v}
    {Q : β → Sort v} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

private theorem section_shrink_congr {α β : Type v} (h : α = β)
    [Small.{u} α] [Small.{u} β] : Shrink.{u} α = Shrink.{u} β := by
  cases h
  rfl

private theorem section_cast_heq {α β : Sort v} (h : α = β) (a : α) :
    HEq (Eq.mp h a) a := by
  cases h
  rfl

private meta structure SectionCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

/-- Equality of the types identifies choice values by proof irrelevance. -/
private theorem section_choice_heq {α β : Sort u} (h : α = β)
    (ha : Nonempty α) (hb : Nonempty β) :
    HEq (Classical.choice ha) (Classical.choice hb) := by
  cases h
  rfl

/-- Compare dependent functions at a shared argument before transporting the family. -/
private theorem section_pointwise_heq {α : Sort u} {P Q : α → Sort v}
    {f : ∀ x, P x} {g : ∀ x, Q x} (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  have hPQ : P = Q := funext (fun x ↦ type_eq_of_heq (h x))
  cases hPQ
  exact heq_of_eq (funext (fun x ↦ eq_of_heq (h x)))

private meta def shareSectionProof (lhs rhs h : Expr) : MetaM Expr := do
  let mut val ← instantiateMVars h
  let mut ty ← mkHEq lhs rhs
  let mut used := (collectFVars (collectFVars {} val) ty).fvarIds
  let mut xs := #[]
  for decl in (← getLCtx).decls.toArray.reverse do
    if let some decl := decl then
      if used.contains decl.fvarId then
        xs := #[decl.toExpr] ++ xs
        used := used ++ (collectFVars {} decl.type).fvarIds
        if let some value := decl.value? then
          used := used ++ (collectFVars {} value).fvarIds
  let mut args := #[]
  for x in xs do
    if !(← x.fvarId!.getDecl).isLet then args := args.push x
  for x in xs.reverse do
    let decl ← x.fvarId!.getDecl
    let domain ← instantiateMVars decl.type
    let vb := val.abstract #[x]
    let tb := ty.abstract #[x]
    if let some value := decl.value? then
      let value ← instantiateMVars value
      val := .letE decl.userName domain value vb false
      ty := .letE decl.userName domain value tb false
    else
      val := .lam decl.userName domain vb decl.binderInfo
      ty := .forallE decl.userName domain tb decl.binderInfo
  val ← instantiateMVars val
  ty ← instantiateMVars ty
  if val.hasExprMVar || ty.hasExprMVar then
    throwError "unresolved native auxiliary metavariable"
  let levels := (collectLevelParams (collectLevelParams {} val) ty).params.toList
  let name ← try mkAuxLemma levels ty val
    catch err => throwError "native auxiliary for {lhs.getAppFn}: {err.toMessageData}"
  return mkAppN (mkConst name (levels.map Level.param)) args

-- Build heterogeneous congruence proofs across the existing category-instance aliases.
-- Each auxiliary proof is kernel checked; choice uses proof irrelevance at equal types.

private meta def sectionNativeHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT SectionCongrState MetaM Expr := do
  match fuel with
  | 0 => throwError "native congruence exhausted: {lhs}\n{rhs}"
  | next + 1 =>
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs == rhs then return ← mkHEqRefl lhs
    for (a, b, h) in (← get).proofs do
      if a == lhs && b == rhs then return h
    let prove : StateRefT SectionCongrState MetaM Expr := do
      if lhs.isAppOfArity ``Shrink 2 && rhs.isAppOfArity ``Shrink 2 then
        let xs := lhs.getAppArgs
        let ys := rhs.getAppArgs
        let h ← mkEqOfHEq (← sectionNativeHEq xs[0]! ys[0]! next)
        let h ← mkAppOptM ``section_shrink_congr
          #[some xs[0]!, some ys[0]!, some h, some xs[1]!, some ys[1]!]
        return ← mkHEqOfEq h
      if lhs.isAppOfArity ``Eq.mp 4 then
        let args := lhs.getAppArgs
        let h₁ ← mkAppM ``section_cast_heq #[args[2]!, args[3]!]
        let h₂ ← sectionNativeHEq args[3]! rhs next
        return ← mkAppM ``HEq.trans #[h₁, h₂]
      if rhs.isAppOfArity ``Eq.mp 4 then
        let args := rhs.getAppArgs
        let h₁ ← sectionNativeHEq lhs args[3]! next
        let h₂ ← mkAppM ``section_cast_heq #[args[2]!, args[3]!]
        return ← mkAppM ``HEq.trans #[h₁, ← mkAppM ``HEq.symm #[h₂]]
      let isSectionAlias (e : Expr) : Bool :=
        e.isAppOf ``AlgebraicGeometry.ProEtale.DiagonalCoefficients.Modules ||
          e.isAppOf ``CondensedRing.moduleObjectDerivedPullback ||
          e.isAppOf ``GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
      if isSectionAlias lhs then
        if let some lhs' ← withTransparency .all (unfoldDefinition? lhs) then
          return ← sectionNativeHEq lhs' rhs next
      if isSectionAlias rhs then
        if let some rhs' ← withTransparency .all (unfoldDefinition? rhs) then
          return ← sectionNativeHEq lhs rhs' next
      if lhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          rhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        return ← mkHEqOfEq (← mkAppM ``section_diagonal_abelian_eq #[lhs.getAppArgs[0]!])
      if rhs.isAppOf ``AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian &&
          lhs.isAppOf ``CategoryTheory.sheafIsAbelian then
        let he ← mkAppM ``section_diagonal_abelian_eq #[rhs.getAppArgs[0]!]
        return ← mkHEqOfEq (← mkAppM ``Eq.symm #[he])
      if (← isProof lhs) && (← isProof rhs) then
        return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let lhsType ← whnf (← inferType lhs)
      let rhsType ← whnf (← inferType rhs)
      if lhsType.isForall && rhsType.isForall &&
          lhsType.bindingBody!.isAppOf ``Invertible &&
          rhsType.bindingBody!.isAppOf ``Invertible then
        if lhsType == rhsType then
          return ← mkHEqOfEq (← mkAppM ``Subsingleton.elim #[lhs, rhs])
      if lhs.isAppOfArity ``Classical.choice 2 && rhs.isAppOfArity ``Classical.choice 2 then
        let xs := lhs.getAppArgs
        let ys := rhs.getAppArgs
        let ht ← mkEqOfHEq (← sectionNativeHEq xs[0]! ys[0]! next)
        return ← mkAppM ``section_choice_heq #[ht, xs[1]!, ys[1]!]
      match lhs, rhs with
      | .lam n α body _, .lam _ β body' _ =>
        if α == β then
          let init ← get
          let hfun ← withLocalDeclD n α fun x => do
            let h ← sectionNativeHEq (body.instantiate1 x) (body'.instantiate1 x) next
            mkLambdaFVars #[x] h
          let congrs := (← get).congrs
          set { init with congrs := congrs }
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          let P := mkLambda n .default α ty.bindingBody!
          let Q := mkLambda n .default α ty'.bindingBody!
          return ← mkAppOptM ``section_pointwise_heq #[some α, some P, some Q,
            some lhs, some rhs, some hfun]
        let hα ← mkEqOfHEq (← sectionNativeHEq α β next)
        let init ← get
        let hfun ← withLocalDeclD n α fun x =>
          withLocalDeclD (n.appendAfter "'") β fun y => do
          withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
            modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
            let h ← sectionNativeHEq (body.instantiate1 x) (body'.instantiate1 y) next
            mkLambdaFVars #[x, y, hxy] h
        let congrs := (← get).congrs
        set { init with congrs := congrs }
        let ty ← whnf (← inferType lhs)
        let ty' ← whnf (← inferType rhs)
        let P := mkLambda n .default α ty.bindingBody!
        let Q := mkLambda n .default β ty'.bindingBody!
        return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
          some lhs, some rhs, some hα, some hfun]
      | .forallE n α body _, .forallE _ β body' _ =>
        let hα ← mkEqOfHEq (← sectionNativeHEq α β next)
        let P := mkLambda n .default α body
        let Q := mkLambda n .default β body'
        let hPQ ← sectionNativeHEq P Q next
        let h ← mkAppOptM ``sectionPiEq #[some α, some β, some P, some Q,
          some hα, some hPQ]
        return ← mkHEqOfEq h
      | _, _ => pure ()
      let expandProjection (e : Expr) : MetaM Expr := do
        let .proj typeName index major := e.getAppFn | return e
        let info := Lean.getStructureInfo (← getEnv) typeName
        let p ← mkProjection major info.fieldNames[index]!
        return mkAppN p e.getAppArgs
      let lhs' ← expandProjection lhs
      let rhs' ← expandProjection rhs
      if lhs' != lhs || rhs' != rhs then
        return ← sectionNativeHEq lhs' rhs' next
      let reduceFunctorProjection (e : Expr) : MetaM Expr := do
        if e.isAppOf ``Functor.obj || e.isAppOf ``Functor.map then
          let args := e.getAppArgs
          if args.size > 4 then
            let F := args[4]!
            if F.isAppOf ``Functor.comp || F.isAppOf ``Functor.id then
              return ← whnf e
        return e
      let lhs' ← reduceFunctorProjection lhs
      let rhs' ← reduceFunctorProjection rhs
      if lhs' != lhs || rhs' != rhs then
        return ← sectionNativeHEq lhs' rhs' next
      let mut f := lhs.getAppFn
      let mut g := rhs.getAppFn
      let mut xs := lhs.getAppArgs
      let mut ys := rhs.getAppArgs
      if f == g && xs.size == ys.size then
        let mut same := 0
        while same < xs.size && xs[same]! == ys[same]! do
          same := same + 1
        f := mkAppN f (xs.extract 0 same)
        g := mkAppN g (ys.extract 0 same)
        xs := xs.extract same xs.size
        ys := ys.extract same ys.size
      if f == g && xs.size == ys.size && !xs.isEmpty then
        let before ← get
        try
          let mut found := none
          for (ff, arity, thm) in (← get).congrs do
            if ff == f && arity == xs.size then found := some thm
          let thm? ← match found with
            | some thm => pure (some thm)
            | none => do
              let optimized? ← if let .const name levels := f then
                mkHCongrWithArityForConst? name levels xs.size
              else pure none
              let thm? ← match optimized? with
                | some thm => pure (some thm)
                | none =>
                  try pure (some (← mkHCongrWithArity f xs.size))
                  catch _ => pure none
              if let some thm := thm? then
                modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
              pure thm?
          if let some thm := thm? then
            let mut args := #[]
            for i in [:xs.size] do
              let h ← sectionNativeHEq xs[i]! ys[i]! next
              let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
              args := args ++ #[xs[i]!, ys[i]!, h]
            let h := mkAppN thm.proof args
            let ty ← inferType h
            if ty.isHEq then return h else return ← mkHEqOfEq h
          else
            let ty ← whnf (← inferType lhs)
            let ty' ← whnf (← inferType rhs)
            if ty.isForall && ty'.isForall then
              let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
                (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
              let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
                (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
              return ← sectionNativeHEq lhs' rhs' next
        catch _ => set before
      let lhs' ← whnf lhs
      let rhs' ← whnf rhs
      if lhs' != lhs || rhs' != rhs then
        return ← sectionNativeHEq lhs' rhs' next
      let lhs' := (← unfoldDefinition? lhs).getD lhs
      let rhs' := (← unfoldDefinition? rhs).getD rhs
      if lhs' != lhs || rhs' != rhs then
        return ← sectionNativeHEq lhs' rhs' next
      throwError "coefficient congruence stuck:
  {lhs}
  {rhs}"
    let h ← prove
    let h ← shareSectionProof lhs rhs h
    modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
    return h

private meta def sectionCheckApplication (e : Expr) :
    StateRefT SectionCongrState MetaM Expr := do
  let mut f := e.getAppFn
  let args := e.getAppArgs
  for i in [:args.size] do
    let arg := args[i]!
    let ty ← whnf (← inferType f)
    let .forallE _ domain _ _ := ty | throwError "section application is not a function"
    let actual ← inferType arg
    let arg ← if actual == domain || !(← isProof arg) then pure arg else do
      let h ← try sectionNativeHEq actual domain
        catch err => throwError "assembly argument {i}: {err.toMessageData}"
      mkAppM ``Eq.mp #[← mkEqOfHEq h, arg]
    f := mkApp f arg
  return f

-- Keep the published comparison data folded in the final specialization.

/--
The single-complex component of the derived pullback section is the ordinary
section map conjugated by the two left-derived single comparisons.
Source: the second identity proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md`.
The proof combines the published left-derived single composition and naturality
formulas with the identity normalization and equality transport, then cancels the
ordinary compositor. The identity normalization uses `mapDerivedCategoryIdIso_factorsh`.
(blueprint: lem-route-projective-pull-section-single)
-/
theorem projective_pull_section_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (pullSectionIso Λ Y f h).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) =
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
        ((CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar Λ f)).hom.app M) ≫
      (CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        (((CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
          CondensedRing.upperStarCongr Λ h ≪≫
          CondensedRing.upperStarId Λ (ProjectiveLine Y)).hom.app M) := by
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term
          r#"section_iso_component_of_comparisons
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0)
    (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f)
    (eqToIso (congrArg
      (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h))
    (CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y))
    (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f)
    (CondensedRing.upperStarCongr Λ h)
    (CondensedRing.upperStarId Λ (ProjectiveLine Y))
    (pullSectionIso Λ Y f h) (pullSectionIso_eq Λ Y f h) M
    ((CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
      ((Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ f)).hom.app M))
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
        ((CondensedRing.upperStar Λ f).obj M))
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar Λ (diagonalImmersion Y ≫ f))).hom.app M)
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar Λ (𝟙 (ProjectiveLine Y)))).hom.app M)
    (pull_comp_single Λ Y f M) (pull_id_single Λ Y M)
    (pull_transport_single Λ Y f h M)"# with
        | .ok parsed => pure parsed
        | .error message => Lean.throwError "{message}"
      let raw ← Lean.Elab.Term.elabTerm parsed none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let raw ← Lean.instantiateMVars raw
      let (result, st) ← (sectionCheckApplication raw).run {}
      let lhs ← Lean.Meta.inferType result
      let rhs ← Lean.Elab.Tactic.getMainTarget
      let (proof, _) ← (sectionNativeHEq lhs rhs).run st
      let eqProof ← Lean.Meta.mkEqOfHEq proof
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[eqProof, result])
      Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.RationalP1
