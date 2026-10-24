/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyExchange
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.WeilObject.BoundedConstructible.Homology
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison

/-!

# Homology sheaves of the pushforward of Weil objects along a finite morphism

Let `f : X ⟶ Y` be a finite morphism over `Spec k` with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`. The pushforward `f_*` of module objects is exact
(`ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite`), so the derived
pushforward `Rf_*` commutes with the homology sheaves: `Hⁿ(Rf_* K) ≅ f_* Hⁿ(K)`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarHomologyIso`). On the homology sheaves, the
derived base-change morphism of the Frobenius square is the base-change morphism of module objects
(`CategoryTheory.Adjunction.homologyFunctor_map_exchangeRight_derivedAdjunction`), so this
isomorphism is compatible with the Weil structures: for a Weil object `K` for `e_X`,
`Hⁿ(Rf_*^Weil K) ≅ f_* Hⁿ(K)` as Weil sheaves for `e_Y`
(`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerStar_iso_of_isFinite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Squares of left derived functors of exact functors -/

section Diag
open Lean Meta Elab Tactic

meta partial def findDiffAux (a b : Expr) (acc : IO.Ref (Array (Expr × Expr))) (fuel : Nat := 30)
    (path : List String := []) : MetaM Unit := do
  if a == b then return
  if (← acc.get).size ≥ 8 then return
  if (← isProof a) && (← isProof b) then return
  let unfoldStep : MetaM Unit := do
    let a' ← whnfR a
    let b' ← whnfR b
    if a' != a || b' != b then return ← findDiffAux a' b' acc fuel path
    if fuel = 0 then acc.modify (·.push (a, b)); logInfo m!"PATH {path}"; return
    let ha := match a.getAppFn with | .const n _ => some n | _ => none
    let hb := match b.getAppFn with | .const n _ => some n | _ => none
    -- unfold the side whose head is a definition with the larger height
    let env ← getEnv
    let height (n? : Option Name) : Nat := match n? with
      | some n => match env.find? n with
        | some (.defnInfo d) => match d.hints with | .regular h => h.toNat + 1 | .abbrev => 1000 | _ => 0
        | _ => 0
      | none => 0
    let (ua, ub) := if height ha ≥ height hb then (true, false) else (false, true)
    if ua then
      if let some a' ← unfoldDefinition? a then
        logInfo m!"unfold KEY head {ha}"
        return ← findDiffAux a' b acc (fuel - 1) path
    if ub || !ua then
      if let some b' ← unfoldDefinition? b then
        logInfo m!"unfold GOAL head {hb}"
        return ← findDiffAux a b' acc (fuel - 1) path
    logInfo m!"PATH {path}"
    acc.modify (·.push (a, b))
  match a, b with
  | .app f₁ x₁, .app f₂ x₂ =>
      if f₁.getAppNumArgs == f₂.getAppNumArgs && f₁.getAppFn == f₂.getAppFn then
        let hd := toString f₁.getAppFn.constName?
        findDiffAux f₁ f₂ acc fuel path
        findDiffAux x₁ x₂ acc fuel ((hd ++ "#" ++ toString f₁.getAppNumArgs) :: path)
      else unfoldStep
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ =>
      findDiffAux t₁ t₂ acc fuel
      withLocalDeclD `x t₁ fun x ↦ findDiffAux (b₁.instantiate1 x) (b₂.instantiate1 x) acc fuel
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ =>
      findDiffAux t₁ t₂ acc fuel
      withLocalDeclD `x t₁ fun x ↦ findDiffAux (b₁.instantiate1 x) (b₂.instantiate1 x) acc fuel
  | .mdata _ e, _ => findDiffAux e b acc fuel
  | _, .mdata _ e => findDiffAux a e acc fuel
  | .proj _ i₁ e₁, .proj _ i₂ e₂ =>
      if i₁ == i₂ then findDiffAux e₁ e₂ acc fuel else acc.modify (·.push (a, b))
  | _, _ => unfoldStep

elab "find_diff " h:ident : tactic => withMainContext do
  let goal ← getMainTarget
  let lctx ← getLCtx
  let some d := lctx.findFromUserName? h.getId | throwError "no"
  let t ← instantiateMVars d.type
  let g ← instantiateMVars goal
  let acc ← IO.mkRef #[]
  findDiffAux t g acc
  for (a, b) in ← acc.get do
    logInfo m!"KEY: {a}\n=====\nGOAL: {b}"

elab "find_diff_terms " a:term " , " b:term : tactic => withMainContext do
  let a ← instantiateMVars (← Elab.Term.elabTerm a none)
  let b ← instantiateMVars (← Elab.Term.elabTerm b none)
  let acc ← IO.mkRef #[]
  findDiffAux a b acc
  for (a, b) in ← acc.get do
    logInfo m!"A: {a}\n=====\nB: {b}"

elab "diff_rhs " h:ident " , " t:term : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let y := ty.appArg!
  let b ← instantiateMVars (← Elab.Term.elabTerm t none)
  let acc ← IO.mkRef #[]
  findDiffAux y b acc
  for (a, b) in ← acc.get do
    logInfo m!"A: {a}\n=====\nB: {b}"

elab "diff_goal_inst " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let g ← instantiateMVars (← getMainTarget)
  let g := g.appArg!
  logInfo m!"I2INST: {ty.appFn!.appFn!.appArg!}"
  logInfo m!"GOALINST: {g.appFn!.appFn!.appArg!}"

end Diag

namespace CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  [MonoidalCategory D₁] [MonoidalPreadditive D₁] [HasCountableCoproducts D₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D₁] [HasExactColimitsOfShape ℤ D₁]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).obj X)]
  [∀ (X : D₁), PreservesColimitsOfShape ℤ ((curriedTensor D₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D₁]
  {u : C₁ ⥤ C₂} {f₂ : C₂ ⥤ D₂} {f₁ : C₁ ⥤ D₁} {v : D₁ ⥤ D₂} {W₁ W₂ : C₁ ⥤ D₂}
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  [W₁.Additive] [PreservesFiniteLimits W₁] [PreservesFiniteColimits W₁]
  [W₂.Additive] [PreservesFiniteLimits W₂] [PreservesFiniteColimits W₂]

/-- The isomorphism `Lu ⋙ Lf₂ ≅ Lf₁ ⋙ Lv` of total left derived functors of exact functors
induced by isomorphisms `c₁ : W₁ ≅ u ⋙ f₂`, `c₂ : W₂ ≅ f₁ ⋙ v` and an equation `W₁ = W₂`,
through the composition isomorphisms `Functor.leftDerivedFunctorCompIso`. -/
noncomputable def leftDerivedFunctorSquareIso (c₁ : W₁ ≅ u ⋙ f₂) (h : W₁ = W₂)
    (c₂ : W₂ ≅ f₁ ⋙ v) :
    u.leftDerivedFunctor ⋙ f₂.leftDerivedFunctor ≅ f₁.leftDerivedFunctor ⋙ v.leftDerivedFunctor :=
  (W₁.leftDerivedFunctorNatIso c₁ ≪≫ u.leftDerivedFunctorCompIso f₂).symm ≪≫
    W₁.leftDerivedFunctorNatIso (eqToIso h) ≪≫
      (W₂.leftDerivedFunctorNatIso c₂ ≪≫ f₁.leftDerivedFunctorCompIso v)

/-- Through the identifications of the total left derived functors of exact functors with the
functors they induce on derived categories, `leftDerivedFunctorSquareIso c₁ h c₂` is the
isomorphism `D(u) ⋙ D(f₂) ≅ D(f₁) ⋙ D(v)` induced by `c₁⁻¹ ≫ h ≫ c₂`. -/
lemma leftDerivedFunctorSquareIso_hom_app (c₁ : W₁ ≅ u ⋙ f₂) (h : W₁ = W₂)
    (c₂ : W₂ ≅ f₁ ⋙ v) (K : DerivedCategory C₁) :
    f₂.mapDerivedCategory.map (u.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        f₂.leftDerivedFunctorIsoMapDerivedCategory.inv.app (u.leftDerivedFunctor.obj K) ≫
          (leftDerivedFunctorSquareIso c₁ h c₂).hom.app K =
      (mapDerivedCategorySquareIso (c₁.symm ≪≫ eqToIso h ≪≫ c₂)).hom.app K ≫
        v.mapDerivedCategory.map (f₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
          v.leftDerivedFunctorIsoMapDerivedCategory.inv.app (f₁.leftDerivedFunctor.obj K) := by
  simp [leftDerivedFunctorSquareIso, leftDerivedFunctorNatIso, leftDerivedFunctorCompIso,
    mapDerivedCategoryNatIso_trans, mapDerivedCategoryNatIso_symm]

/-- The components of `leftDerivedFunctorSquareIso`. -/
lemma leftDerivedFunctorSquareIso_hom_app_eq (c₁ : W₁ ≅ u ⋙ f₂) (h : W₁ = W₂)
    (c₂ : W₂ ≅ f₁ ⋙ v) (K : DerivedCategory C₁) :
    (leftDerivedFunctorSquareIso c₁ h c₂).hom.app K =
      (W₁.leftDerivedFunctorNatIso c₁ ≪≫ u.leftDerivedFunctorCompIso f₂).inv.app K ≫
        eqToHom (by subst h; rfl) ≫
          (W₂.leftDerivedFunctorNatIso c₂ ≪≫ f₁.leftDerivedFunctorCompIso v).hom.app K := by
  rw [leftDerivedFunctorSquareIso, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_hom, leftDerivedFunctorNatIso_eqToIso_hom_app]

end CategoryTheory.Functor

/-! ### Transport of algebras along functors commuting with the structures -/

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {𝒟X 𝒟Y 𝒜X 𝒜Y : Type*} {_ : Category 𝒟X} {_ : Category 𝒟Y} {_ : Category 𝒜X}
  {_ : Category 𝒜Y}
  {LX : 𝒟X ⥤ 𝒟X} {LY : 𝒟Y ⥤ 𝒟Y} {PX : 𝒜X ⥤ 𝒜X} {PY : 𝒜Y ⥤ 𝒜Y} {R : 𝒟X ⥤ 𝒟Y}
  {S : 𝒜X ⥤ 𝒜Y} {HX : 𝒟X ⥤ 𝒜X} {HY : 𝒟Y ⥤ 𝒜Y}

/-- Let `R` and `S` transport algebras along `b` and `bc`, and `H_X`, `H_Y` along `θ_X`, `θ_Y`.
An isomorphism `ψ : R ⋙ H_Y ≅ H_X ⋙ S` compatible with these commutation isomorphisms induces an
isomorphism `H_Y (R K) ≅ S (H_X K)` of algebras. -/
theorem nonempty_mapOfNatIso_obj_mapOfNatIso_obj_iso (b : R ⋙ LY ≅ LX ⋙ R)
    (bc : S ⋙ PY ≅ PX ⋙ S) (θX : HX ⋙ PX ≅ LX ⋙ HX) (θY : HY ⋙ PY ≅ LY ⋙ HY)
    (ψ : R ⋙ HY ≅ HX ⋙ S)
    (h : ∀ K, PY.map (ψ.hom.app K) ≫ bc.hom.app (HX.obj K) ≫ S.map (θX.hom.app K) =
      θY.hom.app (R.obj K) ≫ HY.map (b.hom.app K) ≫ ψ.hom.app (LX.obj K))
    (K : IsoAlgebra LX) :
    Nonempty ((mapOfNatIso θY).obj ((mapOfNatIso b).obj K) ≅
      (mapOfNatIso bc).obj ((mapOfNatIso θX).obj K)) := by
  refine ⟨isoMk (ψ.app K.carrier) ?_⟩
  change PY.map (ψ.hom.app K.carrier) ≫
      (bc.hom.app (HX.obj K.carrier) ≫ S.map (θX.hom.app K.carrier ≫ HX.map K.str.hom)) =
    (θY.hom.app (R.obj K.carrier) ≫ HY.map (b.hom.app K.carrier ≫ R.map K.str.hom)) ≫
      ψ.hom.app K.carrier
  have nat := ψ.hom.naturality K.str.hom
  simp only [Functor.comp_map] at nat
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (h K.carrier), nat]


/-- The isomorphism of `nonempty_mapOfNatIso_obj_mapOfNatIso_obj_iso`, as a natural isomorphism
of functors `IsoAlgebra LX ⥤ IsoAlgebra PY`. -/
theorem nonempty_mapOfNatIso_comp_mapOfNatIso_iso (b : R ⋙ LY ≅ LX ⋙ R)
    (bc : S ⋙ PY ≅ PX ⋙ S) (θX : HX ⋙ PX ≅ LX ⋙ HX) (θY : HY ⋙ PY ≅ LY ⋙ HY)
    (ψ : R ⋙ HY ≅ HX ⋙ S)
    (h : ∀ K, PY.map (ψ.hom.app K) ≫ bc.hom.app (HX.obj K) ≫ S.map (θX.hom.app K) =
      θY.hom.app (R.obj K) ≫ HY.map (b.hom.app K) ≫ ψ.hom.app (LX.obj K)) :
    Nonempty (mapOfNatIso b ⋙ mapOfNatIso θY ≅ mapOfNatIso θX ⋙ mapOfNatIso bc) := by
  refine ⟨NatIso.ofComponents (fun K ↦ isoMk (ψ.app K.carrier) ?_) fun φ ↦ ?_⟩
  · change PY.map (ψ.hom.app K.carrier) ≫
        (bc.hom.app (HX.obj K.carrier) ≫ S.map (θX.hom.app K.carrier ≫ HX.map K.str.hom)) =
      (θY.hom.app (R.obj K.carrier) ≫ HY.map (b.hom.app K.carrier ≫ R.map K.str.hom)) ≫
        ψ.hom.app K.carrier
    have nat := ψ.hom.naturality K.str.hom
    simp only [Functor.comp_map] at nat
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (h K.carrier), nat]
  · ext
    exact ψ.hom.naturality φ.hom.f
end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Adjunction

variable {𝒜 ℬ 𝒜₂ ℬ₂ : Type*} [Category 𝒜] [Category ℬ] [Category 𝒜₂] [Category ℬ₂]
  {P : ObjectProperty ℬ} {Q : ObjectProperty 𝒜} {P₂ : ObjectProperty ℬ₂}
  {Q₂ : ObjectProperty 𝒜₂} {L' : ℬ ⥤ 𝒜} {R' : 𝒜 ⥤ ℬ} {L₂' : ℬ₂ ⥤ 𝒜₂} {R₂' : 𝒜₂ ⥤ ℬ₂}
  (adj : L' ⊣ R') (adj₂ : L₂' ⊣ R₂') {G' : ℬ ⥤ ℬ₂} {H' : 𝒜 ⥤ 𝒜₂} (θ' : G' ⋙ L₂' ≅ L' ⋙ H')
  {hL : ∀ X : P.FullSubcategory, Q ((P.ι ⋙ L').obj X)}
  {hR : ∀ X : Q.FullSubcategory, P ((Q.ι ⋙ R').obj X)}
  {hL₂ : ∀ X : P₂.FullSubcategory, Q₂ ((P₂.ι ⋙ L₂').obj X)}
  {hR₂ : ∀ X : Q₂.FullSubcategory, P₂ ((Q₂.ι ⋙ R₂').obj X)}
  {hG : ∀ X : P.FullSubcategory, P₂ ((P.ι ⋙ G').obj X)}
  {hH : ∀ X : Q.FullSubcategory, Q₂ ((Q.ι ⋙ H').obj X)}

/-- **The exchange morphism of restricted adjunctions**: for adjunctions restricted to full
subcategories along lifts of the functors, and a comparison `θ` of the lifts lifting `θ'`, the
exchange morphism of `θ` is that of `θ'`. -/
lemma exchangeRight_restrictFullyFaithful_app_hom
    (θ : P₂.lift (P.ι ⋙ G') hG ⋙ Q₂.lift (P₂.ι ⋙ L₂') hL₂ ≅
      Q.lift (P.ι ⋙ L') hL ⋙ Q₂.lift (Q.ι ⋙ H') hH)
    (hθ : ∀ K, (θ.hom.app K).hom = θ'.hom.app K.obj) (K : Q.FullSubcategory) :
    ((exchangeRight
        (adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
          (Q.liftCompιIso _ hL).symm (P.liftCompιIso _ hR).symm)
        (adj₂.restrictFullyFaithful P₂.fullyFaithfulι Q₂.fullyFaithfulι
          (Q₂.liftCompιIso _ hL₂).symm (P₂.liftCompιIso _ hR₂).symm) θ).app K).hom =
      (exchangeRight adj adj₂ θ').app K.obj := by
  have h := map_exchangeRight_app_of_comm
    (adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
      (Q.liftCompιIso _ hL).symm (P.liftCompιIso _ hR).symm)
    (adj₂.restrictFullyFaithful P₂.fullyFaithfulι Q₂.fullyFaithfulι
      (Q₂.liftCompιIso _ hL₂).symm (P₂.liftCompιIso _ hR₂).symm) θ adj adj₂ θ'
    (Q.liftCompιIso _ hL).symm (P.liftCompιIso _ hR).symm (Q₂.liftCompιIso _ hL₂).symm
    (P₂.liftCompιIso _ hR₂).symm (P₂.liftCompιIso _ hG).symm (Q₂.liftCompιIso _ hH).symm
    (fun K ↦ map_restrictFullyFaithful_unit_app _ _ _ _ _ K)
    (fun K ↦ by
      rw [map_restrictFullyFaithful_counit_app]
      simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom,
        Iso.refl_inv, NatTrans.id_app]
      simp)
    (fun K ↦ by simpa [ObjectProperty.liftCompιIso] using hθ K) K
  simpa [ObjectProperty.liftCompιIso] using h

end CategoryTheory.Adjunction

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category C] [Category D] {P : ObjectProperty D} {F : C ⥤ D}
  {hF : ∀ X, P (F.obj X)}

@[simp]
lemma liftCompιIso_hom_app (X : C) : (P.liftCompιIso F hF).hom.app X = 𝟙 _ :=
  rfl

@[simp]
lemma liftCompιIso_inv_app (X : C) : (P.liftCompιIso F hF).inv.app X = 𝟙 _ :=
  rfl

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Endofunctor.IsoAlgebra

section Pushforward

variable {DX DY 𝒜X 𝒜Y : Type*} {_ : Category DX} {_ : Category DY} {_ : Category 𝒜X}
  {_ : Category 𝒜Y}
  {P : ObjectProperty DX} {Q : ObjectProperty DY}

/-- The commutation `(ι ⋙ H) ⋙ v ≅ L ⋙ (ι ⋙ H)` of the restriction of a functor `H` to a full
subcategory with an endofunctor `L` of the full subcategory lifting `L'`, from a commutation
`θ : H ⋙ v ≅ L' ⋙ H` and the compatibility `c : L ⋙ ι ≅ ι ⋙ L'`. -/
noncomputable def liftComparison {H : DX ⥤ 𝒜X} {v : 𝒜X ⥤ 𝒜X} {L' : DX ⥤ DX}
    {L : P.FullSubcategory ⥤ P.FullSubcategory} (θ : H ⋙ v ≅ L' ⋙ H)
    (c : L ⋙ P.ι ≅ P.ι ⋙ L') :
    (P.ι ⋙ H) ⋙ v ≅ L ⋙ (P.ι ⋙ H) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ θ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c.symm _ ≪≫ Functor.associator _ _ _

/-- **Homology of the transport of algebras along a restricted right adjoint.** Let
`adj_D : L_f ⊣ R_f` be an adjunction of categories `D_Y`, `D_X` restricting to full subcategories
`Q`, `P`, with endofunctors `L_u`, `L_v` and a comparison `θ_D : L_u ⋙ L_f ≅ L_f ⋙ L_v`, all
restricting to the full subcategories. Let `H_X`, `H_Y` be functors to categories with an
adjunction `adj_U : f₁ ⊣ g`, endofunctors `u`, `v` and a comparison `β : u ⋙ f₁ ≅ f₁ ⋙ v`,
commuting with the functors through `θ_u`, `θ_v` and `ψ_a`. If on `H` the exchange morphism of
`θ_D` is that of `β` (`hA`), then for an algebra `K` for `L_v` on the full subcategory, the
transport of the pushforward of `K` along `H_Y` is isomorphic to the pushforward of the transport
of `K` along `H_X`.

The restricted functors, compatibilities, adjunction and base-change morphism are passed as
variables with equations to their definitions, so that concrete instances can use their own
definitions. -/
theorem nonempty_mapOfNatIso_liftComparison_obj_iso
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} (adjD : Lf ⊣ Rf) {Lu : DY ⥤ DY} {Lv : DX ⥤ DX}
    (θD : Lu ⋙ Lf ≅ Lf ⋙ Lv) {HX : DX ⥤ 𝒜X} {HY : DY ⥤ 𝒜Y} {u : 𝒜Y ⥤ 𝒜Y} {v : 𝒜X ⥤ 𝒜X}
    {f₁ : 𝒜Y ⥤ 𝒜X} {g : 𝒜X ⥤ 𝒜Y} (adjU : f₁ ⊣ g) (β : u ⋙ f₁ ≅ f₁ ⋙ v)
    (θu : HY ⋙ u ≅ Lu ⋙ HY) (θv : HX ⋙ v ≅ Lv ⋙ HX) (ψa : HX ⋙ g ≅ Rf ⋙ HY)
    (hA : ∀ K, u.map (ψa.hom.app K) ≫ θu.hom.app (Rf.obj K) ≫
        HY.map ((Adjunction.exchangeRight adjD adjD θD).app K) =
      (Adjunction.exchangeRight adjU adjU β).app (HX.obj K) ≫ g.map (θv.hom.app K) ≫
        ψa.hom.app (Lv.obj K))
    {LfB : Q.FullSubcategory ⥤ P.FullSubcategory} {RfB : P.FullSubcategory ⥤ Q.FullSubcategory}
    {LuB : Q.FullSubcategory ⥤ Q.FullSubcategory} {LvB : P.FullSubcategory ⥤ P.FullSubcategory}
    (cLf : LfB ⋙ P.ι ≅ Q.ι ⋙ Lf) (cRf : RfB ⋙ Q.ι ≅ P.ι ⋙ Rf) (cLu : LuB ⋙ Q.ι ≅ Q.ι ⋙ Lu)
    (cLv : LvB ⋙ P.ι ≅ P.ι ⋙ Lv)
    (hLf : ∀ K : Q.FullSubcategory, P ((Q.ι ⋙ Lf).obj K))
    (hRf : ∀ K : P.FullSubcategory, Q ((P.ι ⋙ Rf).obj K))
    (hLu : ∀ K : Q.FullSubcategory, Q ((Q.ι ⋙ Lu).obj K))
    (hLv : ∀ K : P.FullSubcategory, P ((P.ι ⋙ Lv).obj K))
    (eLf : LfB = P.lift (Q.ι ⋙ Lf) hLf) (eRf : RfB = Q.lift (P.ι ⋙ Rf) hRf)
    (eLu : LuB = Q.lift (Q.ι ⋙ Lu) hLu) (eLv : LvB = P.lift (P.ι ⋙ Lv) hLv)
    (ecLf : HEq cLf (P.liftCompιIso (Q.ι ⋙ Lf) hLf))
    (ecRf : HEq cRf (Q.liftCompιIso (P.ι ⋙ Rf) hRf))
    (ecLu : HEq cLu (Q.liftCompιIso (Q.ι ⋙ Lu) hLu))
    (ecLv : HEq cLv (P.liftCompιIso (P.ι ⋙ Lv) hLv))
    (adjB : LfB ⊣ RfB)
    (eadjB : adjB = adjD.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι cLf.symm cRf.symm)
    (θB : LuB ⋙ LfB ≅ LfB ⋙ LvB) (hθB : ∀ K, HEq (θB.hom.app K).hom (θD.hom.app K.obj))
    (bB : RfB ⋙ LuB ⟶ LvB ⋙ RfB) [IsIso bB] (ebB : bB = Adjunction.exchangeRight adjB adjB θB)
    (exU : g ⋙ u ≅ v ⋙ g) (eexU : exU.hom = Adjunction.exchangeRight adjU adjU β) :
    Nonempty (mapOfNatIso (asIso bB) ⋙ mapOfNatIso (liftComparison θu cLu) ≅
      mapOfNatIso (liftComparison θv cLv) ⋙ mapOfNatIso exU) := by
  subst eLf eRf eLu eLv
  obtain rfl := eq_of_heq ecLf
  obtain rfl := eq_of_heq ecRf
  obtain rfl := eq_of_heq ecLu
  obtain rfl := eq_of_heq ecLv
  subst eadjB ebB
  refine nonempty_mapOfNatIso_comp_mapOfNatIso_iso (asIso _) exU _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Q.liftCompιIso _ hRf) HY ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P.ι ψa.symm ≪≫
      (Functor.associator _ _ _).symm) (fun K ↦ ?_)
  have hB := Adjunction.exchangeRight_restrictFullyFaithful_app_hom (hL := hLf) (hR := hRf)
    (hL₂ := hLf) (hR₂ := hRf) (hG := hLu) (hH := hLv) adjD adjD θD θB
    (fun K ↦ eq_of_heq (hθB K)) K
  have h := hA K.obj
  simp only [liftComparison, ObjectProperty.liftCompιIso_hom_app, ObjectProperty.liftCompιIso_inv_app,
    Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.comp_map, asIso_hom,
    eexU] at h ⊢
  have h' : θu.hom.app (Rf.obj K.obj) ≫ HY.map ((Adjunction.exchangeRight adjD adjD θD).app K.obj) ≫
      ψa.inv.app (Lv.obj K.obj) = u.map (ψa.inv.app K.obj) ≫
        (Adjunction.exchangeRight adjU adjU β).app (HX.obj K.obj) ≫ g.map (θv.hom.app K.obj) := by
    rw [← cancel_epi (u.map (ψa.hom.app K.obj)), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp, reassoc_of% h]
    simp
  rw [ObjectProperty.ι_map, hB]
  exact h'.symm

end Pushforward

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.ObjectProperty.FullSubcategory

/-- The underlying morphism of `eqToHom` in a full subcategory. -/
lemma eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (h : X = Y) : (eqToHom h).hom = eqToHom (congrArg (·.obj) h) := by
  subst h
  rfl

end CategoryTheory.ObjectProperty.FullSubcategory

namespace AlgebraicGeometry

/-- A morphism between schemes locally of finite type over a field is locally of finite
presentation. -/
lemma locallyOfFinitePresentation_left {k : Type*} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) :
    LocallyOfFinitePresentation f.left := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  infer_instance

namespace ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The base-change morphism on the ambient derived categories -/

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The inverse of the composition isomorphism of the derived pullbacks on bounded constructible
complexes, on the ambient derived category. -/
lemma boundedConstructibleUpperStarComp_inv_app_hom {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (a : X' ⟶ Y')
    (b : Y' ⟶ Z) (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b).inv.app K).hom =
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) a.left b.left).inv.app K.obj := by
  rw [← cancel_epi
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b).hom.app K).hom]
  rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app,
    boundedConstructibleUpperStarComp_hom_app_hom, Iso.hom_inv_id_app]
  rfl

-- synthesizing the instances of the derived categories of module objects is slow
set_option maxHeartbeats 1000000 in
/-- The pullback comparison of a commutative square on the ambient derived categories: the
comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of the composition isomorphisms
`leftDerivedUpperStarComp`. -/
noncomputable def leftDerivedUpperStarSquareComparison (sq : CommSq g' f' f g) :
    L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((g'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  Functor.leftDerivedFunctorSquareIso (upperStarComp (Profinite.padicAlgClRingObj ℓ) f'.left g.left)
    (by rw [← Over.comp_left, ← sq.w, Over.comp_left])
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) g'.left f.left)

set_option maxHeartbeats 3000000 in
/-- The pullback comparison of a commutative square on bounded constructible complexes is
`leftDerivedUpperStarSquareComparison` on the ambient derived categories. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_hom (sq : CommSq g' f' f g)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).hom.app
        K).hom = (leftDerivedUpperStarSquareComparison ℓ sq).hom.app K.obj := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.eqToHom_hom,
    boundedConstructibleUpperStarComp_inv_app_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    leftDerivedUpperStarSquareComparison, Functor.leftDerivedFunctorSquareIso_hom_app_eq]
  rfl

end BaseChange

/-! ### Homology of the pushforward of Weil objects -/

section Homology

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The homology sheaf functor of Weil objects is the transport of algebras along the restriction
to bounded constructible complexes of the commutation of the derived pullback with homology. -/
lemma WeilBoundedConstructible.homologyFunctor_eq_mapOfNatIso_liftComparison (e : X ≅ X)
    (n : ℤ) :
    WeilBoundedConstructible.homologyFunctor ℓ e n =
      IsoAlgebra.mapOfNatIso (IsoAlgebra.liftComparison
        ((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.leftDerivedFunctorHomologyFunctorIso n)
        (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)) :=
  rfl

variable (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- `weilLowerStar` as a transport of algebras. -/
lemma weilLowerStar_eq_mapOfNatIso :
    weilLowerStar ℓ eX eY f hf =
      IsoAlgebra.mapOfNatIso (asIso (weilLowerStarComparison ℓ eX eY f hf)) :=
  rfl

end Homology

end ProEtale.CondensedRing

end AlgebraicGeometry
