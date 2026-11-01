/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionSiteCoefficientPasting

/-! # Descent of the exceptional scalar counit equation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  reductionSiteScalarIso reductionSiteCompactSupportIso reductionDirectImageComparison
  reductionSite scalarExtensionFunctor

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem site_map_bijective
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    Function.Bijective ((reductionSite A T).map : (K ⟶ L) → _) := by
  exact ((sfIntrinsicDerivedEquivalence T A).fullyFaithfulFunctor.map_bijective _ _).comp
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)

private theorem descend_counit
    {CA DA CB DB IA JA IB JB : Type*}
    [Category* CA] [Category* DA] [Category* CB] [Category* DB]
    [Category* IA] [Category* JA] [Category* IB] [Category* JB]
    (FA : CA ⥤ DA) (FB : CB ⥤ DB) (FAi : IA ⥤ JA) (FBi : IB ⥤ JB)
    (UA : CA ⥤ IA) (VA : DA ⥤ JA) (UB : CB ⥤ IB) (VB : DB ⥤ JB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (SX : IA ⥤ IB) (SY : JA ⥤ JB)
    (δX : UA ⋙ SX ≅ S ⋙ UB) (δY : VA ⋙ SY ≅ T ⋙ VB)
    (b : FAi ⋙ SY ⟶ SX ⋙ FBi)
    {M : CA} {N : CB} {L : DA} {K : DB} {X : IA} {Y : IB} {I : JA} {J : JB}
    (ex : X ≅ UA.obj M) (ey : Y ≅ UB.obj N)
    (ox : VA.obj L ≅ I) (oy : VB.obj K ≅ J)
    (sA : FAi.obj (UA.obj M) ≅ VA.obj (FA.obj M))
    (sB : FBi.obj (UB.obj N) ≅ VB.obj (FB.obj N))
    (epsA : FA.obj M ⟶ L) (epsB : FB.obj N ⟶ K)
    (epsAi : FAi.obj X ⟶ I) (epsBi : FBi.obj Y ⟶ J)
    (v : SY.obj I ⟶ J) (a : T.obj L ⟶ K) (m : SX.obj X ⟶ Y)
    (q : T.obj (FA.obj M) ⟶ FB.obj (S.obj M)) (t : S.obj M ⟶ N)
    (hb : IsIso (b.app X))
    (hcA : FAi.map ex.hom ≫ sA.hom ≫ VA.map epsA ≫ ox.hom = epsAi)
    (hcB : FBi.map ey.hom ≫ sB.hom ≫ VB.map epsB ≫ oy.hom = epsBi)
    (ho : VB.map a ≫ oy.hom = δY.inv.app L ≫ SY.map ox.hom ≫ v)
    (hm : FBi.map m ≫ epsBi = @inv _ _ _ _ (b.app X) hb ≫ SY.map epsAi ≫ v)
    (ht : UB.map t = δX.inv.app M ≫ SX.map ex.inv ≫ m ≫ ey.hom)
    (hs : SY.map sA.hom ≫ δY.hom.app (FA.obj M) ≫ VB.map (q ≫ FB.map t) =
      b.app (UA.obj M) ≫ FBi.map (δX.hom.app M ≫ UB.map t) ≫ sB.hom)
    (hinj : Function.Injective (VB.map : (T.obj (FA.obj M) ⟶ K) → _)) :
    q ≫ FB.map t ≫ epsB = T.map epsA ≫ a := by
  let := hb
  have ht' : δX.hom.app M ≫ UB.map t = SX.map ex.inv ≫ m ≫ ey.hom := by
    rw [ht]
    simp only [Iso.hom_inv_id_app_assoc]
  have hn := b.naturality ex.inv
  dsimp only [Functor.comp_map] at hn
  have hd := δY.hom.naturality epsA
  dsimp only [Functor.comp_map] at hd
  have hcA' : FAi.map ex.inv ≫ epsAi = sA.hom ≫ VA.map epsA ≫ ox.hom := by
    rw [← hcA]
    simp only [← FAi.map_comp_assoc, Iso.inv_hom_id, FAi.map_id, Category.id_comp]
  apply hinj
  apply (cancel_mono oy.hom).1
  apply (cancel_epi (SY.map sA.hom ≫ δY.hom.app (FA.obj M))).1
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = b.app (UA.obj M) ≫ FBi.map (δX.hom.app M ≫ UB.map t) ≫
        sB.hom ≫ VB.map epsB ≫ oy.hom := by
      rw [← VB.map_comp_assoc, reassoc_of% hs]
    _ = SY.map (FAi.map ex.inv) ≫ b.app X ≫ FBi.map m ≫ epsBi := by
      rw [ht']
      simp only [FBi.map_comp, Category.assoc]
      rw [hcB, ← reassoc_of% hn]
    _ = SY.map sA.hom ≫ SY.map (VA.map epsA) ≫ SY.map ox.hom ≫ v := by
      rw [hm]
      simp only [IsIso.hom_inv_id_assoc]
      rw [← SY.map_comp_assoc, hcA']
      simp only [SY.map_comp, Category.assoc]
    _ = _ := by
      rw [← reassoc_of% hd, ho]
      simp only [Iso.hom_inv_id_app_assoc]


-- The record fields and the consumer can synthesize distinct proof terms for
-- site instances. Explicit proof-irrelevance congruences prevent kernel reduction
-- through the large chosen derived-functor constructions. This proof builder is
-- the one used in EtaleAffineProjectionCoefficientMate.

private meta def proofArgumentCongruence (fuel : Nat) (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let fuel + 1 := fuel | throwError "congruence depth"
  if a.isFVar then
    if let some v ← a.fvarId!.getValue? then
      return ← proofArgumentCongruence fuel v b
  if b.isFVar then
    if let some v ← b.fvarId!.getValue? then
      return ← proofArgumentCongruence fuel a v
  if a.isLet then
    return ← proofArgumentCongruence fuel (a.letBody!.instantiate1 a.letValue!) b
  if b.isLet then
    return ← proofArgumentCongruence fuel a (b.letBody!.instantiate1 b.letValue!)
  if a.isMData then
    return ← proofArgumentCongruence fuel a.mdataExpr! b
  if b.isMData then
    return ← proofArgumentCongruence fuel a b.mdataExpr!
  if a == b then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  if ← Lean.Meta.isProof a then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
  if a.isApp && b.isApp && a.getAppFn == b.getAppFn then
    try
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if aa.size != ba.size then throwError "arity mismatch"
      let th ← Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
      let mut args : Array Lean.Expr := #[]
      for i in [:aa.size] do
        let h ← proofArgumentCongruence fuel aa[i]! ba[i]!
        let h ← if th.argKinds[i]! == Lean.Meta.CongrArgKind.eq then
            Lean.Meta.mkAppM ``eq_of_heq #[h]
          else pure h
        args := args ++ #[aa[i]!, ba[i]!, h]
      let out := Lean.mkAppN th.proof args
      let ty ← Lean.Meta.inferType out
      if ty.isEq then return ← Lean.Meta.mkAppM ``heq_of_eq #[out]
      return out
    catch _ => pure ()
  if ← Lean.Meta.withReducible (Lean.Meta.isDefEq a b) then
    return ← Lean.Meta.mkAppM ``HEq.refl #[a]
  throwError "nonapplication mismatch: {a} / {b}"

private theorem realized_counit
    (A : Type u) [CommRing A] [Finite A] {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G)
    (R : ReductionExceptionalRealization A j p hF G adj)
    (K : spFiniteConstructibleTorCategory Y A) :
    (reductionCompactSupport A j p).map (R.rightIso.app K).hom ≫
      ((reductionSiteCompactSupportIso A j p).app
        ⟨R.right.obj (R.origin.obj K), R.right_plus K⟩).hom ≫
      (reductionSite A Y).map (R.adjunction.counit.app (R.origin.obj K)) ≫
      (R.originIso.app K).hom = (adj.counit.app K).hom := by
  simp only [Iso.app_hom]
  have h := R.counit K
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let d ← g.getDecl
    let mut last : Option Lean.LocalDecl := none
    for l in d.lctx do
      last := some l
    let some hdecl := last | throwError "missing realization counit equation"
    let source ← Lean.Meta.whnf (← Lean.instantiateMVars hdecl.type)
    let target ← Lean.Meta.whnf (← Lean.instantiateMVars d.type)
    let he ← proofArgumentCongruence 100 source target
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[he]
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, hdecl.toExpr])

/-- The coefficient counit equation descends to the ordinary etale realization.
Source: blueprint latest, reduction-exceptional proof, Charts and Locality,
site/coefficient compatibility square (blueprint: lem-sp-reduction-counit-descent).

Proof: apply the faithful intrinsic realization inverse and use the specified
coefficient/site compact-support square on the A exceptional output. Conjugate
this square by RA.rightIso and RB.rightIso, and use naturality of both compact-
support comparisons at q. The two realization counit equations replace the
transported ordinary counits by the intrinsic counits. The given equation for m
then cancels the invertible coefficient comparison. The input equation for a
identifies the last endpoint with the ordinary scalar input. Full faithfulness
of comparison into a bounded-below target reflects the resulting equality.
All boundedness assertions needed for the square follow from the finite-Tor
intrinsic right outputs and their specified bounded-below origins; no chart or
invertibility of m is used. -/
theorem reductionExceptional_counit_descent
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (K : spFiniteConstructibleTorCategory Y A)
    (KB : spFiniteConstructibleTorCategory Y B)
    (v : (scalarExtensionFunctor φ Y).obj K.obj ⟶ KB.obj)
    (a : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj
      (RA.origin.obj K) ⟶ RB.origin.obj KB)
    (ha : (reductionSite B Y).map a ≫ RB.originIso.hom.app KB =
      (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj K) ≫
        (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app K) ≫ v)
    (m : (scalarExtensionFunctor φ X).obj (GA.obj K).obj ⟶ (GB.obj KB).obj)
    (hb : IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj))
    (hm : (reductionCompactSupport B j p).map m ≫ (adjB.counit.app KB).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj) hb ≫
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom ≫ v)
    (q : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj
      (RA.right.obj (RA.origin.obj K)) ⟶ RB.right.obj (RB.origin.obj KB))
    (hq : (reductionSite B X).map q =
      (reductionSiteScalarIso φ X).inv.app (RA.right.obj (RA.origin.obj K)) ≫
        (scalarExtensionFunctor φ X).map (RA.rightIso.inv.app K) ≫
        m ≫ RB.rightIso.hom.app KB) :
    (Etale.compactScalarMap (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).app
        (RA.right.obj (RA.origin.obj K)) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).map q ≫
      RB.adjunction.counit.app (RB.origin.obj KB) =
    (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).map
      (RA.adjunction.counit.app (RA.origin.obj K)) ≫ a := by
  let C : Compactification (j ≫ p) :=
    ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
  let M := RA.right.obj (RA.origin.obj K)
  let N := RB.right.obj (RB.origin.obj KB)
  let FA := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) C
  let FB := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) C
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} φ
  have hinj := (site_map_bijective B Y
    ((Etale.scalarExtension ψ Y).obj (FA.obj M)) (RB.origin.obj KB)
    (RB.origin_ctf KB).1.1.1).1
  dsimp only [Etale.compactScalarMap]
  have h := descend_counit FA FB (reductionCompactSupport A j p)
    (reductionCompactSupport B j p)
    (reductionSite A X) (reductionSite A Y) (reductionSite B X) (reductionSite B Y)
    (Etale.scalarExtension ψ X) (Etale.scalarExtension ψ Y)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ Y)
    (reductionSiteScalarIso φ X) (reductionSiteScalarIso φ Y)
    (reductionDirectImageComparison φ j p) (RA.rightIso.app K) (RB.rightIso.app KB)
    (RA.originIso.app K) (RB.originIso.app KB)
    ((reductionSiteCompactSupportIso A j p).app ⟨M, RA.right_plus K⟩)
    ((reductionSiteCompactSupportIso B j p).app ⟨N, RB.right_plus KB⟩)
    (RA.adjunction.counit.app (RA.origin.obj K))
    (RB.adjunction.counit.app (RB.origin.obj KB))
    (adjA.counit.app K).hom (adjB.counit.app KB).hom v a m
    (Etale.ExceptionalCoefficients.compactSupportMap ψ C M) q hb
    (realized_counit A j p hFA GA adjA RA K)
    (realized_counit B j p hFB GB adjB RB KB)
    ha hm hq
    (reductionSiteCoefficientPasting φ j p M (RA.right_plus K) N (RB.right_plus KB) q)
    hinj
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let d ← g.getDecl
    let mut last : Option Lean.LocalDecl := none
    for l in d.lctx do
      last := some l
    let some hdecl := last | throwError "missing ordinary counit equation"
    let source ← Lean.Meta.whnf (← Lean.instantiateMVars hdecl.type)
    let target ← Lean.Meta.whnf (← Lean.instantiateMVars d.type)
    let he ← proofArgumentCongruence 100 source target
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[he]
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, hdecl.toExpr])

end AlgebraicGeometry.ProEtale
