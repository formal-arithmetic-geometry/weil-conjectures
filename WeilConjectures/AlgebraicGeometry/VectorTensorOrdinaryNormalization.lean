/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.NormalizedVectorPurityBundle
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # Ordinary normalization of coefficient-first vector integration
Source: blueprint vector-bundle purity, ordinary integration and its adjunction transpose.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

attribute [local implicit_reducible] Scheme.Modules

private theorem normalized_swap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [BraidedCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (W : C) (t : L.obj W ⟶ 𝟙_ D) (K : D)
    (γ : W ⊗ P.obj K ⟶ R.obj K)
    (π : L.obj W ⊗ K ⟶ L.obj (W ⊗ P.obj K))
    (p : L.obj (P.obj K ⊗ W) ≅ K ⊗ L.obj W)
    (hp : p.inv = (β_ K (L.obj W)).hom ≫ π ≫ L.map (β_ W (P.obj K)).hom)
    (hn : π ≫ L.map γ ≫ adj.counit.app K = (t ▷ K) ≫ (λ_ K).hom) :
    adj.homEquiv _ K (p.hom ≫ (K ◁ t) ≫ (ρ_ K).hom) =
      (β_ (P.obj K) W).hom ≫ γ := by
  apply (adj.homEquiv _ K).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]
  apply (cancel_epi p.inv).1
  rw [Iso.inv_hom_id_assoc, hp]
  simp only [Category.assoc, ← L.map_comp_assoc, SymmetricCategory.symmetry_assoc]
  rw [hn, ← BraidedCategory.braiding_naturality_right_assoc]
  simp

-- Check the canonical braiding identifications before specializing to ModuleCat A.
private theorem normalized_etale_swap
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X Y : Scheme.{u})
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (R P : DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology B)) (adj : L ⊣ R)
    (W : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (t : L.obj W ⟶ (DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology B) 0).obj (𝟙_ (Sheaf Y.smallEtaleTopology B)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (γ : W ⊗ P.obj K ⟶ R.obj K)
    (π : L.obj W ⊗ K ⟶ L.obj (W ⊗ P.obj K))
    (p : L.obj (P.obj K ⊗ W) ≅ K ⊗ L.obj W)
    (hp : p.inv = ((Etale.derivedTensorSymmetry B Y).hom.app K).app (L.obj W) ≫
      π ≫ L.map (((Etale.derivedTensorSymmetry B X).hom.app W).app (P.obj K)))
    (hn : ∃ m : L.obj (W ⊗ P.obj K) ⟶ K,
      HEq (L.map γ ≫ adj.counit.app K) m ∧
      HEq (π ≫ m) (((t ≫ (Etale.singleFunctorObjUnitIso B Y).hom) ▷ K) ≫
        (λ_ K).hom)) :
    adj.homEquiv _ K (p.hom ≫ ((Etale.derivedTensor B Y).obj K).map t ≫
      (Etale.derivedTensorRightUnitor B Y K).hom) =
      ((Etale.derivedTensorSymmetry B X).hom.app (P.obj K)).app W ≫ γ := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology B)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology B)
  obtain ⟨m, hm, hπ⟩ := hn
  have hu : (Etale.singleFunctorObjUnitIso B Y).hom = 𝟙 _ := by
    have h := (Etale.singleFunctorObjUnitIso B Y).hom_inv_id
    rwa [Etale.singleFunctorObjUnitIso_inv, Category.comp_id] at h
  have ht : t ≫ (Etale.singleFunctorObjUnitIso B Y).hom = t := by
    rw [hu]
    exact Category.comp_id _
  rw [ht] at hπ
  have hn' := eq_of_heq hπ
  rw [← eq_of_heq hm] at hn'
  exact normalized_swap L R P adj W t K γ π p hp hn'

attribute [local irreducible] Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction

-- Retain the native finite-coefficient presentations when specializing the calculation.
open WeilConjectures.PurityFiniteSetting in
private theorem normalized_finite_swap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X)
    (t : (RfShriek A f).obj W ⟶ Etale.ordinaryFiniteUnit A Y)
    (K : Etale.DerivedCategoryModule A Y)
    (γ : RfPullback A f ⋙ tensorLeft W ⟶ RfUpper A f)
    (p : (RfShriek A f).obj
        (((Etale.derivedTensor (ModuleCat A) X).obj ((RfPullback A f).obj K)).obj W) ≅
      ((Etale.derivedTensor (ModuleCat A) Y).obj K).obj ((RfShriek A f).obj W))
    (hp : p.inv = Etale.compactProjectionMapCoeffFirst A f K W)
    (hn : IntegrationGammaNormalized (RfShriek A f) (RfUpper A f) (RfPullback A f)
      (Etale.rightDerivedUpperShriekAdjunction A f) W
      (t ≫ (Etale.singleFunctorObjUnitIso (ModuleCat A) Y).hom)
      ((Etale.projectionMap (ModuleCat A) f).app W) γ) :
    (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ K
      (p.hom ≫ ((Etale.derivedTensor (ModuleCat A) Y).obj K).map t ≫
        (Etale.derivedTensorRightUnitor (ModuleCat A) Y K).hom) =
      ((Etale.derivedTensorSymmetry (ModuleCat A) X).hom.app
        ((RfPullback A f).obj K)).app W ≫ γ.app K := by
  exact normalized_etale_swap (ModuleCat A) X Y
    (RfShriek A f) (RfUpper A f) (RfPullback A f)
    (Etale.rightDerivedUpperShriekAdjunction A f) W t K (γ.app K)
    (((Etale.projectionMap (ModuleCat A) f).app W).app K) p hp (hn K)

-- Infer the native proposition and share its nested instance proofs as a definition.
-- This is a proof value, obtained directly from the existing normalization theorem.
set_option linter.defProp false in
private def vector_normalized_family
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :=
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  (WeilConjectures.PurityFiniteSetting.vectorBundleNormalized A N hN hA S hS d F).2

private theorem hpi_congr {α β : Sort v} {p : α → Sort w} {q : β → Sort w}
    (ht : α = β) (h : ∀ a b, HEq a b → p a = q b) :
    (∀ a, p a) = (∀ b, q b) := by
  cases ht
  have hpq : p = q := funext fun a ↦ h a a HEq.rfl
  cases hpq
  rfl

private theorem hfunext {α β : Sort v} {P : α → Sort w} {Q : β → Sort w}
    {f : ∀ a, P a} {g : ∀ b, Q b} (ht : α = β)
    (hPQ : ∀ a b, HEq a b → P a = Q b)
    (h : ∀ a b, HEq a b → HEq (f a) (g b)) : HEq f g := by
  cases ht
  have hPQ' : P = Q := funext fun a ↦ hPQ a a HEq.rfl
  cases hPQ'
  apply heq_of_eq
  funext a
  exact eq_of_heq (h a a HEq.rfl)

-- Build the definitional comparison by cached heterogeneous congruence.
-- Each step is an ordinary equality proof checked by the kernel. Keeping repeated
-- instance comparisons shared avoids unfolding the native tensor constructions.
open Lean Meta Elab Tactic in
private meta def expandProjection (e : Expr) : MetaM Expr := do
  let .proj n i receiver := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) n | return e
  let field := n ++ info.fieldNames[i]!
  return mkAppN (← mkAppM field #[receiver]) e.getAppArgs

open Lean Meta Elab Tactic in
private meta partial def structuralRefl (g : MVarId) (fuel : Nat) :
    StateRefT (ExprMap Expr) MetaM Unit :=
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    if let some proof := (← get).get? target then
      g.assign proof
      return
    let h ← mkFreshExprSyntheticOpaqueMVar target
    structuralReflCore h.mvarId! fuel
    let proof ← instantiateMVars h
    if proof.hasMVar || proof.hasSorry then
      throwError "incomplete structural congruence"
    modify fun cache => cache.insert target proof
    g.assign proof
where
  structuralReflCore (g : MVarId) (fuel : Nat) :
      StateRefT (ExprMap Expr) MetaM Unit := g.withContext do
    if fuel == 0 then throwError "structural reflexivity exhausted"
    let target ← g.getType
    try
      g.assumption
      return
    catch _ => pure ()
    let (lhs, rhs) ←
      if let some (_, lhs, rhs) := target.eq? then pure (lhs, rhs)
      else if let some (_, lhs, _, rhs) := target.heq? then pure (lhs, rhs)
      else throwError "expected equality"
    if lhs == rhs then
      if target.isHEq then g.assign (← mkHEqRefl lhs)
      else g.assign (← mkEqRefl lhs)
    else if (← isProof lhs) && (← isProof rhs) then
      let proof ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let proof ← if target.isHEq then pure proof else mkEqOfHEq proof
      g.assign proof
    else if lhs.isForall && rhs.isForall then
      let ge ← g.heqOfEq
      let gs ← ge.apply (← mkConstWithFreshMVarLevels ``hpi_congr)
      match gs with
      | [ht, hb] =>
        structuralRefl ht (fuel - 1)
        let (_, hb) ← hb.intro1
        let (_, hb) ← hb.intro1
        let (_, hb) ← hb.intro1
        structuralRefl hb (fuel - 1)
      | _ => throwError "Unexpected heterogeneous forall goals"
    else if lhs.isLambda && rhs.isLambda then
      let gh ← g.eqOfHEq
      let gs ← gh.apply (← mkConstWithFreshMVarLevels ``hfunext)
      match gs with
      | [ht, hPQ, hb] =>
        structuralRefl ht (fuel - 1)
        for h in [hPQ, hb] do
          let (_, h) ← h.intro1
          let (_, h) ← h.intro1
          let (_, h) ← h.intro1
          structuralRefl h (fuel - 1)
      | _ => throwError "Unexpected heterogeneous function goals"
    else if lhs.isApp && lhs.getAppFn == rhs.getAppFn then
      let gh ← g.eqOfHEq
      let ct ← mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      let cp ← abstractProof ct.proof
      let gs ← gh.apply cp { synthAssignedInstances := false }
      for h in gs do structuralRefl h (fuel - 1)
    else
      let lhs' ← expandProjection lhs
      let rhs' ← expandProjection rhs
      let lhs' ← if lhs' == lhs then withTransparency .all (whnf lhs) else pure lhs'
      let rhs' ← if rhs' == rhs then withTransparency .all (whnf rhs) else pure rhs'
      if lhs' == lhs && rhs' == rhs then
        g.refl
      else
        let ty ← if target.isHEq then mkHEq lhs' rhs' else mkEq lhs' rhs'
        let h ← mkFreshExprSyntheticOpaqueMVar ty
        g.assign h
        structuralRefl h.mvarId! (fuel - 1)

open Lean Meta Elab Tactic in
local elab "structural_rfl" : tactic => do
  let _ ← (structuralRefl (← getMainGoal) 100).run {}
  replaceMainGoal []

private theorem vector_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S) :
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    ∀ (γ : WeilConjectures.PurityFiniteSetting.VectorPurityGamma A N hA S d F)
      (pe : (Etale.vectorBundlePurityLower A S d F).obj
        (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (Etale.vectorIntegrationSource A N hA S d F))
      (_hpe : pe.inv = Etale.vectorBundlePurityProjectionMap A N hA S d F K),
      WeilConjectures.PurityFiniteSetting.VectorPurityGammaNormalized
        A N hN hA S hS d F γ →
      HEq ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K
        (ordinaryTensorIntegrate A S K (Etale.vectorIntegrationSource A N hA S d F)
          _ pe (Etale.vectorBundleIntegration N hN A hA S hS d F)))
        ((((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.scheme S d F)).hom.app
            ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj K)).app
              (Etale.vectorIntegrationCoefficient A N hA S d F)) ≫ γ.app K) := by
  let := (Etale.vectorIntegration_geometry S d F).1
  let := (Etale.vectorIntegration_geometry S d F).2.1
  have h := normalized_finite_swap A (VectorBundleZeroSection.π S d F)
    (Etale.vectorIntegrationCoefficient A N hA S d F)
    (Etale.vectorBundleIntegration N hN A hA S hS d F) K
  have h' := fun γ pe hp hn ↦ (h γ pe hp hn).heq
  refine Eq.mp ?_ h'
  structural_rfl

/-- The ordinary inverse-projection integration has the prescribed normalized purity
adjunct, with the explicit signed symmetry from coefficient-first to twist-first order.
Source: blueprint sec-smooth-purity/sk-prop-an/thm-amb-vector-bundle-purity.proof.md,
first two paragraphs; normalization of def-pur-vector-purity-normalization.
(blueprint: lem-route-vector-tensor-ordinary-normalization).

Proof: take the normalized family gamma supplied by vectorBundleNormalized. At K its
normalization says that the compact-support image of gamma followed by the Brown counit
is the inverse ordinary projection followed by the trace tensored with K and the left
unitor. Precompose with the signed symmetry to switch the input to coefficient-first
order. The coefficient-first projection is defined by precisely these two symmetries;
invert this composite. The finite-unit map in the normalization is the identity:
Etale.singleFunctorObjUnitIso_inv and the inverse-hom identity give this for its hom.
Naturality of symmetry moves the trace across it, and its unit
identity turns the left unitor into the right unitor. Since pe.inv is the actual
coefficient-first projection, this is exactly ordinaryTensorIntegrate with pe. Applying
the adjunction Hom bijection gives the displayed component identity. The same calculation
works in rank zero and over the empty base, and requires no flatness over Z/N.
-/
theorem vectorTensorOrdinaryNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (pe : (Etale.vectorBundlePurityLower A S d F).obj
        (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (Etale.vectorIntegrationSource A N hA S d F))
    (hpe : pe.inv = Etale.vectorBundlePurityProjectionMap A N hA S d F K) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
      (Etale.vectorIntegration_geometry S d F).2.1
    ∃ γ : WeilConjectures.PurityFiniteSetting.VectorPurityGamma A N hA S d F,
      WeilConjectures.PurityFiniteSetting.VectorPurityGammaNormalized
        A N hN hA S hS d F γ ∧
      HEq ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K
        (ordinaryTensorIntegrate A S K (Etale.vectorIntegrationSource A N hA S d F)
          _ pe (Etale.vectorBundleIntegration N hN A hA S hS d F)))
        ((((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.scheme S d F)).hom.app
            ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj K)).app
              (Etale.vectorIntegrationCoefficient A N hA S d F)) ≫ γ.app K) := by
  let := (Etale.vectorIntegration_geometry S d F).1
  let := (Etale.vectorIntegration_geometry S d F).2.1
  obtain ⟨γ, hn, _⟩ := vector_normalized_family A N hN hA S hS d F
  refine ⟨γ, hn, ?_⟩
  exact vector_component A N hN hA S hS d F K γ pe hpe hn

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
