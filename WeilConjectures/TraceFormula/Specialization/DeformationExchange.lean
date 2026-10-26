/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen
public import WeilConjectures.TraceFormula.Specialization.SupportClosureProper
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.ComponentCounitIso
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The compact-support exchanges of the deformation to the normal cone

For a correspondence `c` contracting at `y`, the compact-support exchanges of blueprint
`det-nearby-exchange-maps` (3) for the support map
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`, through
the compactification `C ⊂ C̄ ⟶ X ⨯ X` deformed along `c̄⁻¹(x, x)`) and for the structure map of `X`
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated`, through a compactification
`X ⊂ X̄` and the dense compactification of the deformation of `X̄`) give the trace specialization
`deformationTraceSpecialization`. This file states that these exchanges specialize the class of
the component `B ∋ y` of the fixed locus
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Gluing an identity `c ≫ L(s ≫ q) ≫ r = w ≫ v` to `w ≫ v ≫ ν = Z`: the composite
`c ≫ L(s') ≫ (L(q) ≫ r) ≫ ν` is `Z` for any `s'` equal to `s`. -/
lemma comp_map_comp_comp_eq_of_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒞 ⥤ 𝒟}
    {u A₁ A₂ B₀ : 𝒟} {U₁ U₂ U₃ : 𝒞} (c : u ⟶ L.obj U₁) (s s' : U₁ ⟶ U₂) (q : U₂ ⟶ U₃)
    (r : L.obj U₃ ⟶ A₁) (w : u ⟶ A₂) (v : A₂ ⟶ A₁) (ν : A₁ ⟶ B₀) (Z : u ⟶ B₀) (hs : s' = s)
    (h : c ≫ L.map (s ≫ q) ≫ r = w ≫ v) (h' : w ≫ v ≫ ν = Z) :
    c ≫ L.map s' ≫ (L.map q ≫ r) ≫ ν = Z := by
  subst hs; rw [← h', ← reassoc_of% h, L.map_comp]; simp only [Category.assoc]

end CategoryTheory

/-- The two sides of an equation. -/
meta def eqSidesOf (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e ← Lean.Meta.whnfR (← Lean.instantiateMVars e)
  let some (_, l, r) := e.eq? | throwError "not an equation"
  return (l, r)

/-- The two factors of a composite `f ≫ g`. -/
meta def compFactors (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``CategoryStruct.comp 7 do throwError "not a composite"
  return (e.getArg! 5, e.getArg! 6)

/-- `glue_unit_class h h'` closes a goal `c ≫ L(s') ≫ ?φ ≫ ν = Z` from
`h : c ≫ L(s ≫ q) ≫ r = w ≫ v` and `h' : w ≫ v ≫ ν = Z`, where `s'` and `s` are definitionally
equal: it assigns `?φ := L(q) ≫ r` and closes the goal with `comp_map_comp_comp_eq_of_eq`. The
identifications `s' = s` and of the remaining terms (which agree up to their proof arguments) are
left to the kernel: the elaborator, through proof irrelevance, infers the types of large proof terms
and needs minutes for them. -/
elab "glue_unit_class " h:ident h':ident : tactic => Lean.Elab.Tactic.withMainContext do
  let he ← Lean.Elab.Tactic.elabTerm h none
  let he' ← Lean.Elab.Tactic.elabTerm h' none
  let (l, wv) ← eqSidesOf (← Lean.Meta.inferType he)
  let (l', Z) ← eqSidesOf (← Lean.Meta.inferType he')
  let (c, rest) ← compFactors l
  let (m, r) ← compFactors rest
  let (s, q) ← compFactors m.consumeMData.appArg!
  let (w, v) ← compFactors wv
  let (_, restD) ← compFactors l'
  let (_, ν) ← compFactors restD
  let (lG, _) ← eqSidesOf (← Lean.Elab.Tactic.getMainTarget)
  let (_, restG) ← compFactors lG
  let (mG, restG') ← compFactors restG
  let (φG, _) ← compFactors restG'
  let s' := mG.consumeMData.appArg!
  -- `?φ := L(q) ≫ r`, with `L(q)` obtained from `L(s ≫ q)` by changing the morphism
  let m := m.consumeMData
  let some (_, _, X, Y) := (← Lean.Meta.whnfR (← Lean.Meta.inferType q)).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let margs := m.getAppArgs
  let n := margs.size
  let mq := Lean.mkAppN m.getAppFn (((margs.set! (n - 3) X).set! (n - 2) Y).set! (n - 1) q)
  let some (_, _, A, _) := (← Lean.Meta.whnfR (← Lean.Meta.inferType mq)).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let rest := rest.consumeMData
  let φ := Lean.mkAppN rest.getAppFn ((rest.getAppArgs.set! 2 A).set! 5 mq)
  unless φG.consumeMData.isMVar do throwError "the middle factor is not a metavariable"
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType φG) (← Lean.Meta.inferType φ) do
    throwError "the middle factor has the wrong type"
  φG.consumeMData.mvarId!.assign φ
  let hs ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl s) (← Lean.Meta.mkEq s' s)
  let pf ← Lean.Meta.mkAppM ``CategoryTheory.comp_map_comp_comp_eq_of_eq
    #[c, s, s', q, r, w, v, ν, Z, hs, he, he']
  let some (_, _, U₁, U₂) := (← Lean.Meta.whnfR (← Lean.Meta.inferType s')).app4? ``Quiver.Hom
    | throwError "unexpected type"
  let args := pf.getAppArgs
  -- the objects of `s'`, so that the statement of the proof is the goal up to proof arguments
  (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN pf.getAppFn ((args.set! 9 U₁).set! 10 U₂))
  Lean.Elab.Tactic.replaceMainGoal []

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)

set_option maxHeartbeats 2000000 in
-- instantiating fact (III) and the reduction at the concrete data is slow
/-- **The compact-support exchanges of the deformation specialize the class of `B`** (blueprint
`det-tf-sp-theta-proper-constant`, `det-tf-sp-theta-open-constant`, with
`det-tf-fixed-deformation-points`; Varshavsky, *Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2): for the exchanges `ν_c`
(`supportCompactSupportExchange`) and `ν_X` (`pointCompactSupportExchangeOfSeparated`), the
exchange `ν_F` of the fixed loci maps the specialization of the unit class of the special fixed
locus `F'` to the specialization of the class of the component `B ∋ y`. Near `y` the deformed fixed
locus is the constant family `B × S` up to nilpotents, on which `ν` is the inverse of the proper
exchange and is compatible with the specialization units. -/
theorem specializesComponentClass_deformation {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    hc.SpecializesComponentClass k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j := by
  have hmem : (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k)) ∈
      Set.range j.left.base := by rw [hB]; rfl
  obtain ⟨b, hbj⟩ : ∃ b : RationalPoint B, b ≫ j = F.liftPoint y hc.comp_c₁_eq_comp_c₂ := by
    have hh : Set.range (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base ⊆
        Set.range j.left.base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim (α := Spec (.of k)) p default]
    exact ⟨Over.homMk (IsOpenImmersion.lift j.left _ hh) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]),
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  have hb : b ≫ j ≫ F.ι = y := by rw [← Category.assoc, hbj, FixedLocus.liftPoint_ι]
  have hI := hc.isIso_ΨF_map_componentCounit k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j hmem
  have hbr : Set.range b.left.base = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨q, hq⟩ : j.left.base p ∈ Set.range j.left.base := ⟨p, rfl⟩
    have h1 : j.left.base p ∈ ({(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base
        (default : Spec (.of k))} : Set _) := hB ▸ ⟨p, rfl⟩
    refine ⟨(default : Spec (.of k)), j.left.isOpenEmbedding.injective ?_⟩
    rw [Set.mem_singleton_iff] at h1
    rw [h1, ← hbj]
    rfl
  have : IsProper (deformationTotalToTrait B b.left.ker k') :=
    isProper_deformationTotalToTrait_ker B k' hbr
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have hN := (deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k') (deformationModel_exists_comp_ε c.C _ k')
  have : IsProper j.left := by
    have : IsProper (j.left ≫ F.F.hom) := by rw [Over.w j]; infer_instance
    exact IsProper.of_comp _ F.F.hom
  have : IsClosedImmersion j.left := .of_isPreimmersion _ j.left.isClosedMap.isClosed_range
  have : IsClosedImmersion (j ≫ F.ι).left := by rw [Over.comp_left]; infer_instance
  have := hc.isClosedImmersion_componentSpecialLift k' j hb
  have h3 := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
    (hc.componentSpecialLift_ι k' j hb) hI
  have hD := unitClass_comp_map_comp_deformationCompactSupportExchange_app B b.left.ker k' (ℓ := ℓ)
  -- Facts (I) and (III) and the unit class identity of `ν_B` are `hI`, `h3` and `hD`; the
  -- cancellation is `TraceSpecialization.specializesComponentClass_of_eq`, and `glue_unit_class`
  -- glues `h3` to `hD`. Still open: fact (II), the factorization `h1` of `ν_F` on `j_! ℚ̄_ℓ`.
  refine TraceSpecialization.specializesComponentClass_of_eq _ _ _ j hI
    (W := _) ?φ ((deformationCompactSupportExchange B b.left.ker k').app (𝟙_ _)) ?h1 ?h2
  case h2 => glue_unit_class h3 hD
  all_goals sorry

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
