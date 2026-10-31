/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Algebra.Category.Grp.AB

meta import Mathlib.Lean.Meta.CongrTheorems

/-!
# Module and derived comparison for pullback from the condensed point

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pp. 5--6, pullback paragraph before (3.1), Remark 3.2 and Definition 3.5
(blueprint: lem-zl-condensed-point-module-comparison).

The ordinary comparison is the existing `CondensedRing.upperStarFromPointModComp`.
Its scalar cancellation uses the specified coefficient isomorphism, and its underlying
map is `upperStarFromPointComp`. The internal module categories are identified with
sectionwise module sheaves by `InternalAbelianSheafModule.sectionModuleEquivalence`;
`InternalModuleOperations.upperComparison` identifies the two module inverse images.
All derived categories here are ordinary and unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory

/-- Point-module inverse image preserves finite limits.
Source: HRS Section 3, pp. 5--6 (blueprint: lem-zl-condensed-point-module-comparison).
Proof: Step 1. The profinite test-object functor preserves finite limits and coverings.
The site inverse-image tensor lemma therefore makes its sheafified left Kan extension
exact on abelian sheaves. Compose with the exact scheme inverse image along the structure
map. The action transported by `mapMod` does not change the underlying functor; finite
limits of modules are computed on underlying abelian sheaves, by the lifted-exactness
lemma. Thus point-module pullback preserves finite limits. -/
@[instance]
theorem condensedPointModule_preservesFiniteLimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (CondensedRing.upperStarFromPointMod Λ X) := by
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  unfold CondensedRing.upperStarFromPointMod
  infer_instance

/-- Point-module inverse image preserves finite colimits.
Source: HRS Section 3, pp. 5--6 (blueprint: lem-zl-condensed-point-module-comparison).
Proof: Step 1. The sheafified left Kan extension and scheme inverse image preserve finite
colimits on abelian sheaves. Tensoring on either site preserves colimits. Module
categories are abelian, and finite colimits are computed on underlying abelian sheaves.
The module transport's equality of underlying functors therefore gives finite-colimit
preservation by the lifted-exactness lemma. -/
@[instance]
theorem condensedPointModule_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (CondensedRing.upperStarFromPointMod Λ X) := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  unfold CondensedRing.upperStarFromPointMod
  infer_instance

/-- Point-module inverse image is additive.
Source: HRS Section 3, pp. 5--6 (blueprint: lem-zl-condensed-point-module-comparison).
Proof: Step 1. The abelian inverse image is additive by the site inverse-image tensor
lemma and exact scheme inverse image. The module transport commutes with forgetting the
action, which is faithful and additive; the lifted-exactness lemma gives additivity. -/
@[instance]
theorem condensedPointModule_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (CondensedRing.upperStarFromPointMod Λ X).Additive := by
  have : PreservesBinaryBiproducts (CondensedRing.upperStarFromPointMod Λ X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The specified point comparison is linear after transport along the coefficient
isomorphism. The source action is explicitly restriction along the inverse of alpha_f.
Source: HRS Section 3, p. 6 (blueprint: lem-zl-condensed-point-module-comparison).
Proof: Steps 2--3. Write P = p_X^*, Q = f^{-1}, H = p_T^* and e = upperStarFromPointComp.
Extension along alpha_f is canonically restriction along its inverse, with section map
`a tensor m` sent to `alpha_f^{-1}(a)m`, inverse `m` sent to `1 tensor m`.
Apply the restricted-transport linearity lemma with psi = identity, psi' = alpha_f^{-1}
and phi = identity. Its coefficient condition is alpha_f^{-1} followed by alpha_f = 1.
Monoidality of e gives the displayed action identity. The inverse identity follows by
cancelling e and tensoring its inverse. Naturality of e gives naturality on module maps.
These are the components of the existing `CondensedRing.upperStarFromPointModComp`. -/
theorem condensedPointModule_comparison_linear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Mod.act (A := condensedRingObj Λ T)
        (((Mod.comap (inv (condensedPullbackHom Λ f))).obj
          (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj
            ((CondensedRing.upperStarFromPointMod Λ X).obj M))).X) ≫
        (upperStarFromPointComp f).hom.app M.X =
      condensedRingObj Λ T ◁ (upperStarFromPointComp f).hom.app M.X ≫
        Mod.act (A := condensedRingObj Λ T)
          ((CondensedRing.upperStarFromPointMod Λ T).obj M).X := by
  let N := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj
    ((CondensedRing.upperStarFromPointMod Λ X).obj M)
  let P := (CondensedRing.upperStarFromPointMod Λ T).obj M
  let e : N.X ⟶ P.X := (upperStarFromPointComp f).hom.app M.X
  let α := condensedPullbackHom Λ f
  have h := Mod.act_hom
    ((Functor.mapModCompIso (upperStarFromPoint X) (upperStar Ab.{u + 1} f)
      (upperStarFromPointComp f).hom Λ).hom.app M)
  change Mod.act N.X ≫ e =
    (upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X) ◁ e ≫
      (α ▷ P.X ≫ Mod.act P.X) at h
  change (inv α ▷ N.X ≫ Mod.act N.X) ≫ e =
    condensedRingObj Λ T ◁ e ≫ Mod.act P.X
  rw [Category.assoc, h, ← whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp]

/-- The derived comparison is the localization of the existing module comparison,
preceded by the inverse exact-derived composition isomorphism.
Source: HRS Section 3, p. 6; Stacks Tag 04VG
(blueprint: lem-zl-condensed-point-module-comparison). -/
noncomputable def condensedPointModuleDerivedComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T X : Scheme.{u}} (f : T ⟶ X) :
    (CondensedRing.upperStarFromPointMod Λ X).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ f).mapDerivedCategory ≅
      (CondensedRing.upperStarFromPointMod Λ T).mapDerivedCategory :=
  letI := comp_preservesFiniteLimits
    (CondensedRing.upperStarFromPointMod Λ X) (CondensedRing.upperStar Λ f)
  letI := comp_preservesFiniteColimits
    (CondensedRing.upperStarFromPointMod Λ X) (CondensedRing.upperStar Λ f)
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStarFromPointMod Λ X)
    (CondensedRing.upperStar Λ f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarFromPointModComp Λ f)

/- The final equation carries definitionally equal preadditive structures in the proof
arguments of the composite functor's additivity instance. Unstructured conversion unfolds
localization and sheaf inverse images before reconciling them. As in PerfectProjectionFormula,
construct the conversion by congruence and proof irrelevance. The result is kernel checked. -/
local syntax (name := pointStructuralExact) "point_structural_exact " term : tactic

meta section
open Lean Meta Elab Tactic
private def pointConversionAliases : Array Name := #[
  `inferInstance, `CochainComplex, `CategoryTheory.Abelian.toPreadditive,
  `CategoryTheory.Mod.instAbelian, `CategoryTheory.Abelian.ofCoimageImageComparisonIsIso]
private structure PointConversionState where
  proofs : Std.HashMap (Expr × Expr) Expr := {}
  congruences : Std.HashMap (Expr × Array Bool) CongrTheorem := {}
private def pointMetadataHEq (fuel : Nat) (left right : Expr) :
    StateRefT PointConversionState MetaM Expr := do
  match fuel with
  | 0 => throwError "structural conversion exceeded its depth bound"
  | fuel + 1 =>
    let a := left.consumeMData
    let b := right.consumeMData
    if let some p := (← get).proofs.get? (a,b) then return p
    let p ← do
      if a == b then return ← mkHEqRefl a
      if (← isProof a) && (← isProof b) then
        return ← mkAppM ``proof_irrel_heq #[a,b]
      let fa := a.getAppFn
      let fb := b.getAppFn
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      if fa == fb && aa.size == bb.size && !aa.isEmpty then
        let info ← getFunInfoNArgs fa aa.size
        let fixed := aa.zip bb |>.map fun (x,y) => x == y
        let key := (fa,fixed)
        let thm ← match (← get).congruences.get? key with
          | some thm => pure thm
          | none => do
            let thm ← mkRichHCongr (← inferType fa) info
              (fixedFun := true) (fixedParams := fixed) (forceHEq := true)
            modify fun st => { st with congruences := st.congruences.insert key thm }
            pure thm
        let mut result := mkApp thm.proof fa
        for i in [:aa.size] do
          result := mkApp result aa[i]!
          match thm.argKinds[i+1]! with
          | .fixed => pure ()
          | .subsingletonInst => result := mkApp result bb[i]!
          | .eq | .heq =>
            result := mkApp result bb[i]!
            let expected ← whnf (← inferType result)
            let hp ← forallTelescope expected.bindingDomain! fun xs ty => do
              let hp ← match ty.eq?, ty.heq? with
                | some (_, x,y), _ => do
                  let h ← try pointMetadataHEq fuel x y catch ex =>
                    throwError "argument {i} of {fa.constName?}: {ex.toMessageData}"
                  mkAppM ``eq_of_heq #[h]
                | _, some (_, x, _, y) =>
                  try pointMetadataHEq fuel x y catch ex =>
                    throwError "argument {i} of {fa.constName?}: {ex.toMessageData}"
                | _, _ => throwError "unexpected congruence premise {ty}"
              mkLambdaFVars xs hp
            result := mkApp result hp
          | k => throwError "unexpected congruence argument {repr k}"
        return result
      if let some v ← delta? a (pointConversionAliases.contains ·) then
        let h₁ ← mkHEqRefl a
        let h₂ ← pointMetadataHEq fuel v.headBeta b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      if let some v ← delta? b (pointConversionAliases.contains ·) then
        let h₁ ← pointMetadataHEq fuel a v.headBeta
        let h₂ ← mkHEqRefl b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      match a,b with
      | .const n us, .const m vs =>
        if n == m && us.length == vs.length then
          if ← (us.zip vs).allM (fun (u,v) => isLevelDefEq u v) then
            return ← mkHEqRefl a
      | .sort u, .sort v =>
        if ← isLevelDefEq u v then return ← mkHEqRefl a
      | _, _ => pure ()
      if ← withTransparency .default (isDefEq a b) then
        return ← mkHEqRefl a
      throwError "structural conversion stopped at {a.getAppFn.constName?} \
        and {b.getAppFn.constName?}"
    modify fun st => { st with proofs := st.proofs.insert (a,b) p }
    return p
termination_by fuel
end

open Lean Meta Elab Tactic in
@[local tactic pointStructuralExact] private meta def evalPointStructuralExact : Tactic :=
    fun stx => withMainContext do
  let h : TSyntax `term := ⟨stx[1]⟩
  let p ← elabTerm h none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let source ← instantiateMVars (← inferType p)
  let target ← instantiateMVars (← getMainTarget)
  let (heq, _) ← (pointMetadataHEq 1000 source target).run {}
  let eq ← mkAppM ``eq_of_heq #[heq]
  let result ← mkAppM ``Eq.mp #[eq,p]
  (← getMainGoal).assign result
  replaceMainGoal []

private theorem derivedComparison_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T X : Scheme.{u}} (f : T ⟶ X) :
    (condensedPointModuleDerivedComparison Λ f).hom =
      (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStarFromPointMod Λ X)
        (CondensedRing.upperStar Λ f)).inv ≫
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarFromPointModComp Λ f)).hom :=
  rfl

private theorem derivedNatIso_factors
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategoryFactors.hom.app K =
    F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) :=
  Functor.mapDerivedCategoryNatIso_fac e K

private theorem cancel_iso_normalization {C : Type*} [Category C]
    {A B D E H I : C} {e : A ⟶ B} {a : A ⟶ H}
    {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ H} {k : H ⟶ I}
    {x : A ⟶ I} {i : B ⟶ A}
    (hn : x = a ≫ k) (hc : e ≫ b ≫ c ≫ d = a) (hi : i ≫ e = 𝟙 B) :
    i ≫ x = b ≫ c ≫ d ≫ k := by
  rw [hn, ← hc]
  simp only [← Category.assoc, hi, Category.id_comp]

attribute [local irreducible] CondensedRing.upperStarFromPointMod CondensedRing.upperStar
  upperStarFromPoint upperStar Functor.mapMod Functor.mapHomologicalComplex

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward true in
/-- On every unbounded representative the derived comparison is precisely the
localization of the chain comparison, after the canonical termwise factorizations.
Source: HRS Section 3, p. 6; Stacks Tags 04VG and 015F
(blueprint: lem-zl-condensed-point-module-comparison).
Proof: Step 4. Scheme module pullback is exact since alpha_f is invertible. The exact
internal/sectionwise module equivalences and their canonical pullback comparison identify
it with the module inverse image of the pro-etale operations node. Step 5. Apply the
module comparison to each term and differential of K. Naturality is exactly the chain-map
equation, and the inverse comparison supplies the inverse chain map. Both exact functors
preserve quasi-isomorphisms, so localization induces the derived natural isomorphism;
the exact-derived natural-isomorphism lemma gives its factorization identity. Step 6.
The exact-derived composition lemma identifies the derived composite with the composite
of derived functors, normalized by the iterated termwise factorization. Compose its
inverse with the localized module comparison to obtain this equality. The exact-functor
derived-functor lemma identifies D(f^*) with Lf^*, computed on every complex. Transporting
through the internal/sectionwise equivalence preserves this normalization. Before
localization, the degree-n component is phi at K.X n, under the scalar cancellation
of the preceding linearity theorem. No flatness, boundedness or finiteness is used. -/
theorem condensedPointModuleDerivedComparison_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T X : Scheme.{u}} (f : T ⟶ X)
    (K : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ) :
    (condensedPointModuleDerivedComparison Λ f).hom.app (DerivedCategory.Q.obj K) ≫
        (CondensedRing.upperStarFromPointMod Λ T).mapDerivedCategoryFactors.hom.app K =
      (CondensedRing.upperStar Λ f).mapDerivedCategory.map
          ((CondensedRing.upperStarFromPointMod Λ X).mapDerivedCategoryFactors.hom.app K) ≫
        (CondensedRing.upperStar Λ f).mapDerivedCategoryFactors.hom.app
          (((CondensedRing.upperStarFromPointMod Λ X).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (CondensedRing.upperStarFromPointMod Λ X ⋙
              CondensedRing.upperStar Λ f)) (.up ℤ)).hom.app K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (CondensedRing.upperStarFromPointModComp Λ f)
            (.up ℤ)).hom.app K) := by
  rw [derivedComparison_hom Λ f]
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc]
  have hn := derivedNatIso_factors
    (F := CondensedRing.upperStarFromPointMod Λ X ⋙ CondensedRing.upperStar Λ f)
    (G := CondensedRing.upperStarFromPointMod Λ T)
    (CondensedRing.upperStarFromPointModComp Λ f) K
  have hc := Functor.mapDerivedCategoryCompIso_fac
    (C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (CondensedRing.upperStarFromPointMod Λ X) (CondensedRing.upperStar Λ f) K
  have hi := Iso.inv_hom_id_app (Functor.mapDerivedCategoryCompIso
    (C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (CondensedRing.upperStarFromPointMod Λ X) (CondensedRing.upperStar Λ f))
      ((DerivedCategory.Q (C := Mod (Sheaf (coherentTopology Profinite.{u})
        Ab.{u + 1}) Λ)).obj K)
  have h := cancel_iso_normalization hn hc hi
  dsimp only [Functor.comp_obj] at h ⊢
  point_structural_exact h

end AlgebraicGeometry.ProEtale
