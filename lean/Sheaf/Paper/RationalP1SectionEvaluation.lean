/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.RationalP1AmbientComposites
public import Sheaf.Paper.RationalTatePullback
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems

/-! # Evaluating an arbitrary kernel on the projective diagonal

Source: the first identity in the rational projective-line triangle proof, the section
and projection calculation after the trace has been transported to the first projection.
(blueprint: lem-sfb-rational-p1-section-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

/-- Change the second direct-image path to the first by conjugating the canonical
pullback comparison. Source: blueprint First identity, `Rq_*Rp₂* = Rq_*Rp₁*`
(blueprint: lem-sfb-rational-p1-section-evaluation). -/
@[irreducible]
def firstPathComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    moduleObjectDerivedPushforward Λ (secondProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) ≅
      moduleObjectDerivedPushforward Λ (firstProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) := by
  unfold moduleObjectDerivedPushforward
  exact (conjugateIsoEquiv
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y)))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y)))
    (condensedAmbientPullbackComparison Λ (square Y))).symm

/-- Express a diagram functional in the fixed native first direct image.
Source: the full-unit-normalized derived model in the First identity
(blueprint: lem-sfb-rational-p1-section-evaluation). -/
@[irreducible]
def firstNativeFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y)) :
    (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N ⟶
      unit Λ (ProjectiveLine Y) := by
  unfold moduleObjectDerivedPushforward firstProjection
  exact (eqToIso d.p₁_canonical).inv.app N ≫ t

set_option maxHeartbeats 800000 in
-- Keep the native functor sources fixed while constructing the prefix.
/-- The supported-kernel insertion, with its source and target fixed before direct image.
Source: blueprint First identity, the section followed by the diagonal tensor comparison
(blueprint: lem-sfb-rational-p1-section-evaluation). This is the literal section paste,
followed by the second direct image of the tensor comparison and the supported kernel arrow. -/
@[irreducible]
def firstKernelInsertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N) :
    M ⟶ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) :=
  (pushSectionIso Λ Y).hom.app M ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      ((diagonalTensorIso Λ Y M).hom ≫
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
          ((supportedUnitIso Λ Y).hom ≫ α)))

set_option maxHeartbeats 800000 in
-- The terminal functional has the native path objects as its declared endpoints.
/-- Change direct-image paths and evaluate a first-projection functional.
Source: blueprint First identity, the functional after trace base change
(blueprint: lem-sfb-rational-p1-section-evaluation). The arrows are the conjugate path
comparison, the inverse projection, identity tensor the given native functional,
identity tensor singleUnitIso, and the right unitor, in that order. -/
@[irreducible]
def firstTerminalFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N)) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M :=
  (firstPathComparison Λ Y).hom.app
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) ≫
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp ≫
        (M ◁ firstNativeFunctional Λ Y L d N t) ≫
        (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom)

attribute [local irreducible] coefficient line diagram secondLineComparison

set_option maxHeartbeats 800000 in
-- Elaborate the native projection and the two canonical direct-image paths.
/-- The section/projection paste before the terminal unitors.
Source: the first identity in the rational projective-line triangle proof, with the
terminal unitors omitted (blueprint: lem-sfb-rational-p1-section-evaluation-core).
Proof: path-comparison naturality moves the kernel insertion across the path change;
projectionMap naturality cancels the specified inverse first projection. The diagonal
section identity leaves the normalized supported arrow followed by the native
functional. -/
theorem first_section_tensor_evaluation_core
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X)
    (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      (firstPathComparison (coefficient l c).X Y).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗ N) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap (coefficient l c).X (firstProjection Y) M N) hp) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstNativeFunctional (coefficient l c).X Y L d N t) =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫ t)) := by sorry

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/- The structural instance comparison follows the proved congruence procedure in
Sheaf.Paper.FiniteCoefficientProperFormulaTools (G3). All produced terms are built from
HEq reflexivity, proof irrelevance, function extensionality and congruence theorems. -/
private theorem coefficientPiEq {α β : Sort u₁} {P : α → Sort u₂}
    {Q : β → Sort u₂} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

open Lean Meta Elab Tactic in
private meta partial def coefficientHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← coefficientHEq (body.instantiate1 x) (body'.instantiate1 y) next
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
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← coefficientHEq P Q next
      let h ← mkAppOptM ``coefficientPiEq #[some α, some β, some P, some Q,
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
      return ← coefficientHEq lhs' rhs' next
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let init ← get
      try
        let mut found := none
        for (ff, arity, thm) in (← get).congrs do
          if ff == f && arity == xs.size then found := some thm
        let thm? ← match found with
          | some thm => pure (some thm)
          | none => do
            let thm? ← if let .const name levels := f then
              mkHCongrWithArityForConst? name levels xs.size
            else
              try pure (some (← mkHCongrWithArity f xs.size))
              catch _ => pure none
            if let some thm := thm? then
              modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
            pure thm?
        if let some thm := thm? then
          let mut args := #[]
          for i in [:xs.size] do
            let h ← coefficientHEq xs[i]! ys[i]! next
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
            return ← coefficientHEq lhs' rhs' next
      -- Some wrappers ignore parameters. If argumentwise congruence fails, unfold
      -- the wrapper below and compare its values instead.
      catch _ => set init
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

open Lean Meta Elab Tactic in
local elab "section_evaluation_exact " t:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let val ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let val ← instantiateMVars val
  let actual ← inferType val
  let (h, _) ← (coefficientHEq actual target).run {}
  let result ← mkAppM ``Eq.mp #[← mkEqOfHEq h, val]
  goal.assign result
  replaceMainGoal []

private theorem finish_tensor_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (R : C ⥤ D) (M V U : C) {A : D} {Z U₀ U₁ U₂ : C}
    (a : R.obj M ⟶ A) (b : A ⟶ R.obj Z) (p : Z ⟶ M ⊗ V)
    (f : V ⟶ U) (k₀ : 𝟙_ C ⟶ U₀) (k₁ : U₀ ⟶ U₁)
    (k₂ : U₁ ⟶ U₂) (k₃ : U₂ ⟶ U) (e : U ≅ 𝟙_ C)
    (h : a ≫ b ≫ R.map p ≫ R.map (M ◁ f) =
      R.map (ρ_ M).inv ≫ R.map (M ◁ (k₀ ≫ k₁ ≫ k₂ ≫ k₃))) :
    a ≫ b ≫ R.map (p ≫ (M ◁ f) ≫ (M ◁ e.hom) ≫ (ρ_ M).hom) =
      R.map ((ρ_ M).inv ≫ (M ◁ (k₀ ≫ k₁ ≫ k₂ ≫ k₃ ≫ e.hom)) ≫ (ρ_ M).hom) := by
  have h' := congrArg (fun z ↦ z ≫ R.map (M ◁ e.hom) ≫ R.map (ρ_ M).hom) h
  simpa only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc] using h'


/-- The section calculation with an arbitrary kernel arrow and an arbitrary functional.
It uses neither a Tate pullback comparison nor a trace base-change equation. In particular,
no integration equation for `d` is used.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity, final three sentences
(blueprint: lem-sfb-rational-p1-section-evaluation).

Proof: apply the existing pre-unitor evaluation to the arbitrary kernel and functional.
Postcompose it by the direct image of identity_M tensor singleUnitIso.hom, and then by
the right unitor. Functoriality, tensor functoriality and associativity combine the
resulting word into the displayed right-hand side. These elementary rewrites take
place in the proved private categorical helper. Explicit congruence proofs identify
the native instance expressions with that helper's expressions, avoiding expensive
kernel conversion. The argument works for zero kernels and zero functionals and uses
invertibility only of the specified projection at N. -/
theorem first_section_tensor_evaluation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X) (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      firstTerminalFunctional (coefficient l c).X Y L d M N t hp =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      ((ρ_ M).inv ≫ (M ◁
        ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
          d.R₁.R.map α ≫ t ≫ (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ M).hom) := by
  delta firstTerminalFunctional
  section_evaluation_exact finish_tensor_evaluation
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)) M
    ((moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj N)
    (unit (coefficient l c).X (ProjectiveLine Y))
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (firstKernelInsertion (coefficient l c).X Y M N α))
    ((firstPathComparison (coefficient l c).X Y).hom.app
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗ N))
    (@inv _ _ _ _ (projectionMap (coefficient l c).X (firstProjection Y) M N) hp)
    (firstNativeFunctional (coefficient l c).X Y L d N t)
    (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv
    d.support₁.hom (d.R₁.R.map α) t
    (singleUnitIso (coefficient l c).X (ProjectiveLine Y))
    (first_section_tensor_evaluation_core l c Y L d M N α t hp)

end AlgebraicGeometry.ProEtale.RationalP1
