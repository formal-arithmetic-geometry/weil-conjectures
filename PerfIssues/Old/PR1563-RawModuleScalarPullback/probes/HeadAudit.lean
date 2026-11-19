/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # Module raw pullback factorization
Source: Stacks Project, Tags 03FD and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- A raw triangle map whose functors are precomposed with `L` is the composite of any morphism
equal to its source, the image of the class, and the coefficient. Being stated over arbitrary
categories, its associativity step is cheap to check. -/
private theorem rawTriangleMap_whiskerLeft_eq_comp
    {C₀ C D E D' E' : Type*} [Category C₀] [Category C] [Category D] [Category E]
    [Category D'] [Category E'] [Preadditive D'] [Preadditive E']
    (L : C₀ ⥤ C) (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C₀) {K : D'} {K' : E'}
    (z : (((L ⋙ H) ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U)) (s : F.obj K ⟶ K')
    (src : B.obj (H'.obj (L.obj U)) ⟶ F.obj (A.obj (H.obj (L.obj U))))
    (hsrc : rawTriangleSource H H' P A B F c e (L.obj U) = src) :
    rawTriangleMap (L ⋙ H) (L ⋙ H') P A B F (Functor.whiskerLeft L c) e U z s =
      src ≫ F.map z ≫ s := by
  subst hsrc
  exact (Category.assoc _ _ _).symm

/-- The module formula for the raw pullback itself, stated over `B` rather than through the
functor `higherDirectImageRawOverFunctor`. Keeping this a separate declaration keeps the
`unop (op B)` objects of the functor out of the kernel check of the associativity step.
The proof instantiates `rawTriangleMap_whiskerLeft_eq_comp` with explicit arguments, so the
kernel matches `higherDirectImageRawOverPullback` and `moduleSourceFactor` against
`rawTriangleMap` and `rawTriangleSource` argument by argument, instead of unfolding composites
in the derived category. -/
private theorem higherDirectImageRawOverPullback_eq_moduleFactors
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    {A B : Over W} (f : A ⟶ B)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q f U z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G q A B f :=
  rawTriangleMap_whiskerLeft_eq_comp (freeSheaf Λ S)
    (upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k)) (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k))
    (upperStar (ModuleCat.{u + 1} Λ) f.left)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
      (show f.left ≫ B.hom ≫ k = A.hom ≫ k by rw [← Category.assoc, Over.w]).symm).hom
    ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).inv U z
    (moduleCoefficientFactor Λ G q A B f) _ rfl

/-- The module raw map is the composite of its source, class, and coefficient factors.
Source: Stacks Project, Tags 03FD and 03Q8, explicit-map expansion in the proof of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-module-formula).

Proof: The object and map fields of higherDirectImageRawOverFunctor give the raw
presheaf value and higherDirectImageRawOverPullbackHom. Evaluate the latter using
higherDirectImageRawOverPullbackHom_apply. Unfold higherDirectImageRawOverPullback,
higherDirectImageRawTrianglePullback, and rawTriangleMap. The source is the single
functor applied to the upperStarComp hom, followed by the inverse single comparison;
these are exactly moduleSourceFactor. The coefficient is the shift comparison followed
by the shifted higherDirectImageRawOverCoefficient. Expand that named coefficient to
its single comparison and single of the inverse upperStarComp; these are exactly
moduleCoefficientFactor. Category.assoc regroups the first two maps and retains the
middle derived image of z and the last two maps. Proof irrelevance identifies the two
proofs of the Over triangle. No scalar-forgetting square or relation to an abelian
class is used. This also covers q = 0, z = 0, and identity f. -/
theorem rawModuleScalar_pullback_module_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
      moduleCoefficientFactor Λ G (q : ℤ) A B f) := by
  simp only [higherDirectImageRawOverFunctor,
    higherDirectImageRawOverPullbackHom_apply, higherDirectImageRawOverPullback,
    higherDirectImageRawTrianglePullback, rawTriangleMap, moduleSourceFactor,
    rawTriangleSource, moduleCoefficientFactor, Category.assoc]; rfl

end AlgebraicGeometry.Etale

open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 100000

private def auditShape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .mdata .. => "metadata"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private def auditHint : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular height {h}"

private def auditDescribe (label : String) (e : Expr) : MetaM Unit := do
  let args := e.getAppArgs
  let head := e.getAppFn
  logInfo m!"{label}: outer={auditShape e}; head={auditShape head}; args={args.size}"
  match head with
  | .const n ls =>
    logInfo m!"{label}: universes {ls}"
    match (← getConstInfo n) with
    | .defnInfo d =>
      logInfo m!"{label}: definition, Kernel hint {auditHint d.hints}, body outer={auditShape d.value}, body head={auditShape d.value.getAppFn}"
    | .thmInfo _ => logInfo m!"{label}: theorem"
    | .axiomInfo _ => logInfo m!"{label}: axiom"
    | _ => logInfo m!"{label}: other declaration kind"
  | .proj n i major =>
    logInfo m!"{label}: projection {n}.{i}, major outer={auditShape major}, major head={auditShape major.getAppFn}"
  | _ => pure ()
  for i in [:min args.size 32] do
    let a := args[i]!
    logInfo m!"{label}: arg {i} outer={auditShape a}, head={auditShape a.getAppFn}"

private partial def auditFirstDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (auditFirstDiff f g (path ++ ".fn")).orElse fun _ =>
        auditFirstDiff x y (path ++ ".arg")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .lam _ da ba _, .lam _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (auditFirstDiff ta tb (path ++ ".type")).orElse fun _ =>
        (auditFirstDiff va vb (path ++ ".value")).orElse fun _ =>
          auditFirstDiff ba bb (path ++ ".body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then auditFirstDiff ea eb (path ++ ".proj")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => auditFirstDiff ea eb (path ++ ".mdata")
    | _, _ => some (path, a, b)

private partial def auditStripLambdas (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ body _ => auditStripLambdas body (n + 1)
  | _ => (n, e)

private partial def auditStripForalls (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .forallE _ _ body _ => auditStripForalls body (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  logInfo m!"AUDIT declaration {name}; original value and declared type read from the current environment"
  let start ← IO.monoMsNow
  let result := Kernel.check env {} value
  let stop ← IO.monoMsNow
  logInfo m!"Kernel.check(value) {stop - start} ms"
  match result with
  | .error _ => logInfo m!"value replay failed"
  | .ok inferred =>
    auditDescribe "actual inferred type" inferred
    auditDescribe "expected declared type" info.type
    let (actualBinders, actualResult) := auditStripForalls inferred
    let (expectedBinders, expectedResult) := auditStripForalls info.type
    logInfo m!"result binders actual={actualBinders}, expected={expectedBinders}"
    auditDescribe "actual result" actualResult
    auditDescribe "expected result" expectedResult
    let startEq ← IO.monoMsNow
    let equal := Kernel.isDefEq env {} inferred info.type
    let stopEq ← IO.monoMsNow
    logInfo m!"final conversion={stopEq - startEq} ms, result={match equal with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
    match auditFirstDiff inferred info.type with
    | none => logInfo m!"final type pair structurally identical"
    | some (path, a, b) =>
      logInfo m!"first structural divergence {path}"
      auditDescribe "divergence actual" a
      auditDescribe "divergence expected" b
  let (binders, body) := auditStripLambdas value
  logInfo m!"value binders {binders}"
  auditDescribe "value body" body
