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
set_option maxHeartbeats 10000000

private def appHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar {i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | _ => "other"

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula
  let startIndex : Nat := 0
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    logInfo m!"{name}: binders={xs.size}, body head={appHead body}, args={args.size}"
    let mut appSoFar := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      if i >= startIndex then
        let startArg ← IO.monoMsNow
        let argResult := Kernel.check env lctx arg
        let stopArg ← IO.monoMsNow
        let startFn ← IO.monoMsNow
        let fnResult := Kernel.check env lctx appSoFar
        let stopFn ← IO.monoMsNow
        match argResult, fnResult with
        | .ok actual, .ok fnType =>
          match Kernel.whnf env lctx fnType with
          | .ok (.forallE _ expected _ _) =>
            logInfo m!"arg {i}: term={appHead arg}, actual type={appHead actual}, expected domain={appHead expected}, structurally equal={actual == expected}"
            let startEq ← IO.monoMsNow
            let result := Kernel.isDefEq env lctx actual expected
            let stopEq ← IO.monoMsNow
            logInfo m!"arg {i}: own check={stopArg - startArg} ms, prefix check={stopFn - startFn} ms, domain conversion={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
          | _ => logInfo m!"arg {i}: function type not Pi"
        | _, _ => logInfo m!"arg {i}: argument or prefix failed Kernel.check"
      appSoFar := mkApp appSoFar arg
