/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.NotPreservesCoproducts
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtPullbackHom

/-!
# The pushforward of an elliptic curve does not preserve countable coproducts

Blueprint `sk-rem-sf-fullcd-scope` (ii): for the structure morphism `a_E : E ⟶ Spec k` of an
elliptic curve (more generally an abelian variety of positive dimension) over an algebraically
closed field `k`, `Ra_{E*}` does not preserve countable coproducts on `D(E_proét, Λ)`, so
`Ra_{E!} ≅ Ra_{E*}` has no right adjoint.

Let `F` be the sheaf of
`AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar`, with
`Extⁿ(Λ_E, F) ≠ 0` for `n ≥ 1`, and `Kₙ = F[n]`. These classes give nonzero morphisms
`Λ[0] ⟶ (Ra_{E*} F)[n]` on `Spec k`
(`AlgebraicGeometry.ProEtale.exists_forall_hom_ne_zero_rightDerivedLowerStar`). Since countable
products of pro-étale sheaves are exact, `⊕ Kₙ` is also the product of the `Kₙ` in
`D(E_proét, Λ)`, and the right adjoint `Ra_{E*}` preserves this product. On the other hand
`Λ[0]` is compact in `D((Spec k)_proét, Λ)`: morphisms out of it are global sections of `H⁰`,
which commute with coproducts (`DerivedCategory.exists_finset_forall_comp_eq_zero`). A morphism
`Λ[0] ⟶ ∏ Ra_{E*} Kₙ` with all components nonzero then shows that `Ra_{E*}` does not preserve
the coproduct of the `Kₙ` (`DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero`).

## Main statements

- `AlgebraicGeometry.ProEtale.exists_forall_hom_ne_zero_rightDerivedLowerStar`.
- `not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`: `Ra_{E*}` does not
  preserve countable coproducts.
- `AlgebraicGeometry.ProEtale.not_isLeftAdjoint_rightDerivedLowerShriek_of_isAbelianVariety`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (Λ : Type (u + 1)) [Field Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]

/-- For an elliptic curve (more generally an abelian variety of positive dimension) `E` over an
algebraically closed field `k` and a field `Λ`, there is a pro-étale sheaf `F` of `Λ`-modules on
`E` such that for every `n ≥ 1` there is a nonzero morphism `Λ[0] ⟶ (Ra_{E*} F)[n]` in
`D((Spec k)_proét, Λ)`.

As in `AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar`,
`F = V(Λ)` for the exact evaluation functor `U ⊣ V` of
`AlgebraicGeometry.ProEtale.exists_exact_evaluation` has `Extⁿ(Λ_E, F) ≠ 0` for `n ≥ 1`, and
these classes give nonzero morphisms `Λ[0] ⟶ (Ra_{E*} F)[n]`
(`AlgebraicGeometry.ProEtale.hom_ne_zero_of_ext_ne_zero`). -/
theorem exists_forall_hom_ne_zero_rightDerivedLowerStar (hE : 0 < IsAbelianVariety.dim E) :
    ∃ F : Sheaf (Scheme.ProEt.topology E.left) (ModuleCat.{u + 1} Λ), ∀ n : ℕ,
      ∃ φ : (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ)) ⟶
        ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))⟦((n + 1 : ℕ) : ℤ)⟧, φ ≠ 0 := by
  obtain ⟨U, V, adj, _, _, _, _, _, _, ⟨eU⟩⟩ := exists_exact_evaluation Λ E hE
  let H := Multiplicative (ULift.{u + 1} ℕ →₀ ℤ)
  let triv := Rep.trivial Λ H Λ
  let Λk := (constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ Λ)
  have : LocallySmall.{u + 1} (Rep.{u + 1} Λ H) := locallySmall_self _
  have : EnoughProjectives (Rep.{u + 1} Λ H) :=
    Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{u + 1}
  let : HasExt.{u + 1} (Rep.{u + 1} Λ H) := hasExt_of_enoughProjectives _
  have : EnoughInjectives (Rep.{u + 1} Λ H) :=
    Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.2
      (ModuleCat.enoughInjectives.{u + 1} (MonoidAlgebra Λ H))
  refine ⟨V.obj triv, fun m ↦ ?_⟩
  obtain ⟨x, hx⟩ := groupCohomology.exists_ext_ne_zero_finsupp (k := Λ) (ULift.{u + 1} ℕ) m
  -- transport `x` along `U Λ_E ≅ Λ`
  let y : Abelian.Ext (U.obj ((E.hom)^*[ModuleCat.{u + 1} Λ].obj Λk)) triv (m + 1) :=
    (Abelian.Ext.mk₀ eU.hom).comp x (zero_add _)
  have hy : y ≠ 0 := fun h ↦ hx (by
    have := congrArg (fun z ↦ (Abelian.Ext.mk₀ eU.inv).comp z (zero_add _)) h
    simp only [y, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.comp_zero] at this
    exact this)
  obtain ⟨z, hz⟩ := (adj.mapExtCounit_bijective _ triv (m + 1)).2 y
  refine hom_ne_zero_of_ext_ne_zero (ModuleCat.{u + 1} Λ) E.hom Λk (V.obj triv) (m + 1) z
    fun h ↦ hy ?_
  rw [← hz, h, map_zero]

-- the instances `HasSheafCompose` and `PreservesSheafification` on the small pro-étale site
-- take long to synthesize
/-- Blueprint `sk-rem-sf-fullcd-scope` (ii): for the structure morphism `a_E` of an elliptic
curve (more generally an abelian variety of positive dimension) over an algebraically closed
field, `Ra_{E*}` does not preserve countable coproducts on `D(E_proét, Λ)`.

With `F` the sheaf of
`AlgebraicGeometry.ProEtale.exists_forall_not_isZero_homology_rightDerivedLowerStar` and
`Kₙ = F[n]`, countable products and coproducts of pro-étale sheaves are exact, so
`⊕ Kₙ ≅ ∏ Kₙ`, while in degree `0` the coproduct comparison for `Ra_{E*}` is the non-surjective
map `⊕_{n ≥ 1} Hⁿ(E, F) ⟶ ∏_{n ≥ 1} Hⁿ(E, F)`. -/
theorem not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ PreservesColimitsOfShape (Discrete ℕ) (R((E.hom)_*[ModuleCat.{u + 1} Λ])) := by
  have := projective_constantSheaf_spec Λ k
  have := preservesColimitsOfShape_sheafSections_of_iso (A := ModuleCat.{u + 1} Λ)
    (Iso.refl (Spec (.of k))) (Discrete ℕ)
  have : PreservesColimitsOfShape (Discrete ℕ)
      (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
    preservesColimitsOfShape_of_natIso
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId _)).symm
  -- exactness of countable coproducts of sheaves on `Spec k`, obtained from `AB5` by shrinking
  -- universes (instance search cannot guess the intermediate universe)
  have : HasExactColimitsOfShape (Discrete ℕ)
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
    have : HasFiniteBiproducts
        (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    have := AB5OfSize_of_univLE.{0, 0, u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ))
    (AB4.of_AB5.{0} _).ofShape ℕ
  have := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) E.hom).isRightAdjoint
  obtain ⟨F, hF⟩ := exists_forall_hom_ne_zero_rightDerivedLowerStar Λ E hE
  refine DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero
    (R((E.hom)_*[ModuleCat.{u + 1} Λ])) ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Scheme.ProEt.topology (Spec (.of k))) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))) (fun hc π hπ φ ↦ ?_) F fun n ↦ ?_
  · exact DerivedCategory.exists_finset_forall_comp_eq_zero (constantSheafΓAdj _ _) hc π hπ φ
  obtain ⟨φ, hφ⟩ := hF n
  refine ⟨φ ≫ ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).commShiftIso ((n + 1 : ℕ) : ℤ)).inv.app _,
    fun h ↦ hφ ?_⟩
  simpa using h =≫ ((R((E.hom)_*[ModuleCat.{u + 1} Λ])).commShiftIso ((n + 1 : ℕ) : ℤ)).hom.app _

end ProEtale

end AlgebraicGeometry

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
  let name := `AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety
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
