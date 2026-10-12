/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison
public import Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Sheaf.CategoryTheory.Abelian.HorseshoeResolutions
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.PQFCohomology

/-!
# Injective middle term: the Čech local-lift cocycle is the connecting class

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ (proof via the double complex and
the maps `β` and `α⁻¹`) with Lemma 01EP, and the local-lift paragraph of Lemma 0B8S
(blueprint: lem-sc-boundary-cech-injective-middle).
-/

@[expose] public section

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- (blueprint: lem-sc-boundary-cech-injective-middle) Let `0 → A → I → Q → 0` be a short exact
sequence `S` of `O_X`-modules on a scheme `X` with `I = S.X₂` injective, `U` an open covering,
`q` a global section of `Q` and `x i ∈ I(U i)` lifts of `q|_{U i}`. Then the differences
`x_{i₁}|_{U_{i₀} ∩ U_{i₁}} - x_{i₀}|_{U_{i₀} ∩ U_{i₁}}` are the images of the components of a
Čech `1`-cocycle `z` with values in `A` (unique, as `A → I` is injective on sections), and the
canonical comparison map `c_A : Ȟ¹(U, A) → H¹(X, A)` (any `c` with `IsModuleCechComparison`)
sends the class of `z` to the connecting class `∂(q)` of `S`, where `∂` is
`RingedSpace.moduleCohomologyBoundary` and `q` is read in `H⁰(X, Q)` through
`toRightDerivedZero`. Source: Stacks, Cohomology, Lemma 01EQ with 01EP; Lemma 0B8S, local-lift
paragraph.

Proof:
1. On `U_{i₀} ∩ U_{i₁}` the image of `x_{i₁} - x_{i₀}` in `Q` is `q - q = 0`, so by exactness
the difference lies in `A`. On a triple overlap the alternating sum
`(x_{i₂} - x_{i₁}) - (x_{i₂} - x_{i₀}) + (x_{i₁} - x_{i₀})` vanishes, so the differences form a
Čech `1`-cocycle for the differential of def-weil-pbc-site-cech-complex.
2. By lem-sc-cech-comparison-map-naturality, for an injective resolution `A → J^•` the total
complex of the Čech double complex receives `α_A` from global sections, a quasi-isomorphism,
and `β_A` from the Čech complex, and `c_A` is `H¹(α_A)⁻¹ ∘ H¹(β_A)` followed by
`H¹(Γ(X, J^•)) = H¹(X, A)`.
3. As `I` is injective and `A → I` is a monomorphism, choose an injective resolution
`A → J^•` with `J⁰ = I` (lem-weil-pbc-scheme-modules-enough-injectives). Then
`Q = I / A ≅ im(d⁰) ⊆ J¹`, and `K^n = J^{n+1}` with differential `-d` is an injective
resolution of `Q`. Let `q̃ ∈ J¹(X)` be the image of `q`; then `d(x_i) = q̃|_{U_i}`. The horseshoe
`I_B^n = J^n ⊕ J^{n+1}`, `d_B(a, b) = (da - b, -db)`, resolves `I` and gives a horseshoe
resolution of `S` (lem-weil-pbc-horseshoe-delta-functor, lem-weil-pbc-injective-resolution-ses);
the snake computes `∂(q) = -[q̃]` in `H¹(Γ(X, J^•))`, transported to `H¹(X, A)` by
lem-weil-pbc-derived-functor-map-via-lift. In the total complex (def-sp-double-complex-total)
the `0`-cochain `(x_i)` of `Čech⁰(U, J⁰)` has total differential
`(x_{i₁} - x_{i₀}) + (q̃|_{U_i}) = β_A(z) + α_A(q̃)`. Hence `H¹(β_A)[z] = -H¹(α_A)[q̃]`, and by
Step 2 `c_A[z] = -[q̃] = ∂(q)`. -/
theorem boundary_cech_injective_middle (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [Injective S.X₂]
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj S.X₁)
    (hc : IsModuleCechComparison U S.X₁ 1 c)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q) :
    ∃ z : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1,
      (∀ y : Fin 2 → ι,
        S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          ((Pi.π (fun w : Fin 2 → ι ↦
            S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
            (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
            S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) ∧
      c (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
