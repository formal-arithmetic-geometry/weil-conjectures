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
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.Paper.BoundaryCechInjectiveMiddle
import Sheaf.Paper.PQFCohomology

/-!
# The Čech local-lift representative computes the connecting boundary

Source: Stacks Project, Cohomology of Sheaves, Lemma 0B8S, local-lift description of the
boundary, with Lemma 01EQ for the Čech-to-cohomology map
(blueprint: lem-sc-boundary-cech-compatibility).
-/

@[expose] public section

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- (blueprint: lem-sc-boundary-cech-compatibility) Let `0 → A → B → C → 0` be a short exact
sequence `S` of `O_X`-modules on a scheme `X`, `U` an open covering, `s` a global section of
`C` and `t i ∈ B(U i)` lifts of `s|_{U i}`. Then the differences
`t_{i₁}|_{U_{i₀} ∩ U_{i₁}} - t_{i₀}|_{U_{i₀} ∩ U_{i₁}}` are the images of the components of a
Čech `1`-cocycle `z` with values in `A` (unique, as `A → B` is injective on sections), and the
canonical comparison map `c_A : Ȟ¹(U, A) → H¹(X, A)` (any `c` with `IsModuleCechComparison`)
sends the class of `z` to the connecting class `∂(s)` of the long exact cohomology sequence
of `S`, where `∂` is `RingedSpace.moduleCohomologyBoundary` and `s` is read in `H⁰(X, C)`
through `toRightDerivedZero`. Source: Stacks, Cohomology, Lemma 0B8S, local-lift paragraph;
Lemma 01EQ.

Proof:
1. Choose a monomorphism `A → I` into an injective `O_X`-module
(lem-weil-pbc-scheme-modules-enough-injectives). Injectivity extends it across `A → B` to
`φ : B → I`. With `Q = coker(A → I)`, `φ` induces `ψ : C → Q`, and `(id_A, φ, ψ)` is a morphism
from `0 → A → B → C → 0` to `0 → A → I → Q → 0`. Naturality of the connecting maps of the
universal δ-functor (lem-weil-pbc-right-derived-universal-delta-functor) gives
`∂_B(s) = ∂_I(ψ(s))`.
2. The sections `φ(t_i)` are local lifts of `ψ(s)` in `I`. As `φ` restricts to the chosen
inclusion `A → I`, their pairwise differences are the image in `I` of `t_{i₁} - t_{i₀}`: the
`A`-valued Čech cocycle of the original sequence and that of the injective sequence coincide
(def-weil-pbc-site-cech-complex).
3. Apply lem-sc-boundary-cech-injective-middle to `0 → A → I → Q → 0`, `q = ψ(s)` and the lifts
`φ(t_i)`: `c_A([t_{i₁} - t_{i₀}]) = ∂_I(ψ(s))`, which is `∂_B(s)` by Step 1. -/
theorem boundary_cech_compatibility (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj S.X₁)
    (hc : IsModuleCechComparison U S.X₁ 1 c)
    (s : S.X₃.val.obj (op ⊤)) (t : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (ht : ∀ i : ι, S.g.val.app (op (U i)) (t i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s) :
    ∃ z : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1,
      (∀ y : Fin 2 → ι,
        S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          ((Pi.π (fun w : Fin 2 → ι ↦
            S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
            (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (t (y 1)) -
            S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (t (y 0))) ∧
      c (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
