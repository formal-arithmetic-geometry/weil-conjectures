/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Base change for individual affine Čech coefficients

Source: Stacks Project, Tag 02KE, the affine coefficient calculation. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Individual affine intersection coefficients have natural base-change section
coordinates. No products of coefficients, extended complexes, or differentials occur.
Source: Stacks Project, Tag 02KE, Lemma 30.5.1 and the termwise calculation in
Lemma 30.5.2; Tags 01I9 and 01IA for affine quasi-coherent sections.
(blueprint: lem-pc-finite-affine-cech-coefficient-base-change).

Proof: Separatedness over the affine U makes each nonempty finite intersection Z of
the V_i affine. The cartesian square identifies the intersection of the W_i with the
base change of Z. Its map to T' is affine by the intersection base-change theorem.
Over an affine B, its sections are Gamma(B,O) tensor over Gamma(U,O) Gamma(Z,F).
The tilde, scalar restriction, and the two pullbacks in H give this same module by
associativity of tensor products and the affine pullback section formula. Identify
these modules by the map sending b tensor s to b times the pullback of s. This map
is invertible by the affine section formula. Naturality of the pullback unit gives
commutation with face restrictions and with restrictions of B; multiplication on the
first tensor factor gives the scalar equation. These equations hold on pure tensors,
hence on all sections by additivity. Restrict to affine subopens of overlaps to check
agreement and glue the maps and their inverses using the sheaf axiom. The three
identities are local and so hold on every B. Empty intersections give zero modules;
when there is no increasing tuple, there is no coefficient assertion to check. -/
theorem finiteAffineCech_coefficient_baseChange {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W₀ i = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    ∃ c : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r) (B : T'.Opens),
      Γ(H.obj (G.obj (op (alternatingCechIntersection V t))), B) ≃+
        Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B),
      (∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V t))), C)),
        c p t B ((H.obj (G.obj (op (alternatingCechIntersection V t)))).presheaf.map
          i.op s) = M.presheaf.map (homOfLE (inf_le_inf le_rfl
            ((TopologicalSpace.Opens.map f'.base).map i).le)).op (c p t C s)) ∧
      (∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V t))), B)),
        c p t B (b • s) =
          X'.presheaf.map (homOfLE (show
            alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
              from inf_le_right)).op (f'.app B b) • c p t B s) ∧
      (∀ (p : ℕ) (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) (B : T'.Opens)
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V
          ((Fin.succAboveOrderEmb j).trans t)))), B)),
        c (p + 1) t B
          ((H.map (G.map (homOfLE
            (alternatingCechIntersection_face_le V p t j)).op)).app B s) =
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (c p ((Fin.succAboveOrderEmb j).trans t) B s)) := by sorry

end AlgebraicGeometry.Scheme.Modules
