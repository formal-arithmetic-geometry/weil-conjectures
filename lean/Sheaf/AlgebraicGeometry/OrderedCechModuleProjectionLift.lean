/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.OrderedCechModuleCoordinates
public import Mathlib.GroupTheory.Perm.Sign
import Sheaf.AlgebraicGeometry.SignedCechExtension

/-! # Signed projection of module Čech cochains

Source: Stacks Project, Tags 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- All-tuple coordinate, with the actual extension transport.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-module-projection-lift). -/
noncomputable def orderedCechFullCoordinate {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : T'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
    (s : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B)) :
    Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ f' ⁻¹ᵁ B) :=
  (((e p).hom ≫ Pi.π (fun z : Fin (p + 1) → ULift.{u} (Fin r) ↦
    ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
        (op (∏ᶜ fun l ↦ W₀ (z l)))) y).app (op (f' ⁻¹ᵁ B)))
    (((((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
      ComplexShape.embeddingUpNat (i := p) rfl).hom.app B s)

/-- Restrict an ordered coordinate back to an arbitrary permuted full tuple.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-module-projection-lift). -/
noncomputable def orderedCechProjectionOpenMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens)
    (y : Fin (p + 1) → ULift.{u} (Fin r)) (σ : Equiv.Perm (Fin (p + 1)))
    (h : StrictMono (fun l ↦ (y (σ l)).down)) :
    (∏ᶜ fun l ↦ W (y l)) ⨯ B ⟶
      alternatingCechIntersection (fun i ↦ W ⟨i⟩) (OrderEmbedding.ofStrictMono _ h) ⊓ B :=
  homOfLE (le_inf (le_iInf fun l ↦
    (prod.fst ≫ Pi.π (fun k ↦ W (y k)) (σ l)).le) prod.snd.le)

/-- The finite signed extension formula characterizes the projection completely.
Source: Stacks 01FK and 01FM.
(blueprint: lem-pc-ordered-cech-module-projection-lift). -/
def IsOrderedCechModuleProjection {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)) : Prop :=
  ∀ (p : ℕ) (B : T'.Opens) (s : Γ(((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
    (y : Fin (p + 1) → ULift.{u} (Fin r)),
    orderedCechFullCoordinate f' M W₀ D e p B y ((P.f (p : ℤ)).app B s) =
      ∑ σ : Equiv.Perm (Fin (p + 1)),
        if h : StrictMono (fun l ↦ (y (σ l)).down) then
          (Equiv.Perm.sign σ : ℤ) •
            M.presheaf.map (orderedCechProjectionOpenMap W₀ (f' ⁻¹ᵁ B) y σ h).op
              (orderedCechModuleCoordinate f' M W₀ D e p B
                (OrderEmbedding.ofStrictMono _ h) s)
        else 0

/-- Signed extension lifts to a cochain endomorphism of module sheaves.
Source: Stacks 01FK, signed extension; 01FM, the map cπ.
(blueprint: lem-pc-ordered-cech-module-projection-lift).

Proof: In each natural degree use the displayed finite permutation sum and transport
by e inverse to define the section map. Naturality of e and functoriality of restrictions
make it natural in the open. The local scalar equation hlinear, in each summand, makes
it linear over the local ring: the two scalar restrictions agree in the poset of opens.
Consequently it defines a module-sheaf map. Identify the filtered sum with
signedCechExtension: an injective tuple has exactly one increasing sorting permutation,
and a repeated tuple has none. Apply signedCechExtension_differential to commute
signed extension with the face differential, and hd to transport this equation to D.
Push forward and extend by zero; all negative
components and boundary equations are zero. Evaluation gives precisely the formula.
Empty families and degrees exceeding r have zero projection, by the strict filter. -/
theorem orderedCech_module_projection_exists {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s)
    : ∃ P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat),
      IsOrderedCechModuleProjection f' M W₀ D e P := by sorry

end AlgebraicGeometry.Scheme.Modules
