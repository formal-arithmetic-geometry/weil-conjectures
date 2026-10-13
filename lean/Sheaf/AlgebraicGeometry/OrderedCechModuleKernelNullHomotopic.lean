/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.OrderedCechModuleCoordinates
public import Mathlib.Algebra.Homology.Homotopy

/-! # Null homotopy for the module-valued ordered kernel

Source: Stacks Project, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- An endomorphism of the usual presentation vanishing on increasing coordinates
is null homotopic as a morphism of module-sheaf complexes. No ordered complex is given.
Source: Stacks Project, Tag 01FM, equations 20.23.6.1 and 20.23.6.2.
(blueprint: lem-pc-ordered-cech-module-kernel-null-homotopic).

Proof: On each inverse-image open identify D by e with full tuple cochains.
Use the explicit first and second sorting families already defined for additive
Cech cochains. The first boundary is identity minus stable sorting. The second
boundary is stable sorting minus signed extension of increasing restriction.
Their sum L therefore has boundary identity minus the alternating projection P.
Precompose L with g. Since g is a cochain map, the boundary of L after g is
(identity minus P) after g. The displayed coordinate vanishing makes P after g
zero: each nonzero projection summand evaluates g on an increasing tuple, and
all other summands are zero by their filters. Thus the boundary is g.
The operators are finite sums of restrictions with integer coefficients, so
naturality of e makes them commute with restriction of the base open. Every
summand restricts the same local scalar to the same intersection; hlinear gives
local linearity, including after pullback of a scalar along f'. Hence transport
by e assembles actual module-sheaf homotopy components. Extend the natural-degree
components by zero to negative degrees, using the extension isomorphisms in the
nonnegative degrees. There is no incoming component in degree zero, exactly as
in the additive sorting families. For an empty family the cochain objects are
zero; for p+1>r the condition is vacuous but the same contraction kills all full
cochains in those degrees. No cover or nonempty-index assumption is used. -/
theorem orderedCech_module_kernel_nullHomotopic {X' T' : Scheme.{u}} (f' : X' ⟶ T')
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
    (g : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)
        ⟶ ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat))
    (hg : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(
        ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat).X (p : ℤ), B))
      (t : Fin (p + 1) ↪o Fin r),
      orderedCechModuleCoordinate f' M W₀ D e p B t ((g.f (p : ℤ)).app B s) = 0) :
    Nonempty (Homotopy g 0) := by sorry

end AlgebraicGeometry.Scheme.Modules
