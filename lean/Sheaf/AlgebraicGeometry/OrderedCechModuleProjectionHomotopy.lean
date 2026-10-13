/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionLift
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import Sheaf.AlgebraicGeometry.AlternatingCechSecondSortingIdentity
import Sheaf.AlgebraicGeometry.OrderedCechModuleCoordinates

/-! # Sorting homotopy for the module Čech projection

Source: Stacks Project, Tags 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The signed projection is homotopic to identity before any kernel hypothesis.
Source: Stacks 01FM, equations 20.23.6.1 and 20.23.6.2.
(blueprint: lem-pc-ordered-cech-module-projection-homotopy).

Proof: Transport the first sorting family H and the second family J along e on every
open. Their identities give dH+Hd=id-kappa and dJ+Jd=kappa-P. Naturality follows
termwise from restriction functoriality; local linearity follows from hlinear since
all terms restrict the same scalar to the same intersection. Their sum is therefore
an actual family of module-sheaf maps with boundary id-P. Push forward these maps
and extend by zero in negative degrees. The degree-zero incoming component is zero,
as in the natural-degree families. These give the asserted homotopy. The formulas
also apply to empty families and to degrees with no increasing tuples. -/
theorem orderedCech_module_projection_homotopy {X' T' : Scheme.{u}} (f' : X' ⟶ T')
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
    (P : ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat) ⟶
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat))
    (hP : IsOrderedCechModuleProjection f' M W₀ D e P) :
    Nonempty (Homotopy (𝟙 _) P) := by sorry

end AlgebraicGeometry.Scheme.Modules
