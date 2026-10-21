/-
Copyright (c) 2026 Q50. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q50
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Evaluation formula for coextension along an isomorphism

Source: blueprint main-20261015, `def-sfb-module-open-lower-shriek-adjunction`,
proof, last sentence, and `def-sfb-modobj-coextension-along-iso`
(blueprint: lem-sfb-coextension-iso-evaluation-formula).

The existing adjoint-uniqueness isomorphism is evaluation at the unit. Its inverse,
already a natural family of module morphisms, is the unique underlying factorization
of the transpose of the action transported through the inverse scalar map.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

/-- Evaluation and inverse formulas for the specified coextension comparison.

Source: blueprint main-20261015, `def-sfb-module-open-lower-shriek-adjunction`,
proof, last sentence; normalization of `def-sfb-modobj-coextension-along-iso`
(blueprint: lem-sfb-coextension-iso-evaluation-formula).

Proof plan:
1. Restriction retains underlying objects and arrows (`def-sfb-modobj-restriction`).
   Successive restriction along `φ` and its inverse cancels the two scalar maps in
   the action, giving the identity underlying unit and counit of
   `def-sfb-modobj-restriction-equivalence`.
2. Apply `lem-weil-pbc-quasi-inverse-adjoint` with this counit fixed. The resulting
   inverse-restriction adjunction has identity underlying counit.
3. The counit of `def-sfb-modobj-restrict-coextend-adjunction` is evaluation at the
   unit, namely the left-unitor inverse followed by the unit tensored with the
   identity and then `coextendEv`.
4. Counit compatibility in `det-sp-unique-right-adjoint` identifies the underlying
   arrow of `def-sfb-modobj-coextension-along-iso` with this evaluation. The same
   comparison is a natural isomorphism of module objects, supplying linearity,
   naturality and both inverse identities.
5. The inverse Hom map of `def-sfb-modobj-restrict-coextend-adjunction`, applied to
   the identity underlying inverse-restriction counit, evaluates to the transported
   action. Curry this equation to obtain the second clause. The equalizer inclusion
   from `def-sfb-modobj-coextension` is monic, giving the last, underlying uniqueness
   clause. Thus the factored transpose is precisely the inverse module morphism. -/
theorem coextendScalarsIsoComapInv_formula
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ X : C, PreservesColimits (tensorLeft X)]
    [∀ X : C, PreservesColimits (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (N : Mod C R) :
    ((coextendScalarsIsoComapInv φ).hom.app N).hom =
        (λ_ (coextendScalarsObj φ N).X).inv ≫
          η[S] ▷ (coextendScalarsObj φ N).X ≫ coextendEv φ N ∧
      ((coextendScalarsIsoComapInv φ).inv.app N).hom ≫ coextendι φ N =
        MonoidalClosed.curry ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) ∧
      ∀ d : N.X ⟶ (coextendScalarsObj φ N).X,
        d ≫ coextendι φ N =
            MonoidalClosed.curry ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) →
          d = ((coextendScalarsIsoComapInv φ).inv.app N).hom := by
  have hε : ((comapEquivalenceOfIsIso φ).counit.app N).hom = 𝟙 N.X := by
    change 𝟙 N.X ≫ 𝟙 N.X ≫ 𝟙 N.X = 𝟙 N.X
    simp
  have he : ((coextendScalarsIsoComapInv φ).hom.app N).hom = coextendCounitHom φ N := by
    have h := Adjunction.rightAdjointUniq_hom_app_counit
      (restrictCoextendAdjunction φ) (comapEquivalenceOfIsIso φ).toAdjunction N
    have h' := congrArg (fun f ↦ f.hom) h
    change ((coextendScalarsIsoComapInv φ).hom.app N).hom ≫
      ((comapEquivalenceOfIsIso φ).counit.app N).hom = _ at h'
    erw [hε, Category.comp_id] at h'
    simpa [restrictCoextendAdjunction, Adjunction.mkOfHomEquiv_counit_app,
      coextendHomEquiv] using h'
  have hd : ((coextendScalarsIsoComapInv φ).inv.app N).hom ≫ coextendι φ N =
      MonoidalClosed.curry ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) := by
    have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
      (comapEquivalenceOfIsIso φ).toAdjunction (restrictCoextendAdjunction φ) N
    rw [restrictCoextendAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at h
    have hi : (coextendScalarsIsoComapInv φ).inv.app N =
        coextendHom φ ((comapEquivalenceOfIsIso φ).counit.app N) :=
      ((coextendHomEquiv φ N _).apply_symm_apply _).symm.trans
        (congrArg (coextendHomEquiv φ N _) h)
    apply MonoidalClosed.uncurry_injective
    erw [MonoidalClosed.uncurry_natural_left, uncurry_coextendι,
      MonoidalClosed.uncurry_curry, hi, whiskerLeft_coextendHom_hom_coextendEv, hε,
      Category.comp_id]
    rfl
  refine ⟨he, hd, ?_⟩
  intro d h
  exact (cancel_mono (coextendι φ N)).1 (h.trans hd.symm)

end CategoryTheory.Mod
