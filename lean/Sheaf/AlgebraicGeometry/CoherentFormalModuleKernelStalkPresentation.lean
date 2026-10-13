/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import Sheaf.RingTheory.AdicKernelImageBound
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Stalk presentations of stabilized kernel images

Source: Stacks Project, Lemma 087X, proof of claims (a) and (b).
(blueprint: lem-weil-pbc-formal-kernel-stalk-presentation).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The stabilized image system has compatible surjective stalk presentations with an
eventually bounded kernel filtration.

Source: Stacks Project, Lemma 087X, proof of claims (a) and (b).
(blueprint: lem-weil-pbc-formal-kernel-stalk-presentation).

Proof: On each member of a finite affine cover, use the affine formal-module
 equivalence to represent alpha by a homomorphism of finite modules over the
 completed coordinate ring. Its kernel L is finite since that ring is Noetherian.
 Artin--Rees for the image of this homomorphism identifies the eventual kernel
 images at level m with L/(L intersect I^(m+1)M). The hypothesis hc identifies
 the prescribed stabilized image with this eventual image; hS and naturality
 of j identify S and all its transition maps with these quotient images.
 Artin--Rees for L in M supplies b with L intersect I^(r+b)M contained in I^r L.
 Choose the maximum of these constants over the finite cover. Localize L
 (as a module over the affine coordinate ring) at x to get M. Exactness of
 localization gives surjective maps p_m to S_m with kernels the localizations
 of L intersect I^(m+1)M_source. Their transitions commute, since they are
 induced by the same inclusions of L into the source module. Localization
 of the Artin--Rees containment gives the displayed kernel bound uniformly
 in x. The equation on germs identifies J with the localization of I.
 If I is zero, the presentations are isomorphisms; if it is the unit ideal,
 their targets vanish and the bound is automatic. Zero modules cause no
 exception and the empty cover has maximum zero. -/
theorem coherentFormalModule_kernel_stalk_presentation
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
    ∃ b : ℕ, ∀ x : X,
      ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r) →
      let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
      ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
        ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
          (∀ m : ℕ, Function.Surjective (p m)) ∧
          (∀ (a b : ℕ) (h : a ≤ b) (z : M),
            (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
          (∀ (d : ℕ), max c b ≤ d → ∀ n : ℕ,
            LinearMap.ker (p (n + d)) ≤
              J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) M)) := by sorry

end AlgebraicGeometry
