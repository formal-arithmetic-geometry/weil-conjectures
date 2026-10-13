/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Order.Hom.Basic

/-! # Localization of affine intersection quotient systems

Source: Stacks Project, Tags 01IB, 01IC, and 00CS; ideal products as in 01I8.
(blueprint: lem-weil-pbc-affine-intersection-quotients-stalk).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Localizing compatible affine quotients preserves any prescribed kernel filtration.

Source: Stacks Project, Schemes, Tags 01IB and 01IC, and Algebra, Tag 00CS.
(blueprint: lem-weil-pbc-affine-intersection-quotients-stalk).

Proof: Put A = Gamma(U,O_X), B = O_(X,x), and let P be the prime of x in U.
Construct M = B tensor_A L, with L restricted from R to A. The affine
quasi-coherent stalk correspondence identifies each stalk S_m,x with the
localization of Gamma(U,S_m); localize q_m to define p_m. Naturality of germs
identifies the localized section transitions with the stalk transitions, giving
compatibility of all p_m. Localization preserves surjectivity and exactness.
For an R-submodule Q of L, define phi(Q) as the image of B tensor_A Q in M.
Inclusions of submodules make this an order homomorphism. Exactness applied to
the section kernel criterion identifies ker p_m with phi(D_m). Restriction of
scalars identifies K^r L with
I(U)^r L: K is the extended ideal, R coefficients can be absorbed into elements
of L, and ideal extension commutes with powers. Localization of ideal products
therefore gives phi(K^r L) = (I(U)B)^r M. The quasi-coherent ideal/stalk
correspondence identifies I(U)B with the image J of the ideal stalk inclusion;
the assumed germ equation for e ensures it uses exactly this unit-stalk
identification. This also proves the formula at r=0, since localization of the
identity on L has full image. No finiteness, Noetherian hypothesis, completion,
formal module, kernel stabilization, or Artin--Rees bound is used. If U is empty
there is no x; zero or unit ideals and zero modules obey the same equations. -/
theorem affine_intersection_quotients_stalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (S : ℕᵒᵖ ⥤ X.Modules)
    (U : X.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(X, U.1) R]
    (L : ModuleCat.{u} R) (D : ℕ → Submodule R L)
    (q : ∀ m : ℕ,
      ((ModuleCat.restrictScalars (algebraMap Γ(X, U.1) R)).obj L)
        →ₗ[Γ(X, U.1)] Γ(S.obj (op m), U.1))
    (hqc : ∀ m : ℕ, (S.obj (op m)).IsQuasicoherent)
    (hq : ∀ m : ℕ, Function.Surjective (q m))
    (ht : ∀ (a b : ℕ) (h : a ≤ b) (z : L),
      (S.map (homOfLE h).op).app U.1 (q b z) = q a z)
    (hk : ∀ (m : ℕ) (z : L), q m z = 0 ↔ z ∈ D m)
    (x : X) (hx : x ∈ U.1)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (V : X.Opens) (hx : x ∈ V) (r : Γ(X, V)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        V x hx r) = X.presheaf.germ V x hx r) :
    let K := (I.ideal U).map (algebraMap Γ(X, U.1) R)
    let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
    ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
      ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
        (∀ m : ℕ, Function.Surjective (p m)) ∧
        (∀ (a b : ℕ) (h : a ≤ b) (z : M),
          (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
        ∃ φ : Submodule R L →o Submodule (X.presheaf.stalk x) M,
          (∀ r : ℕ, φ (K ^ r • (⊤ : Submodule R L)) =
            J ^ r • (⊤ : Submodule (X.presheaf.stalk x) M)) ∧
          (∀ m : ℕ, LinearMap.ker (p m) =
            φ (D m)) := by sorry

end AlgebraicGeometry
