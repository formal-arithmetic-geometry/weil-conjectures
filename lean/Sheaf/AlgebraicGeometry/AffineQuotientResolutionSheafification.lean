/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import Sheaf.Algebra.Homology.ModuleStalkExact

/-!
# Sheafifying an affine quotient resolution

Source: Stacks Project, Tag 068C, affine-local resolution argument
(blueprint: lem-sc-affine-quotient-resolution-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An algebraic resolution of an affine quotient sheafifies to a resolution of the
restricted pushforward of the closed subscheme's structure sheaf.
Source: Stacks Project, Tag 068C, affine-local reduction and Koszul resolution
(blueprint: lem-sc-affine-quotient-resolution-sheafification).

Proof: The equation for the quotient presentation identifies the inverse image of
`U` with `Spec (A/I)` over `Spec A`, where `A = Γ(Y,U)`. On a basic open `D(g)`, the
restricted pushforward of the structure sheaf has sections `(A/I)_g`, including
its `A_g`-module action. These identifications commute with restriction maps and
therefore give an isomorphism with `tilde(A/I)` transported along `hU.isoSpec`.
The tilde functor is exact: its stalk at a prime is localization of modules, and
localization is exact. Restriction along the affine chart is an equivalence, hence
exact. Apply these functors to the given augmentation; homology commutes with an
exact functor, so the resulting map remains a quasi-isomorphism. Identify the
image of the single complex with the single complex of the image module, then
compose with the single complex of the preceding module isomorphism. This gives
the asserted chain map and quasi-isomorphism. No bound or freeness is needed. -/
theorem exists_affine_quotient_sheafified_resolution {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.Opens) (hU : IsAffineOpen U) (I : Ideal (Γ(Y, U)))
    (e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
      Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)))
    (he : i ∣_ U ≫ U.toSpecΓ =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ)
    (ε : K ⟶ (ChainComplex.single₀ (ModuleCat (Γ(Y, U) : Type u))).obj
      (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I)))
    [QuasiIso ε] :
    ∃ q : ((tilde.functor Γ(Y, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K ⟶
        (ChainComplex.single₀ U.toScheme.Modules).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
      QuasiIso q := by sorry

end AlgebraicGeometry
