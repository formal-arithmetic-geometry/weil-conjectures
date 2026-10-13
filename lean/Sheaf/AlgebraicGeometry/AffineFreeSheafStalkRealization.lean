/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Realizing section modules on an affine open and comparing their stalks

Source: Stacks Project, Tags 01HV, 01IB, 01C6 and 0098.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Affine sheafification realizes coordinate modules, naturally on their stalk maps.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (7) (associated-sheaf stalk localization),
Tag 01IB (modules on an affine scheme), Tag 01C6 (finite free sheaves),
and Tag 0098 (stalks under restriction along the affine chart).
(blueprint: lem-sc-affine-free-sheaf-stalk-realization).

Proof: The existing affinePerfectSheafification is tilde followed by restriction
along the affine chart and the inverse of the slice-site equivalence. Its value on
a finite coordinate module is the coproduct of copies of the structure sheaf indexed
by its standard basis. The stalk of that finite coproduct is the finite
coordinate module over the stalk ring. Neighbourhoods contained in U are cofinal
at x, so ordinary open direct image followed by the ambient stalk gives the same
module with the same scalar action. Explicitly, send a coordinate tuple (r_p) to
the finite sum of r_p times the germ of its standard basis section. An arbitrary
stalk element is represented locally by finitely many coordinate sections; their
germs give its inverse image. If a tuple maps to zero, its coordinate projection
germs are all zero, proving injectivity. Conversely, the finite projection-inclusion
identity shows that this inverse reconstructs every germ. These maps are linear
over the ambient stalk ring because scalar multiplication on germs is induced by
multiplication on sections, and give e n. On each basis germ the stalk
of a sheafified map is its coefficient matrix mapped by the germ homomorphism.
Thus the assumed coefficient equalities imply the displayed naturality equation.
Rank zero uses the empty coproduct and its unique map; U need not be quasi-compact. -/
theorem exists_affine_freeSheaf_stalk_realization
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U) :
    ∃ e : ∀ n : ℕ, ModuleCat.of (X.presheaf.stalk x)
          (ULift.{0} (Fin n → X.presheaf.stalk x)) ≅
          (SheafOfModules.pushforward.{u}
              (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
            RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
              ((affinePerfectSheafification X U hU).obj
                (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))))),
        ∀ (n m : ℕ)
          (f : ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))) ⟶
            ModuleCat.of Γ(X, U) (ULift.{0} (Fin m → Γ(X, U))))
          (g : ModuleCat.of (X.presheaf.stalk x)
              (ULift.{0} (Fin n → X.presheaf.stalk x)) ⟶
            ModuleCat.of (X.presheaf.stalk x)
              (ULift.{0} (Fin m → X.presheaf.stalk x))),
          (∀ (p : Fin n) (q : Fin m),
            X.presheaf.germ U x hxU ((f (ULift.up (Pi.single p 1))).down q) =
              ((g (ULift.up (Pi.single p 1))).down q)) →
          (e n).hom ≫ (SheafOfModules.pushforward.{u}
              (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
            RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
              ((affinePerfectSheafification X U hU).map f) =
              g ≫ (e m).hom := by sorry

end AlgebraicGeometry.Scheme
