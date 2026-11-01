/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleTracePairingLocal

/-! # Gluing the constructed finite-etale sheet transposes -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The explicitly constructed sheet transposes glue to a native module map.
Source: source-side sheaf Hom descent in smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing).

Proof in words. Choose etale neighbourhoods splitting p, refine them to cover
all points of U by their sheets, and restrict the displayed local transposes to
this cover. Given two sheets on two charts, their overlap has the same map to U
and hence to X. Refine it by the open-and-closed intersections of the two finite
splittings. On each piece their enumerations differ by a permutation that sends
the chosen sheet to the chosen sheet. The canonical product projection maps
commute with pullback and this permutation, by inverse-image composition and
counit naturality. Therefore their inverses and product inclusions identify the
two constructed transposes. Sheaf Hom descent glues the compatible maps on U.
The maps are linear before gluing, so the sheaf map is a native module map.
Comparing with an arbitrary splitting chart on the same common refinements and
using separatedness proves the displayed equation for EVERY chart, not just the
chosen cover. The empty source and zero coefficient ring give the unique maps. -/
theorem nativeFiniteEtaleLocalTranspose_glue
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) :
    ∃ f : M ⟶ (upperStar Λ p).obj P,
      ∀ (c : FiniteEtaleModuleChart p) (j : Fin c.degree),
        (upperStar Λ (c.sheet j)).map f = nativeFiniteEtaleLocalTranspose Λ p c M P h j := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
