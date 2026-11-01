/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothFibreLatticeFibreSection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Local detection of the scalar-extension isomorphism

The scalar-extension morphism in the smooth-fibre lattice argument is checked after a
pro-etale cover.  This isolates the local-to-global categorical step from the geometric
construction of the cover.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood-extension-local-iso)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A morphism of coefficient modules is locally invertible on a pro-etale cover. -/
def ScalarExtensionLocalIso
    {A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] {Z : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj A Z)}
    (j : M ⟶ N) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
    ∀ s : C.I₀, IsIso ((CondensedRing.upperStar A (C.f s)).map j)

/--
A scalar-extension morphism which is invertible on a pro-etale cover is invertible globally.

Proof in words: the maps in a `Scheme.Cover` form a covering presieve for the pro-etale
precoverage.  Apply the standard conservativity theorem
`ProEtale.isIso_of_isIso_localizationRestriction` to the underlying morphism of sheaves.
The canonical comparison between localization restriction and `CondensedRing.upperStar`
transports each assumed local isomorphism to the restriction used by that theorem.  The
forgetful functor from module sheaves reflects isomorphisms, so the original module map is
an isomorphism.  This is precisely the local-to-global step and uses no geometric input.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood-extension-local-iso)
-/
theorem isIso_of_scalar_extension_local_iso
    {A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] {Z : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj A Z)}
    (j : M ⟶ N) (hlocal : ScalarExtensionLocalIso j) : IsIso j := by
  sorry

end AlgebraicGeometry.ProEtale
