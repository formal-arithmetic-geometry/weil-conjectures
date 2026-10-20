/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Flatness of locally free constant-coefficient sheaves
Source: Stacks Project, Modules on Sites, lemmas flatness-sheafification-refined
and flatness-local; the constant coefficient realization identifies the scalar actions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- A fixed-ring sheaf whose canonical ringed-site realization is finite locally free
is a flat object for the ordinary sheaf tensor product.

Source: Stacks Project, Modules on Sites, section Flat modules, lemmas
flatness-sheafification-refined and flatness-local; the local basis characterization
of finite locally free modules.

Proof: The local generators data give a covering on which the realization is the free
module on `Fin t`. The constant-ring sheafification unit is locally bijective; hence
on the localized site the equivalence `finiteCoefficientEtaleRealization` identifies
this free ringed module with the constant sheaf on the free Lambda-module on `Fin t`.
At every geometric point, lift the point through this cover. Applying the fibre functor
to the basis and coordinate maps identifies the fibre of L with this free Lambda-module.
Its tensor functor is the finite direct sum of the identity, hence is exact, also when
t = 0 or Lambda is the zero ring. Flatness of etale fixed-ring sheaves is detected on
these geometric fibres by `Etale.flat_iff_forall_flat_sheafFiber_obj`; therefore L is flat.
No assumption about flatness over another ring occurs.
(blueprint: lem-pur-finite-locally-free-etale-flat). -/
theorem flat_of_finiteCoefficientEtaleRealization_locallyFree
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (t : ℕ)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (R := finiteCoefficientEtaleRingSheaf X Λ)
      ((finiteCoefficientEtaleRealization X Λ).obj L) t) :
    ObjectProperty.flat L := by sorry

end AlgebraicGeometry.ProEtale
