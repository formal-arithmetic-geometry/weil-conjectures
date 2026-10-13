/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.TildePrincipalLocalizationTransport
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover

/-! # Finite local freeness from finite projective principal localizations

Source: Stacks Project, Tag 00NX, (2) implies (7), and Tag 08EG, local freeness paragraph.
(blueprint: lem-sc-principal-open-finite-projective-tilde).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A module whose principal localizations inside an open are finite projective has
finite locally free associated sheaf on that open.
Source: Stacks Project, Tag 00NX, (2) implies (7); Tag 08EG, local freeness paragraph.
(blueprint: lem-sc-principal-open-finite-projective-tilde).

Proof: For each point x of U choose a principal open D(f) containing x and contained
in U. Its ring is A_f and the associated sheaf restricts to the sheaf associated with
M_f, by the localization description of tilde. The hypothesis makes M_f finite
projective. Apply lem-weil-pbc-finite-projective-standard-free-cover to M_f over A_f.
The resulting finitely many standard opens D(g) cover Spec A_f; each corresponding
localized module is finite free. Under D(f) = Spec A_f these are open neighbourhoods
in U, and localization of associated sheaves identifies their restrictions with free
sheaves of the same finite ranks. Compose their open immersions with D(f) into U.
The resulting family over all x covers U. The sheaf definition of finite local freeness
then supplies the conclusion, with no common rank required. Empty U has the empty
cover; the zero module has rank zero; no finiteness of M on all of Spec A is assumed.
-/
theorem finiteLocallyFree_restrict_tilde_of_principalOpen_projective
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) (M : ModuleCat.{u} A)
    (h : ∀ f : A, PrimeSpectrum.basicOpen f ≤ U →
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) ∧
        Module.Projective (Localization.Away f) (LocalizedModule.Away f M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj M) := by
  sorry

end AlgebraicGeometry
