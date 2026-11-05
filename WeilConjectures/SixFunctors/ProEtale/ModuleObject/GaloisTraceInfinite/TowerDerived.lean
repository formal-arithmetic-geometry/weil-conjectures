/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.ModuleObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitTransportAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# The derived unit of a Galois tower is split by an invariant retraction

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) with Galois groups
of order invertible in `Λ`, and let `K` be a bounded below complex of `Λ_X`-module objects such
that, at every term, `g_{∞*} g_∞^* Kⁿ` is the colimit of the finite levels and `g_∞^* Kⁿ` is
`g_{∞*}`-acyclic. Then the unit `K ⟶ Rg_{∞*} Lg_∞^* K` of the derived adjunction has a retraction
`R`, induced by the levelwise normalized traces
(`AlgebraicGeometry.ProEtale.GaloisTower.complexTrace`), which is invariant under the derived unit
transports along the automorphisms of `Y_∞` over `X` compatible with the Galois actions
(`AlgebraicGeometry.ProEtale.GaloisTower.exists_invariant_retraction_derivedUnit`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end CondensedRing

namespace GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
  (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))

end GaloisTower

end AlgebraicGeometry.ProEtale
