/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-!
# Local freeness through the pullback of module objects

`ProEtale.IsLocallyFree` is phrased with the sheaf pullback `mapMod(f^*)`, a module over the
sheaf pullback `f^* Λ_X` of the coefficient ring. This file shows that it suffices that the
pullbacks `f^* M = Λ_Y ⊗_{f^* Λ_X} f^* M` of module objects over the condensed ring `Λ` be free
(`ProEtale.CondensedRing.isLocallyFree_of_isFree_upperStar`), since the coefficient morphism
`α_f : f^* Λ_X ⟶ Λ_Y` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}

end AlgebraicGeometry.ProEtale.CondensedRing
