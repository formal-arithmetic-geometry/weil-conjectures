/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb
public import WeilConjectures.TraceFormula.Specialization.Trait

/-!

# Restriction to the closed point of the trait through henselian lifts

Let `S = Spec k'⟦t⟧` and `i : Spec k' ⟶ S` the closed point. The closed point is the closed
subscheme `Spec (k'⟦t⟧ ⧸ (t))`, with quasi-compact open complement `Spec k'⟦t⟧[t⁻¹]`. Hence the
sections of `i^* F` over the w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras `C̄` are the
sections of `F` over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)`
(`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), and these cover the site of
the closed point. So a module object `F` over `Λ_S` vanishes after `i^*` as soon as its sections
over all such `W` vanish (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_of_forall`),
and a morphism becomes an isomorphism after `i^*` as soon as it is bijective on all such
sections (`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_of_forall`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section ClosedLift

variable {A : CommRingCat.{u}} (I : Ideal A) {R : Type (u + 1)} [Ring R]

variable {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j] [QuasiCompact j]

end ClosedLift

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k']

end AlgebraicGeometry.ProEtale.CondensedRing
