/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimits
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

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k']

/-- The henselian lift `W = Spec H_{k'⟦t⟧}(C̄)` of a `k'⟦t⟧ ⧸ (t)`-algebra `C̄`, as an object of
the pro-étale site of the trait. -/
noncomputable abbrev traitClosedLift (C : Type u) [CommRing C]
    [Algebra (PowerSeries k') C] : (trait k').ProEt :=
  closedLiftSpec (.of (PowerSeries k')) C

/-- A module object over `Λ_S` vanishes after restriction to the closed point of the trait if
its sections over the henselian lifts of all w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras
vanish. -/
theorem isZero_upperStar_traitClosedPoint_obj_of_forall
    (F : Mod (Sheaf (ProEt.topology (trait k')) Ab.{u + 1}) (condensedRingObj Λ (trait k')))
    (hF : ∀ (C : Type u) [CommRing C] [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra (PowerSeries k') C]
      [IsScalarTower (PowerSeries k') (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C], IsWContractibleRing C →
        Subsingleton (F.X.obj.obj (op (traitClosedLift C)))) :
    Limits.IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj F) :=
  sorry

/-- A morphism of module objects over `Λ_S` becomes an isomorphism after restriction to the
closed point of the trait if it is bijective on sections over the henselian lifts of all
w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebras. -/
theorem isIso_upperStar_traitClosedPoint_map_of_forall
    {F G : Mod (Sheaf (ProEt.topology (trait k')) Ab.{u + 1}) (condensedRingObj Λ (trait k'))}
    (φ : F ⟶ G)
    (hφ : ∀ (C : Type u) [CommRing C] [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra (PowerSeries k') C]
      [IsScalarTower (PowerSeries k') (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
      [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C], IsWContractibleRing C →
        Function.Bijective (φ.hom.hom.app (op (traitClosedLift C)))) :
    IsIso ((traitClosedPoint k')^*⟦Λ⟧.map φ) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
