/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisLisseCorrespondenceData
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber

/-! # Normalized finite monodromy on a pulled-back finite cover -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

set_option maxHeartbeats 0 in
-- The finite correspondence contains several composite fibre functors.
/-- If a finite module sheaf is represented, as a set sheaf, by a pulled-back finite
cover, its normalized representation kills the kernel of the actual path homomorphism.
Source: the finite-evaluation clauses of `cor-galois-lisse-representations` and
pullback of the fibre functor.
(blueprint: lem-dl-a1-condensed-finite-cover-kernel).

Proof: the pullback fibre isomorphism identifies evaluation on a pulled-back cover
with evaluation of `pullbackPathHom`. Thus an element of its kernel fixes every point
of that cover. The finite-etale-action clause and the injective comparison eta show
that gamma fixes its representing FLC sheaf's stalk. Naturality transports this to the
underlying set sheaf of the module. Finally finiteEvaluationAction and the injective
stalk comparisons kappa and tau show that every module vector is fixed. -/
theorem finite_action_eq_one_of_pullback_cover
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((fiber b).obj P)]
    (eG : G ≃ₜ* Aut (fiber b))
    (haction : ∀ (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P),
      g • z = (eG g).hom.app P z)
    (d : GaloisLisseFiniteCorrespondence b G)
    (A : Type (u + 1)) [Ring A] [Finite A]
    (F : LisseModuleSheafCategory U A) (P : C.FiniteEtale)
    (eF : (d.Φ.functor.obj ((FiniteEtale.pullback j).obj P)).obj ≅
      galoisUnderlyingSetSheaf A F.obj)
    (g : G) (hg : pullbackPathHom j b (eG g) = 1) :
    (((d.e A).functor.obj F).obj.ρ g) = 1 := by
  let Q := (FiniteEtale.pullback j).obj P
  let β := pullbackFiberIso j b
  have hfix (z : (fiber b).obj Q) : (eG g).hom.app Q z = z := by
    apply (ConcreteCategory.bijective_of_isIso (β.hom.app P)).1
    have h := congrArg (fun σ : Aut (fiber (b ≫ j)) ↦
      σ.hom.app P (β.hom.app P z)) hg
    change β.hom.app P ((eG g).hom.app Q (β.inv.app P (β.hom.app P z))) =
      β.hom.app P z at h
    simpa only [← ConcreteCategory.comp_apply, β.hom_inv_id_app,
      ConcreteCategory.id_apply] using h
  have hγ (z) : (d.γ g).hom.app (d.Φ.functor.obj Q) z = z := by
    apply (ConcreteCategory.bijective_of_isIso (d.η.hom.app Q)).1
    rw [d.finiteEtaleAction Q g z, haction, hfix]
    exact ULift.up_down _
  obtain ⟨hF, κ, _, hκ⟩ := d.finiteEvaluationAction A F
  let α : d.Φ.functor.obj Q ≅ galoisUnderlyingFLC A F.obj hF :=
    ObjectProperty.isoMk _ eF
  have hγF (z : ((pointSmallEtale b).sheafFiber (A := Type (u + 1))).obj
      (galoisUnderlyingSetSheaf A F.obj)) :
      (d.γ g).hom.app (galoisUnderlyingFLC A F.obj hF) z = z := by
    obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((Scheme.flcFiber b).map α.hom)).2 z
    have h := ConcreteCategory.congr_hom ((d.γ g).hom.naturality α.hom) w
    simpa only [Functor.comp_map, ObjectProperty.ι_map, hγ,
      ConcreteCategory.comp_apply] using h
  ext v
  change (((d.e A).functor.obj F).obj.ρ g) v = v
  apply (ConcreteCategory.bijective_of_isIso ((d.τ A).hom.app F)).1
  apply κ.injective
  rw [hκ, hγF]

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
