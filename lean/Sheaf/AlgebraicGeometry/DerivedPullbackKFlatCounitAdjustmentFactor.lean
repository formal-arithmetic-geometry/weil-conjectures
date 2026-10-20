/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.Algebra.Homology.KFlatResolution

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- The two universal lifts elaborate through the recorded derived-pullback witness.
/-- Two K-flat counits differ by a natural automorphism of their common source.
No monoidal, properness, or Noetherian hypothesis is needed for this comparison.

Source: Stacks Project, Tag 06YJ, computation on K-flat resolutions, and the
right Kan extension universal property recorded by `exists_derivedPullback`.

Proof. Let δ be the recorded universal counit. The universal property gives lifts
`t₀` and `t` of the two supplied counits to endomorphisms of derived pullback,
with `Qh(t₀) ≫ δ = ε₀` and `Qh(t) ≫ δ = ε`. On a K-flat representative P,
δ, ε₀ and ε are invertible, so these equations show that both lifts are invertible
at Qh(P). Every derived object is isomorphic to the localization of a K-flat
representative: take a complex representative and then a K-flat resolution.
Naturality transports invertibility along these isomorphisms. Thus both lifts
are natural isomorphisms. Whisker `t ≫ t₀⁻¹` with Qh to obtain a. Its composite
with ε₀ is ε by the two universal-property equations and inverse cancellation.
Identity and zero resolutions satisfy the same cancellation equations; neither
an empty scheme nor a zero object requires a separate choice.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment-factor). -/
theorem exists_derivedPullback_kFlat_counit_adjustment_factor
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
      IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f), a.hom ≫ ε₀ = ε
:= by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  obtain ⟨_, _, _, _, _, _, _, E, hE, hEmap, hEadd, δ, hδ, _, hK⟩ :=
    (derivedPullback_spec f)
  have hE' : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  have : (derivedPullback f).IsLeftDerivedFunctor δ W := hδ
  have hlift : ∀ (β : Q ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)),
      (∀ P : CochainComplex A ℤ, CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso (β.app (q.obj P))) →
      IsIso ((derivedPullback f).leftDerivedLift δ W (derivedPullback f) β) := by
    intro β hβ
    let t := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) β
    apply NatTrans.isIso_iff_isIso_app t |>.2
    intro X
    rw [← NatTrans.isIso_app_iff_of_iso t (Q.objObjPreimageIso X)]
    obtain ⟨G, hG⟩ := HomotopyCategory.quotient_obj_surjective (Q.objPreimage X)
    rw [← hG]
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) G
    have hqs : W (q.map s) := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have : IsIso (Q.map (q.map s)) := Localization.inverts Q W _ hqs
    rw [← NatTrans.isIso_app_iff_of_iso t (asIso (Q.map (q.map s)))]
    have : IsIso (δ.app (q.obj P)) := hK P hP
    have : IsIso (β.app (q.obj P)) := hβ P hP
    have hfac : t.app (Q.obj (q.obj P)) ≫ δ.app (q.obj P) = β.app (q.obj P) :=
      (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) β (q.obj P)
    have : IsIso (t.app (Q.obj (q.obj P)) ≫ δ.app (q.obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (δ.app (q.obj P))
  let t₀ := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) ε₀
  let t := (derivedPullback f).leftDerivedLift δ W (derivedPullback f) ε
  have : IsIso t₀ := hlift ε₀ hε₀
  have : IsIso t := hlift ε hε
  let a := Functor.isoWhiskerLeft Q (asIso t ≪≫ (asIso t₀).symm)
  refine ⟨a, ?_⟩
  ext X
  change (t.app (Q.obj X) ≫ (inv t₀).app (Q.obj X)) ≫ ε₀.app X = ε.app X
  rw [← (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) ε₀ X]
  change (t.app (Q.obj X) ≫ (inv t₀).app (Q.obj X)) ≫
    t₀.app (Q.obj X) ≫ δ.app X = ε.app X
  rw [Category.assoc, ← Category.assoc ((inv t₀).app _) (t₀.app _) (δ.app X),
    ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app, Category.id_comp]
  exact (derivedPullback f).leftDerived_fac_app δ W (derivedPullback f) ε X

end AlgebraicGeometry
