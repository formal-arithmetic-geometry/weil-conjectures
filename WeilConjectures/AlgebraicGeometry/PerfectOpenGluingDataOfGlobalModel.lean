/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOpenGluingData
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Gluing data from a global perfect pullback model

Source: Stacks Project, Tag 09RF, construction of adjoint maps.
(blueprint: lem-pc-perfect-open-gluing-data-global-model). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact open restriction is derived pullback, hence preserves perfectness (Stacks 09UA). -/
private theorem perfect_exactOpenRestriction (Y : Scheme.{u}) (A : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))]
    [∀ V : A.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings A.toScheme.toRingedSpace).over V))]
    (R' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
    [R'.Additive] [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
    (hR' : R' = SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) A ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over A))
        (D := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv A))
    (E : schemeDerivedCategory Y) (hE : Scheme.IsPerfect Y E) :
    Scheme.IsPerfect A.toScheme (R'.mapDerivedCategory.obj E) := by
  classical
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace)
  let T : B ⥤ C := Scheme.Modules.tensorPullback A.ι
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec A.ι
  have h : F = T := CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let η : T ≅ Scheme.Modules.restrictFunctor A.ι :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction A.ι).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction A.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback A.ι).symm
  let θ : R' ≅ T := eqToIso hR' ≪≫ Scheme.Modules.overFunctorEquiv A ≪≫ η.symm
  have : Limits.PreservesFiniteLimits T :=
    Limits.preservesFiniteLimits_of_natIso θ
  have : Limits.PreservesFiniteColimits T :=
    Limits.preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : (derivedPullback A.ι).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback A.ι ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback A.ι) ε
      T.mapDerivedCategoryFactorsh.hom W
  let c := (Functor.mapDerivedCategoryNatIso θ).app E ≪≫ i.symm.app E
  have hp := derivedPullback_preserve_perfect A.ι E hE
  intro x
  obtain ⟨V, hx, K, hK, ⟨iK⟩⟩ := hp x
  refine ⟨V, hx, K, hK, ?_⟩
  exact ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings A.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso c ≪≫ iK⟩


set_option maxHeartbeats 500000 in
-- Exact nested restrictions require a larger elaboration budget.
/-- A global perfect model and its limit comparison provide local gluing data.
Source: Stacks Project, Tag 09RF, adjunction construction of local maps.
(blueprint: lem-pc-perfect-open-gluing-data-global-model).
The proof chooses the top open twice, the derived pullback/direct image
adjunction, and obtains the local maps by adjunction from the comparison
isomorphism. Both local maps are the restriction of the same global adjoint,
so their overlap equation is reflexive. Naturality of the pullback/restriction
comparison identifies their restricted counit composites with the restriction
of the original isomorphism; these are invertible. Exact restriction is derived
open pullback, so the two local objects are perfect. -/
theorem perfect_open_gluing_data_of_global_model
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (A : schemeDerivedCategory Y) (hA : Y.IsPerfect A)
    (e : (derivedPullback g).obj A ≅ E) : PerfectOpenGluingData g E := by
  classical
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction g
  let U : Y.Opens := ⊤
  let RX := (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory
  let RY := (schemeOpenRestriction Y U).mapDerivedCategory
  have hγ : Nonempty (derivedPullback g ⋙ RX ≅ RY ⋙ derivedPullback (g ∣_ U)) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (derivedPullback_openRestriction_iso_universes.{u, w, w}
        g (g ⁻¹ᵁ U) U le_rfl)
  obtain ⟨γ⟩ := hγ
  let a := adj.homEquiv A E e.hom
  have hp : U.toScheme.IsPerfect (RY.obj A) :=
    perfect_exactOpenRestriction Y U (schemeOpenRestriction Y U) rfl A hA
  have he : (derivedPullback g).map a ≫ adj.counit.app E = e.hom := by
    exact (adj.homEquiv A E).symm_apply_apply e.hom
  have hi : IsIso ((derivedPullback (g ∣_ U)).map (RY.map a) ≫
      γ.inv.app ((schemeDerivedDirectImage g).obj E) ≫ RX.map (adj.counit.app E)) := by
    have hn : (derivedPullback (g ∣_ U)).map (RY.map a) ≫
        γ.inv.app ((schemeDerivedDirectImage g).obj E) =
        γ.inv.app A ≫ RX.map ((derivedPullback g).map a) := γ.inv.naturality a
    have hh : (derivedPullback (g ∣_ U)).map (RY.map a) ≫
        γ.inv.app ((schemeDerivedDirectImage g).obj E) ≫ RX.map (adj.counit.app E) =
        γ.inv.app A ≫ RX.map e.hom := by
      rw [← Category.assoc, hn, Category.assoc, ← RX.map_comp, he]
    rw [hh]
    infer_instance
  refine ⟨U, U, by simp [U], adj, γ, γ, RY.obj A, RY.obj A,
    Iso.refl _, RY.map a, RY.map a, hp, hp, ?_, hi, hi⟩
  simp

end AlgebraicGeometry
