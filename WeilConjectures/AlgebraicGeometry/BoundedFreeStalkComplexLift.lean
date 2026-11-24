/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.BoundedFreeStalkComplexLocalLift

/-! # Lifting the differential matrices of a bounded free stalk complex

## References

* Stacks Project, Tags 0BCD, 0BC7 and 00CR
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Restriction of ordinary direct image from an open recovers the original module. -/
private theorem openModuleDirectImage_restrict_iso (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    Nonempty ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
      ((SheafOfModules.pushforward.{u}
        (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)).obj M) ≅ M) := by
  let adj := SheafOfModules.overPushforwardOverAdj.{u}
    (R := moduleRings X.toRingedSpace) U
  have : (Over.forget U).Full :=
    ⟨fun f ↦ ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩⟩
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  let := Functor.isContinuous_comp (Over.forget U) (Over.star U)
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology X).over U)
  let φ := 𝟙 ((moduleRings X.toRingedSpace).over U) ≫
    ((Over.forget U).sheafPushforwardContinuous RingCat _ _).map
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  have : IsIso (SheafOfModules.pushforwardNatTrans.{u}
      (G := Over.forget U ⋙ Over.star U)
      (S := (moduleRings X.toRingedSpace).over U) φ
      (Over.forgetAdjStar U).unit) := by
    change IsIso (SheafOfModules.pushforwardNatIso
      (G := Over.forget U ⋙ Over.star U)
      (S := (moduleRings X.toRingedSpace).over U) φ
      (asIso (Over.forgetAdjStar U).unit)).hom
    infer_instance
  have : IsIso (adj.counit.app M) := by
    dsimp [adj, SheafOfModules.overPushforwardOverAdj,
      SheafOfModules.pushforwardPushforwardAdj]
    infer_instance
  exact ⟨asIso (adj.counit.app M)⟩

/-- A bounded free stalk complex lifts as a complex, without a prescribed derived object
(Stacks, Tags 0BCD, 0BC7 and 00CR). -/
theorem exists_boundedFree_stalk_complex_lift
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)))) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (H.X i)) ∧
        (∀ i : ℤ, Nonempty
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
            (H.X i) ≅ SheafOfModules.free
              (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty (F ≅
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj H)) := by
  classical
  let e := fun i ↦ (hfree i).some
  obtain ⟨a, b, hab⟩ := hbounded
  have hd (i : ℤ) (hi : i < a ∨ b < i) : d i = 0 := by
    have hz := (hab i hi).of_iso (e i).symm
    have hs := ModuleCat.subsingleton_of_isZero hz
    by_contra hne
    have hn : 0 < d i := Nat.pos_of_ne_zero hne
    have h01 := congrArg (fun f ↦ f.down ⟨0, hn⟩)
      (hs.elim (ULift.up (fun _ : Fin (d i) ↦ (0 : X.presheaf.stalk x)))
        (ULift.up (fun _ : Fin (d i) ↦ (1 : X.presheaf.stalk x))))
    exact zero_ne_one h01
  let K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ :=
    { X := fun i ↦ ModuleCat.of (X.presheaf.stalk x)
        (ULift.{0} (Fin (d i) → X.presheaf.stalk x))
      d := fun i j ↦ (e i).inv ≫ F.d i j ≫ (e j).hom
      shape := fun i j hij ↦ by rw [F.shape i j hij]; simp
      d_comp_d' := fun i j k _ _ ↦ by simp [Category.assoc] }
  have eK : F ≅ K := HomologicalComplex.Hom.isoOfComponents e
    (fun i j _ ↦ by simp [K])
  obtain ⟨U, hxU, hU, L, hLbounded, hLfree, ⟨eLocal⟩⟩ :=
    exists_boundedFree_stalk_complex_local_lift X x d K (fun _ ↦ rfl) a b hd
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  let H := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  refine ⟨U, hxU, hU, H, ?_, ?_, ?_⟩
  · exact ⟨a, b, fun i hi ↦ P.map_isZero (hLbounded i hi)⟩
  · intro i
    obtain ⟨eFree⟩ := hLfree i
    obtain ⟨eRestrict⟩ := openModuleDirectImage_restrict_iso X U (L.X i)
    exact ⟨eRestrict ≪≫ eFree⟩
  · exact ⟨eK ≪≫ eLocal⟩

end
end AlgebraicGeometry.Scheme
