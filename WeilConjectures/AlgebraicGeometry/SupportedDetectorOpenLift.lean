/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedDetectorOpenLiftCore

/-! # Lifting the detector from the smaller open

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The lift of the smaller-cover detector detects supported objects whose open unit
is invertible; it need not detect arbitrary supported objects on X. -/
theorem exists_supported_detector_open_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (s : Finset X.affineOpens) (hcover : (⨆ U ∈ s, (U : X.Opens)) = ⊤)
    (hcard : 2 ≤ s.card)
    (ih : ∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ U : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
      (t : Finset Y.affineOpens), t.card < s.card →
      (⨆ U ∈ t, (U : Y.Opens)) = ⊤ →
      ∀ (S : Set Y), IsClosed S → IsCompact Sᶜ →
        ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
          (∀ (n : ℤ) (x : Y), x ∉ S →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
          ∀ K : schemeDerivedQCohCategory Y,
            (∀ (n : ℤ) (x : Y), x ∉ S →
              Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
            (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ (U : X.Opens) (V : X.affineOpens), IsCompact (U : Set X) ∧
      U ⊔ (V : X.Opens) = ⊤ ∧
      ∃ (R : DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
          schemeDerivedCategory X)
        (adj : (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
        (Q : schemeDerivedQCohCategory X),
        Scheme.IsPerfect X Q.obj ∧
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj Q.obj).val.presheaf x))) ∧
        ∀ K : schemeDerivedQCohCategory X,
          (∀ (n : ℤ) (x : X), x ∉ T →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
          IsIso (adj.unit.app K.obj) →
          (∀ n : ℤ, Subsingleton (Q.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  obtain ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, hdetect⟩ :=
    exists_supported_detector_open_lift_core X s hcover hcard ih T hT hTc
  refine ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, ?_⟩
  intro K hKT hUnit hHom
  let : IsIso (adj.unit.app K.obj) := hUnit
  have hres := hdetect K hKT (fun n ↦ ?_)
  · apply (IsZero.iff_id_eq_zero K.obj).mpr
    apply (cancel_mono (adj.unit.app K.obj)).mp
    have heq : adj.unit.app K.obj = 0 := by
      apply (adj.homEquiv K.obj _).symm.injective
      exact hres.eq_of_src _ _
    simp [heq]
  · refine ⟨fun f g ↦ ?_⟩
    apply (adj.homEquiv _ _).injective
    apply (cancel_mono (inv (adj.unit.app K.obj))).mp
    exact (hHom n).elim _ _

end AlgebraicGeometry
