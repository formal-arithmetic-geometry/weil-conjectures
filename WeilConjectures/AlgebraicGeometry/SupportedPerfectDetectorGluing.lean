/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SupportedDetectorOpenLift
import WeilConjectures.AlgebraicGeometry.SupportedKoszulUnitSummand

/-! # Gluing supported perfect zero detectors

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The supported Koszul gluing step for a finite affine cover with at least two members.
The hypothesis supplies zero detectors only for schemes with strictly smaller covers. -/
theorem supported_perfect_detector_gluing
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
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  obtain ⟨U, V, hU, hUV, R, adj, Q, hQ, hQT, hdetect⟩ :=
    exists_supported_detector_open_lift X s hcover hcard ih T hT hTc
  obtain ⟨E, hE, hET, ⟨r⟩, hunit⟩ :=
    exists_supported_koszul_unit_summand X T hT hTc U V hU hUV R adj Q hQ hQT
  refine ⟨E, hE, hET, ?_⟩
  intro K hKT hHom
  refine hdetect K hKT (hunit K hKT hHom) ?_
  intro n
  let rn := r.map (shiftFunctor (schemeDerivedCategory X) n)
  refine ⟨fun f g ↦ ?_⟩
  have hfg : rn.r ≫ f = rn.r ≫ g := (hHom n).elim _ _
  have h := congrArg (fun k ↦ rn.i ≫ k) hfg
  simpa only [← Category.assoc, rn.retract, Category.id_comp] using h

end AlgebraicGeometry
