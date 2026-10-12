/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import Sheaf.AlgebraicGeometry.PerfectSupportedMapLift
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
/-! # The detector on the localized smaller open

Source: Stacks Project, Tag 0A9A, induction paragraphs.
(blueprint: lem-pc-supported-detector-open-lift-core).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- A supported perfect global object whose derived restriction detects the supported
quasi-coherent objects on the smaller open. No assertion of global detection is made.
Source: Stacks Project, Tag 0A9A, induction paragraphs and retract argument.
(blueprint: lem-pc-supported-detector-open-lift-core).

Proof:
1. Choose V in s and let U be the union of s.erase V. Each remaining chart lies in U,
   so its inverse image under U.toScheme.ι is affine, and these give a cover of U with
   at most s.card - 1 members. The finite union U is compact. Quasi-separatedness of X
   makes U intersect T-complement compact. U.toScheme is quasi-separated and compact.
2. Transport the derived localizations through Modules.overEquiv U, and similarly on
   every open of U. The homology comparison identifies quasi-coherence and zero stalks.
   Apply ih to this smaller cover and the inverse image of T, which is closed with
   compact complement. This supplies a perfect supported detector P on U.toScheme.
3. Apply exists_perfect_supported_map_lift to P, the zero quasi-coherent object on X,
   and the zero map. The resulting global perfect object Q is supported on T and P is
   a retract of its restriction. Q has quasi-coherent cohomology: its local strictly
   perfect representatives have quasi-coherent finite locally free terms and hence
   quasi-coherent homology; quasi-coherence is local.
4. Derived exact open restriction has a right adjoint, obtained by deriving open direct
   image using K-injective resolutions. Transport the adjunction through the canonical
   open module equivalence to obtain R and adj in the displayed localized categories.
5. Given K supported on T, exact restriction and the homology comparison give a
   supported quasi-coherent object on U. If every Hom from the restriction of Q[n]
   vanishes, the shift comparison and the shifted retract of P make every Hom from
   P[n] vanish. The detector from step 2 makes the restriction of K zero. Notice this
   argument never assumes an invertible global unit and never concludes that K is zero.
   When U is empty its derived category is zero; redundant charts only decrease the
   size of the induced cover and do not affect the argument. -/
theorem exists_supported_detector_open_lift_core
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
          (∀ n : ℤ, Subsingleton
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               (Q.obj⟦n⟧) ⟶
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               K.obj)) →
          IsZero
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               K.obj) := by
  sorry
end AlgebraicGeometry
