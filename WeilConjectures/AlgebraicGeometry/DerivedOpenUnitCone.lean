/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Support and quasi-coherence of the derived open-unit cone
## References

* Stacks Project, Tags 09IR and 08D5
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Identify the right adjoint with open direct image through the derived over equivalence.
The underived open pushforward is fully faithful and preserves K-injective complexes,
so its derived functor is fully faithful. Restriction and qcqs direct image preserve
quasi-coherent cohomology (Stacks, Tags 09IR and 08D5). -/
private theorem open_right_adjoint (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) (hqc : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ⥤
      schemeDerivedCategory (Spec (.of A)))
    (adj : (SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory ⊣ R)
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : schemeDerivedQCohProperty (Spec (.of A)) E) :
    schemeDerivedQCohProperty (Spec (.of A))
      (R.obj ((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E)) ∧
      R.Full ∧ R.Faithful := by
  let X := Spec (.of A)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv U
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let L := r ⋙ e.functor
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits L := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits L := comp_preservesFiniteColimits _ _
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  have a : L ⊣ G :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  have : G.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : G.Full :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : G.Faithful :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  let d := e.mapDerivedCategory
  let da : r.mapDerivedCategory ⋙ d.functor ⊣ G.rightDerivedFunctor :=
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      (Functor.mapDerivedCategoryCompIso r e.functor).symm
  let ra : r.mapDerivedCategory ⊣ d.functor ⋙ G.rightDerivedFunctor :=
    (da.comp d.symm.toAdjunction).ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft r.mapDerivedCategory d.unitIso.symm ≪≫
        Functor.rightUnitor _)
  let α := ra.rightAdjointUniq adj
  have hfull : R.Full := Functor.Full.of_iso α
  have hfaithful : R.Faithful := Functor.Faithful.of_iso α
  refine ⟨?_, hfull, hfaithful⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp hqc
  have : QuasiCompact U.ι := quasiCompact_of_compactSpace U.ι
  have hres : schemeDerivedQCohProperty U.toScheme (L.mapDerivedCategory.obj E) := by
    apply (schemeDerivedQCoh_openRestriction_iff X U E).mpr
    intro n
    have := hE n
    exact SheafOfModules.isQuasicoherent_over _ U
  have hpush := schemeDerivedDirectImage_preserves_QCoh U.ι _ hres
  have hpush' : schemeDerivedQCohProperty X
      ((d.functor ⋙ G.rightDerivedFunctor).obj (r.mapDerivedCategory.obj E)) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        (G.rightDerivedFunctor.mapIso
          ((Functor.mapDerivedCategoryCompIso r e.functor).symm.app E))) (hpush n)
  intro n
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (α.app _)) (hpush' n)

/-- The cone of the open restriction unit has quasi-coherent cohomology and vanishes
on the open (Stacks, Tags 09IR and 08D5). -/
theorem derived_open_unit_cone_properties
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
    (hqc : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ⥤
      schemeDerivedCategory (Spec (.of A)))
    (adj : (SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory ⊣ R)
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : schemeDerivedQCohProperty (Spec (.of A)) E)
    (C : schemeDerivedCategory (Spec (.of A)))
    (g : R.obj ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E) ⟶ C)
    (h : C ⟶ E⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (adj.unit.app E) g h ∈ distTriang _) :
    schemeDerivedQCohProperty (Spec (.of A)) C ∧
      IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj C) := by
  obtain ⟨hRE, hfull, hfaithful⟩ := open_right_adjoint A U hqc R adj E hE
  let : R.Full := hfull
  let : R.Faithful := hfaithful
  have htri : (schemeDerivedQCohProperty (Spec (.of A))).IsTriangulated := by
    simpa [supportedProperty] using
      supported_qcoh_isTriangulated (Spec (.of A)) Set.univ
  let := htri
  have hiso : (schemeDerivedQCohProperty (Spec (.of A))).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK n
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK n)
  let := hiso
  refine ⟨(schemeDerivedQCohProperty (Spec (.of A))).ext_of_isTriangulatedClosed₃
    _ hT hE hRE, ?_⟩
  let F := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory
  have : IsIso (adj.counit.app (F.obj E)) := inferInstance
  have hunit : IsIso (F.map (adj.unit.app E)) :=
    isIso_of_comp_hom_eq_id _ (adj.left_triangle_components E)
  exact Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ hT) hunit

end AlgebraicGeometry
