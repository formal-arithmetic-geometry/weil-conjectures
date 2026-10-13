/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.AlgebraicGeometry.PerfectObjectCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
import Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import Sheaf.AlgebraicGeometry.PerfectNoetherianCohomology
import Sheaf.AlgebraicGeometry.PerfectRelativeFiniteTor
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.Algebra.Category.ModuleCat.TorSymmetry

/-! # Compactness after comparison with proper perfect direct image

Source: Stacks Project, Tags 0B6G, 08EV, 09M1, and 00M3.
(blueprint: lem-sc-proper-perfect-transport-compact).
-/

@[expose] public section
universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Proper perfect direct image of a perfect object is compact after comparison with the
quasi-coherent model. Source: Stacks Project, Tags 09M1, 0B6G, and 0A9R.
(blueprint: lem-sc-proper-perfect-transport-compact). -/
theorem properPerfect_transport_compact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (f : X ⟶ Y) [IsProper f]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj N))
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eR : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.1) :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
    IsCompactObject (R.obj P) := by
  let : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  let : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
  -- Convert second-variable Tor to the first-variable convention of the stalk criterion.
  have hperfect : HasStalkwiseFiniteTorDimension f := by
    intro x
    obtain ⟨n, hn⟩ := hTor x
    refine ⟨n, fun N i hi ↦ ?_⟩
    let A := Y.presheaf.stalk (f x)
    let M : ModuleCat.{u} A := (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
      (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    obtain ⟨e⟩ := nonempty_tor'_flip_iso A i
    let b := BraidedCategory.tensorLeftIsoTensorRight M
    let d : (MonoidalCategory.tensorLeft M).leftDerived i ≅
        (MonoidalCategory.tensorRight M).leftDerived i :=
      { hom := NatTrans.leftDerived b.hom i
        inv := NatTrans.leftDerived b.inv i
        hom_inv_id := by rw [← NatTrans.leftDerived_comp, b.hom_inv_id,
          NatTrans.leftDerived_id]
        inv_hom_id := by rw [← NatTrans.leftDerived_comp, b.inv_hom_id,
          NatTrans.leftDerived_id] }
    exact IsZero.of_iso (hn N i hi) (((e.app M).app N) ≪≫ (d.app N).symm)
  -- Check the three hypotheses of the mixed-universe perfect direct-image criterion.
  obtain ⟨hbounded, hcoherent⟩ := Scheme.perfect_bounded_coherent_cohomology X P.1 hP
  have hsupport : ∀ i : ℤ, Scheme.Modules.HasSupportProperOver f
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P.1) := by
    intro i
    let F : X.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj P.1
    obtain ⟨hq, ht⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp (hcoherent i)
    have : F.IsQuasicoherent := hq
    have : F.IsFiniteType := ht
    let Z : TopologicalSpace.Closeds X :=
      ⟨{x : X | ¬ Subsingleton (F.presheaf.stalk x)},
        (Scheme.Modules.finite_type_module_support_closed X F).2.2.2⟩
    refine ⟨Z, rfl, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)
    infer_instance
  have hpush := Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor
    f P.1 hbounded hcoherent hsupport
      (Scheme.perfect_hasFiniteTorDimensionOver f hperfect P.1 hP)
  -- Restriction carries the comparison isomorphism to each strictly perfect local model.
  apply perfectObjectCompact Y (R.obj P)
  intro y
  obtain ⟨U, hy, K, hK, ⟨eK⟩⟩ := hpush y
  refine ⟨U, hy, K, hK, ⟨?_⟩⟩
  let res := (SheafOfModules.overFunctor.{u}
    (moduleRings Y.toRingedSpace) U).mapDerivedCategory
  exact res.mapIso (eR.app P) ≪≫ eK
end AlgebraicGeometry
