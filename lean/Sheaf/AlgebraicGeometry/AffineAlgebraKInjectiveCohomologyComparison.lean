module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import Sheaf.Paper.DerivedSectionsLeftExactBottom
import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Scalar-restriction comparisons elaborate several module-sheaf category instances.
set_option linter.unusedVariables false in
-- The existing statement names its existential isomorphism witness without using it.
/-- Affine K-injective cohomology comparison. The comparison is obtained by affine
sections on an affine basis, using quasi-coherence and K-injectivity, and is
linear over the direct-image algebra.
Source: Stacks Project, Tag 0AVW and Tag 08D4.
(blueprint: new-affine-algebra-kinjective-cohomology-comparison). -/
theorem affine_algebra_kinjective_cohomology_comparison
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ∃ e : (((RingedSpace.moduleDirectImage
          (toDirectImageAlgebraSpace f)).mapHomologicalComplex (.up ℤ)).obj I).homology n ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj (I.homology n), True := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))
  let B := SheafOfModules.{v} (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard B
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let G := F.rightDerivedFunctor
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  -- Scalar restriction is exact and conservative: it leaves underlying sheaves unchanged.
  have heT : T ⋙ SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace) ≅
      SheafOfModules.toSheaf.{v} (moduleRings (directImageAlgebraSpace f)) := Iso.refl _
  have : T.ReflectsIsomorphisms := by
    have : (T ⋙ SheafOfModules.toSheaf.{v}
        (moduleRings Y.toRingedSpace)).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_iso heT.symm
    exact reflectsIsomorphisms_of_comp T
      (SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace))
  have : Limits.PreservesFiniteLimits T := by
    have : Limits.PreservesFiniteLimits
        (T ⋙ SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace)) :=
      Limits.preservesFiniteLimits_of_natIso heT.symm
    exact Limits.preservesFiniteLimits_of_reflects_of_preserves
      T (SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace))
  have : Limits.ReflectsFiniteColimits
      (SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace)) :=
    { reflects := fun _ ↦ Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : Limits.PreservesFiniteColimits T := by
    have : Limits.PreservesFiniteColimits
        (T ⋙ SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace)) :=
      Limits.preservesFiniteColimits_of_natIso heT.symm
    exact Limits.preservesFiniteColimits_of_reflects_of_preserves
      T (SheafOfModules.toSheaf.{v} (moduleRings Y.toRingedSpace))
  have underived : F ⋙ T ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom := Iso.refl _
  let comparison : G ⋙ T.rightDerivedFunctor ≅ schemeDerivedDirectImage f :=
    Functor.isoWhiskerLeft G T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).symm ≪≫
      Functor.rightDerivedFunctorNatIso underived
  have : IsGrothendieckAbelian.{v} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  have hacyc : ∀ (M : C), M.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
      Limits.IsZero ((schemeModuleHigherDirectImage f p).obj M) := by
    intro M hM p hp
    have := hM
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) := ⟨p.toNat, by omega⟩
    have hm : 0 < m := by omega
    have hz := Scheme.Modules.isZero_higherDirectImage_of_isAffineHom f M hm
    exact hz.of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) M m)
  let E := DerivedCategory.Q.obj I
  have hE : schemeDerivedQCohProperty X E := by
    intro i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors C i).app I).symm (hI i)
  let t := DerivedCategory.TStructure.t (C := C)
  let E' := (t.truncGE n).obj E
  let Q := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hzero : Limits.IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{v + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext j
    exact PEmpty.elim j
  have : Q.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{v + 1}⟩⟩
  have hE' : schemeDerivedQCohProperty X E' :=
    DerivedCategory.homologyProperty_truncGE hE n
  let u := (t.truncGEπ n).app E
  let u' : (⟨E, hE⟩ : schemeDerivedQCohCategory X) ⟶ ⟨E', hE'⟩ :=
    (schemeDerivedQCohProperty X).homMk u
  let H := DerivedCategory.homologyFunctor D n
  -- The natural affine comparison makes the truncation projection invertible over O_Y.
  obtain ⟨e⟩ := qcoh_acyclic_derived_pushforward_cohomology f hacyc n
  have : IsIso ((DerivedCategory.homologyFunctor C n).map u) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E n n le_rfl
  have hpush : IsIso (((schemeDerivedQCohProperty X).ι ⋙
      DerivedCategory.homologyFunctor C n ⋙
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map u') := by
    change IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map
      ((DerivedCategory.homologyFunctor C n).map u))
    infer_instance
  have hscheme := (NatIso.isIso_map_iff e u').2 hpush
  change IsIso ((DerivedCategory.homologyFunctor B n).map
    ((schemeDerivedDirectImage f).map u)) at hscheme
  let c : G ⋙ H ⋙ T ≅ schemeDerivedDirectImage f ⋙
      DerivedCategory.homologyFunctor B n :=
    Functor.isoWhiskerLeft G (T.rightDerivedFunctorHomologyFunctorIso n) ≪≫
      Functor.isoWhiskerRight comparison (DerivedCategory.homologyFunctor B n)
  have hT := (NatIso.isIso_map_iff c u).2 hscheme
  change IsIso (T.map (H.map (G.map u))) at hT
  have : IsIso (H.map (G.map u)) := @isIso_of_reflects_iso _ _ _ _ _ _ _ T hT _
  -- Bottom cohomology is computed by the underived left exact functor.
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : Limits.PreservesFiniteLimits F := by
    let U := SheafOfModules.forget (moduleRings (directImageAlgebraSpace f))
    let V := PresheafOfModules.toPresheaf (moduleRings (directImageAlgebraSpace f)).obj
    have : Limits.PreservesFiniteLimits (F ⋙ U ⋙ V) := by
      change Limits.PreservesFiniteLimits
        ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
          PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map f.base).op)
      infer_instance
    exact Limits.preservesFiniteLimits_of_reflects_of_preserves F (U ⋙ V)
  obtain ⟨eB⟩ := F.rightDerivedFunctor_truncated_bottom n
  let eA := asIso (H.map (G.map u)) ≪≫ eB.app E
  obtain ⟨eR⟩ := RingedSpace.derivedModuleDirectImage_computed_by_resolution
    (toDirectImageAlgebraSpace f) (K := I) (J := I) (𝟙 I)
  let eRH := H.mapIso eR
  let eQ := (DerivedCategory.homologyFunctorFactors D n).app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let eI := (DerivedCategory.homologyFunctorFactors C n).app I
  exact ⟨eQ.symm ≪≫ eRH.symm ≪≫ eA ≪≫ F.mapIso eI, trivial⟩

end AlgebraicGeometry
