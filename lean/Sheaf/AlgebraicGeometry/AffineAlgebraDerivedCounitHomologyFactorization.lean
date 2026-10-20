/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Sheaf.AlgebraicGeometry.AffineDerivedCohomology
import Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.AffineAlgebraModuleAdjunctionIsos
import Sheaf.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization
import Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh

/-! # Cohomology of the affine algebra derived counit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- The scalar-restriction comparison elaborates several sheaf category instances.
/-- Under the cohomology comparison, the derived affine algebra counit is the
underived counit applied to the cohomology module.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-derived-counit-homology-factorization).

Proof: Exact conservative scalar restriction from f_*O_X to O_Y compares
Rg_* with Rf_*. The affine unbounded cohomology formula and the affine module
correspondence show that Rg_* preserves quasi-coherent cohomology. The natural
acyclic-pushforward cohomology comparison, together with the underived counit
isomorphisms, shows that Rg_* reflects isomorphisms between complexes with
quasi-coherent cohomology. The derived unit homology factorization makes the
unit at Rg_*K invertible. The right triangle identity then makes Rg_* of the
counit invertible; preservation of quasi-coherence by derived pullback allows
reflection to the counit itself. Compose its homology isomorphism with the
inverse of the ordinary counit isomorphism to define e. Inverse cancellation
proves the equation. The conclusion requires existence of e, rather than a
specified canonical comparison. No boundedness or nonemptiness is assumed. -/
theorem affine_algebra_derived_counit_homology_factorization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    [Limits.PreservesFiniteLimits P]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj
          (L.obj ((RingedSpace.derivedModuleDirectImage
            (toDirectImageAlgebraSpace f)).obj K)) ≅
        P.obj ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).map
          (adj.counit.app K) =
        e.hom ≫ a.counit.app ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).obj K) := by
  -- Compare with scheme pushforward after exact, conservative scalar restriction.
  let G := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let G₀ := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let : HasDerivedCategory (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) :=
    HasDerivedCategory.standard _
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
  have underived : G₀ ⋙ T ≅
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom := Iso.refl _
  let comparison : G ⋙ T.rightDerivedFunctor ≅ schemeDerivedDirectImage f :=
    Functor.isoWhiskerLeft G T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso G₀ T).symm ≪≫
      Functor.rightDerivedFunctorNatIso underived
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n
  obtain ⟨_, hunit, hcounit⟩ := affine_algebra_module_adjunction_isos f P a
  -- The affine cohomology formula also gives quasi-coherence over the algebra.
  have hG : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      directImageAlgebraDerivedQCohProperty f (G.obj E) := by
    intro E hE i
    obtain ⟨⟨e⟩, hq⟩ := schemeHigherDirectImage_of_affine f E hE i
    let HY := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) i
    let c := (T.rightDerivedFunctorHomologyFunctorIso i).app (G.obj E) ≪≫
      HY.mapIso (comparison.app E) ≪≫ e
    apply ((Scheme.Modules.affine_module_correspondence f).1 _).mpr
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      c.symm hq
  have := IsSeparated.of_isAffineHom f
  have : IsGrothendieckAbelian.{v} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  have hacyc : ∀ (F : SheafOfModules.{v} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        Limits.IsZero ((schemeModuleHigherDirectImage f p).obj F) := by
    intro F hF p hp
    have := hF
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) := ⟨p.toNat, by omega⟩
    have hm : 0 < m := by omega
    have hz := Scheme.Modules.isZero_higherDirectImage_of_isAffineHom f F hm
    exact hz.of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F m)
  -- The natural cohomology comparison and the underived counit detect isomorphisms.
  have hreflect {E F : schemeDerivedCategory X}
      (hE : schemeDerivedQCohProperty X E) (hF : schemeDerivedQCohProperty X F)
      (u : E ⟶ F) (hu : IsIso (G.map u)) : IsIso u := by
    apply (DerivedCategory.isIso_iff _ _).2
    intro i
    let Hi := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings X.toRingedSpace)) i
    let u' : (⟨E, hE⟩ : schemeDerivedQCohCategory X) ⟶ ⟨F, hF⟩ :=
      (schemeDerivedQCohProperty X).homMk u
    obtain ⟨e⟩ := qcoh_acyclic_derived_pushforward_cohomology f hacyc i
    have hmap : IsIso (((schemeDerivedQCohProperty X).ι ⋙
        schemeHigherDirectImage f i).map u') := by
      have : IsIso ((G ⋙ T.rightDerivedFunctor).map u) := by
        change IsIso (T.rightDerivedFunctor.map (G.map u))
        infer_instance
      have hiso := (NatIso.isIso_map_iff comparison u).1 this
      change IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((schemeDerivedDirectImage f).map u))
      infer_instance
    have hpush := (NatIso.isIso_map_iff e u').1 hmap
    change IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map (Hi.map u))
      at hpush
    have : IsIso (T.map (G₀.map (Hi.map u))) := hpush
    have : IsIso (G₀.map (Hi.map u)) := isIso_of_reflects_iso _ T
    have : IsIso (a.counit.app (Hi.obj E)) := hcounit _ (hE i)
    have : IsIso (a.counit.app (Hi.obj F)) := hcounit _ (hF i)
    have ht : IsIso (P.map (G₀.map (Hi.map u))) := by infer_instance
    have heq := a.counit.naturality (Hi.map u)
    change P.map (G₀.map (Hi.map u)) ≫ a.counit.app (Hi.obj F) =
      a.counit.app (Hi.obj E) ≫ Hi.map u at heq
    exact IsIso.of_isIso_fac_left heq.symm
  -- Invert the unit at G(K), use the triangle identity, then reflect the counit.
  have hGK := hG K hK
  have hu : IsIso (adj.unit.app (G.obj K)) := by
    apply (DerivedCategory.isIso_iff _ _).2
    intro i
    obtain ⟨e, he⟩ :=
      affine_algebra_derived_unit_homology_factorization f P a L adj (G.obj K) hGK i
    have := hunit _ (hGK i)
    have : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) i).map
        (adj.unit.app (G.obj K)) ≫ e.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  have hGc : IsIso (G.map (adj.counit.app K)) :=
    isIso_of_hom_comp_eq_id _ (adj.right_triangle_components K)
  have hc : IsIso (adj.counit.app K) :=
    hreflect (affine_algebra_derived_pullback_preserves_qcoh f L adj _ hGK) hK _ hGc
  have : IsIso (a.counit.app (H.obj K)) := hcounit _ (hK n)
  -- The statement asks for some source comparison, so compose the two counits.
  let c := H.map (adj.counit.app K)
  refine ⟨asIso c ≪≫ (asIso (a.counit.app (H.obj K))).symm, ?_⟩
  change c = (c ≫ inv (a.counit.app (H.obj K))) ≫ a.counit.app (H.obj K)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
