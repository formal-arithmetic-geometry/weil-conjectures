/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison
import WeilConjectures.AlgebraicGeometry.ProjectionMateSchemeIsoTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived transport on a fixed affine chart

## References

* Stacks Project, Tag 08EU.
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option maxHeartbeats 600000 in
-- The two comparisons elaborate several independently chosen derived localizations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived transport on a supplied commuting affine chart square.
The chart geometry is input; the affine adjunction, comparison and objects are
constructed together, rather than asserting an implication for arbitrary objects
(Stacks, Tag 08EU). -/
theorem projectionMate_affineChart_transport
    (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X)
    (V : Y.Opens) (A : Type u) [hA : CommRing A]
    (Z : Scheme.{u}) [hZ : CompactSpace Z] [hZqs : QuasiSeparatedSpace Z]
    (g : Z ⟶ Spec (.of A)) [hg : QuasiCompact g] [hgqs : QuasiSeparated g]
    (eV : Spec (.of A) ≅ V.toScheme) (eZ : Z ≅ (f ⁻¹ᵁ V).toScheme)
    (hcomm : g ≫ eV.hom = eZ.hom ≫ (f ∣_ V)) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    ∃ (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (s : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory Z))
      (N : schemeDerivedQCohCategory (Spec (.of A))) (E : schemeDerivedQCohCategory Z),
      IsIso (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj N.obj ⊗ E.obj)
        (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
          (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj))) →
      ∀ n : ℤ, IsIso (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).map
        (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))).over V) := by
  let _ := hZ
  let _ := hZqs
  let _ := hg
  let _ := hgqs
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
  obtain ⟨pV, tV, MV, LV, ⟨a⟩⟩ :=
    exists_derivedProjectionMate_openRestriction_comparison f p t M L V
      (f ⁻¹ᵁ V).toScheme (f ∣_ V) rfl HEq.rfl
  obtain ⟨e, q, s, N, E, ⟨b⟩⟩ :=
    projectionMate_schemeIso_transport (f ⁻¹ᵁ V).toScheme V.toScheme Z (Spec (.of A))
      (f ∣_ V) g eZ eV hcomm pV tV MV LV
  refine ⟨q, s, N, E, ?_⟩
  intro hmate n
  have := hmate
  have hlocal := (Arrow.isIso_iff_isIso_of_isIso b.hom).mp
    (show IsIso (e.functor.map _) from inferInstance)
  have hrestricted : IsIso ((schemeOpenRestriction Y V).mapDerivedCategory.map
      (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))) :=
    (Arrow.isIso_iff_isIso_of_isIso a.hom).mpr hlocal
  have := hrestricted
  have hhom : IsIso ((schemeOpenRestriction Y V).map
      ((DerivedCategory.homologyFunctor _ n).map
        (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
          ((derivedPullback f).obj M.obj ⊗ L.obj)
          (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
            (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj))))) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction Y V).mapDerivedCategoryHomologyFunctorIso n) _).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction Y V).mapDerivedCategory.map _))
        infer_instance)
  have : IsIso ((Scheme.Modules.overEquiv V).functor.map
      (((DerivedCategory.homologyFunctor _ n).map
        (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
          ((derivedPullback f).obj M.obj ⊗ L.obj)
          (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
            (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))).over V)) := hhom
  exact isIso_of_reflects_iso _ (Scheme.Modules.overEquiv V).functor

end AlgebraicGeometry
