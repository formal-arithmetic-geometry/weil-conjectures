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
import WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartData
import WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartTransport

/-! # A local affine comparison certificate for a supplied projection mate

## References

* Stacks Project, Tag 08EU.
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

-- Eliminating the nested chart witnesses elaborates two standard localization instances.
/-- Every affine chart supplies an affine projection mate whose invertibility implies
invertibility of the original mate on the cohomology sheaves restricted to that chart.
There is no affine projection-formula hypothesis in this comparison theorem
(Stacks, Tag 08EU). -/
theorem exists_projectionMate_affineChart_certificate
    (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ (A : Type u) (hA : CommRing A),
      letI := hA
      ∃ (Z : Scheme.{u}) (hZ : CompactSpace Z) (hZqs : QuasiSeparatedSpace Z),
        letI := hZ
        letI := hZqs
        letI := HasDerivedCategory.standard
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
        letI := HasDerivedCategory.standard
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        ∃ (g : Z ⟶ Spec (.of A)) (hg : QuasiCompact g) (hgqs : QuasiSeparated g),
          letI := hg
          letI := hgqs
          ∃ (eV : Spec (.of A) ≅ V.toScheme)
            (eZ : Z ≅ (f ⁻¹ᵁ V).toScheme),
            g ≫ eV.hom = eZ.hom ≫ (f ∣_ V) ∧
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
  obtain ⟨A, hA, Z, hZ, hZqs, g, hg, hgqs, eV, eZ, hcomm⟩ :=
    exists_projectionMate_affineChart_data X Y f V hV
  let := hA
  let := hZ
  let := hZqs
  let := hg
  let := hgqs
  obtain ⟨q, s, N, E, htransport⟩ :=
    projectionMate_affineChart_transport X Y f p t M L V A Z g eV eZ hcomm
  exact ⟨A, hA, Z, hZ, hZqs, g, hg, hgqs, eV, eZ, hcomm, q, s, N, E, htransport⟩

end AlgebraicGeometry
