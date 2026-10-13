/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Derived transport on a fixed affine chart

Source: Stacks Project, Tag 08EU, affine-local reduction.
(blueprint: lem-pc-projection-mate-affine-chart-transport).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Derived transport on a supplied commuting affine chart square.
The chart geometry is input; the affine adjunction, comparison and objects are
constructed together, rather than asserting an implication for arbitrary objects.
Source: Stacks Project, Tag 08EU, first sentence; the parent node steps 2--3.
(blueprint: lem-pc-projection-mate-affine-chart-transport).

Proof: first apply exists_derivedProjectionMate_openRestriction_comparison to
the actual inverse-image open and restricted morphism. It constructs a local
adjunction, tensor comparison and restricted quasi-coherent objects, together with
an arrow isomorphism from restriction of the supplied p,t mate to their mate.
Its construction uses exact restrictions as reflective localizations. Pullback,
tensor and direct image commute naturally with restriction; consequently they
preserve the inverted maps. Descend p's unit and counit, retaining their triangles.
Descend t and its inverse through the product localization. The localized counit
formula and naturality of t identify the original restricted mate with the local
mate, conjugated by invertible source and target comparisons.
Next pushforward along eV and eZ and their inverses gives exact module equivalences.
Derive them and compose with canonical equivalences between the chosen and standard
localizations. K-flat computations and derived-functor universal properties identify
tensor, pullback and direct image after transport; the commuting square identifies
the transported restricted morphism with g. Conjugate the local adjunction and tensor
comparison to obtain q and s, and transport the two objects to obtain N and E.
Exact equivalences along scheme isomorphisms preserve quasi-coherent cohomology.
Expanding homEquiv in terms of unit and counit shows that the transported mate is
conjugate to the q,s mate. Thus invertibility of the latter implies invertibility
of the original restricted mate. Apply homology in each degree. Exact restriction
commutes naturally with homology, and the over equivalence reflects isomorphisms,
so each original homology map restricted as an over-site morphism is invertible.
Empty opens and unbounded complexes are covered by the same constructions. No
projection-formula invertibility is used to obtain the chart data. -/
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
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))).over V) := by sorry

end AlgebraicGeometry
