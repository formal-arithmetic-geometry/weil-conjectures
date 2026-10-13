/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Nonzero residue coefficient detected by derived homology

Source: Stacks Project, Tag 0E62, residue-field argument, with Tag 0BCD.
(blueprint: lem-sc-residue-homology-rank-one-coefficient).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- In linear coordinates on the source and target stalks, the degree-zero
coefficient of a connective perfect chain representative has nonzero residue.
Source: Stacks Project, Tag 0E62, residue-field argument, with Tag 0BCD.
(blueprint: lem-sc-residue-homology-rank-one-coefficient).

Proof: identify the localized module site with the open subscheme. Every term
of the strictly perfect complex is a summand of a finite free module, hence flat;
finite support makes the complex bounded above. Termwise flat pullback computes
its derived residue pullback. The same comparison applies to the single source.
The restriction and pullback comparison along the residue point identifies the
representing equality with the original derived residue arrow, conjugated by
the images of c and e. Naturality of these comparisons therefore makes its
residue H^0 map invertible. The source H^0 is the residue field. Since negative
terms vanish, the target H^0 injects into the degree-zero residue term: there
are no incoming boundaries. Thus the nonzero image of the source generator in
H^0 remains nonzero in that term. Linear coordinates σ and τ base change to
residue-field coordinates, and the image is precisely the residue of
τ(α^0(σ⁻¹(1))). It is therefore nonzero. This argument works for any linear
frames: changing either frame multiplies the coefficient by a local unit.
No invertibility of the original stalk component is asserted. The point rules
out empty opens and ensures the local ring and its residue field are nonzero. -/
theorem residue_ne_zero_rankOne_stalk_coefficient (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a)))
    (c : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))))
    (α : (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶ P)
    (hα : DerivedCategory.Q.map α = c.inv ≫
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫
        e.hom)
    (σ : ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).obj
      ((Scheme.Modules.overEquiv U).functor.obj
        (((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).obj
              (SheafOfModules.unit S.ringCatSheaf))).X 0))) ≃ₗ[
                U.toScheme.presheaf.stalk ⟨s, hs⟩] U.toScheme.presheaf.stalk ⟨s, hs⟩)
    (τ : ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).obj
      ((Scheme.Modules.overEquiv U).functor.obj (P.X 0))) ≃ₗ[
        U.toScheme.presheaf.stalk ⟨s, hs⟩] U.toScheme.presheaf.stalk ⟨s, hs⟩) :
    IsLocalRing.residue (U.toScheme.presheaf.stalk ⟨s, hs⟩)
      (τ (((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).map
        ((Scheme.Modules.overEquiv U).functor.map (α.f 0))).hom (σ.symm 1))) ≠ 0 := by sorry

end AlgebraicGeometry
