/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections

/-! # Naturality of residue derived homology in a local perfect representative

Source: Stacks Project, Tags 0E62, 06YJ and 0D5S.
(blueprint: lem-sc-residue-stalk-homology-map-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The representing chain arrow induces an isomorphism on residue stalk H⁰.
Source: Stacks Project, Tag 0E62, residue-field argument; Tags 06YJ and 0D5S.
(blueprint: lem-sc-residue-stalk-homology-map-comparison).

Proof: transport the localized module category to the open subscheme by overEquiv.
Each term of P is a retract of a finite free module, hence flat; finite support gives
boundedness above. The single restricted structure sheaf is also bounded and flat.
The K-flat counit therefore computes both residue pullbacks termwise. Its naturality
identifies the pullback of Q(α) with the termwise pullback of α. Restriction to U and
pullback to its residue point compose to pullback to s; the composition comparison is
natural. Apply these comparisons to hα. The resulting arrow is conjugate to the
residue pullback of a by the images of c and e. Degree-zero homology is therefore
invertible by ha. Finally sections on the one-point residue scheme identify termwise
tensor pullback with extension of scalars of the stalk along the residue quotient.
This identification is natural in sheaf maps, so it intertwines the homology arrow
with the displayed homologyMap. Transporting an isomorphism along these comparisons
proves the assertion. No linear frames or vanishing of negative terms are required. -/
theorem isIso_residue_stalk_homologyMap (S : Scheme.{u})
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
 :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    letI : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk ⟨s, hs⟩))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk ⟨s, hs⟩))).left_adjoint_additive
    letI : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        ⟨s, hs⟩).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace ⟨s, hs⟩
    letI : ((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk ⟨s, hs⟩))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    IsIso (HomologicalComplex.homologyMap
      ((((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩ ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk ⟨s, hs⟩))).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0) := by sorry

end AlgebraicGeometry
