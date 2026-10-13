/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization
import Sheaf.Algebra.Homology.KFlatClosure

/-! # Translated-unit comparison on K-flat mapping cones

Source: Stacks Project, Tag 06YJ, mapping-cone exactness; translated-unit
comparison in lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-derived-pullback-translated-unit-kflat-cones).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- On a morphism between K-flat complexes, the translated-unit comparison identifies
its pulled-back cone triangle with a distinguished triangle.

Source: Stacks Project, Tag 06YJ, computation of derived pullback on K-flat
complexes and mapping-cone exactness; translated-unit normalization in the proof
of lem-sc-derived-pullback-translated-unit-triangles, expanded by the agent.
(blueprint: lem-sc-derived-pullback-translated-unit-kflat-cones).

Proof. Represent the unit by the structure sheaf in degree zero. It and its
translate are K-flat, and termwise pullback identifies them with the corresponding
complexes on Z. Compare with derived pullback and the supplied monoidal unit map
to obtain a single e, independent of P, Q and p. For p between K-flat complexes,
its cone is K-flat. The derived-pullback counit is invertible on these three
complexes. Additivity identifies the termwise pullback of the cone with the cone
of the termwise pullback of p, including its inclusion and projection maps.
Rewrite translation as tensor with the shifted unit, by the first-variable
Koszul comparison followed by the shifted left unitor. Under this rewrite the
projection map is the displayed composite: pullback of the inverse rewrite,
the supplied inverse tensorator, e tensor the identity, and the target rewrite.
The tensorator associativity and unit equations give this normalization for the
supplied monoidal structure. Thus the three displayed maps are isomorphic to the
localized cone triangle of termwise pullback of p, which is distinguished.
The construction uses no quasi-coherence or boundedness. For zero P or Q the
same cone and unitor identities apply, and on the empty scheme all maps are the
unique maps. The calculation for the supplied tensorator, rather than merely
exactness for some shift comparison, is part of this assertion. -/
theorem exists_derivedPullback_translatedUnit_kFlat_cones
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∀ (P Q : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        CochainComplex.IsKFlat (R := Y.sheaf) Q →
        let Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y := DerivedCategory.Qh
        let T := Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p)
        Triangle.mk ((derivedPullback f).map T.mor₁) ((derivedPullback f).map T.mor₂)
          ((derivedPullback f).map T.mor₃ ≫
            ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom) ∈
          distTriang (schemeDerivedCategory Z) := by
  let E := Scheme.Modules.tensorPullback f
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction f
  let : E.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  let : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ E
    (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  obtain ⟨e, ε, hε, he⟩ := exists_derivedPullback_kFlat_cone_counit_normalization f
  refine ⟨e, ?_⟩
  intro P Q p hP hQ
  let C := CochainComplex.mappingCone.triangleh p
  let W := (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)).mapTriangle.obj C
  have hcone : W ∈ distTriang (schemeDerivedCategory Z) := by
    apply Functor.map_distinguished
    exact HomotopyCategory.mappingCone_triangleh_distinguished p
  have hP' := hε P hP
  have hQ' := hε Q hQ
  have hC' := hε (CochainComplex.mappingCone p)
    (CochainComplex.isKFlat_mappingCone p hP hQ)
  change IsIso (ε.app C.obj₁) at hP'
  change IsIso (ε.app C.obj₂) at hQ'
  change IsIso (ε.app C.obj₃) at hC'
  let := hP'
  let := hQ'
  let := hC'
  apply CategoryTheory.Pretriangulated.isomorphic_distinguished _ hcone _
  refine Triangle.isoMk _ W (asIso (ε.app C.obj₁)) (asIso (ε.app C.obj₂))
    (asIso (ε.app C.obj₃)) ?_ ?_ ?_
  · exact ε.naturality C.mor₁
  · exact ε.naturality C.mor₂
  · simpa only [C, W, Triangle.mk_mor₃, asIso_hom, Category.assoc] using
      (he P Q p hP hQ).symm

end AlgebraicGeometry
