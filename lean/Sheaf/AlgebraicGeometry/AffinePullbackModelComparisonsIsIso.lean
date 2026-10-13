/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Canonical affine model comparisons

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-pullback-sections-model-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Canonical comparison from localized sections to derived affine sections.
Source: Stacks Project, Tag 06Z0, ordinary-to-derived comparison. -/
def affineModelSectionsComparison (A : CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
        (((affineGlobalSections (𝟙 (Spec A))).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (affineDerivedGlobalSections (𝟙 (Spec A))).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (affineGlobalSections (𝟙 (Spec A))).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
    (affineGlobalSections (𝟙 (Spec A))).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app K) ≫
    (affineGlobalSectionsDerivedIso (𝟙 (Spec A))).hom.app (DerivedCategory.Q.obj K)

/-- The fixed left-derived counit, transported from homotopy to complex localization.
Source: Stacks Project, Tag 0D5S; the same counit fixes canonicalPullbackAdjunction. -/
def affineModelPullbackComparison {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [(Scheme.Modules.tensorPullback g).Additive]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj K) :=
  (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _

set_option synthInstance.maxHeartbeats 100000 in
-- Affine carrier identifications require additional instance search.
set_option maxHeartbeats 800000 in
-- Affine carrier identifications require additional elaboration heartbeats.
/-- The two canonical comparison maps used to form the affine pullback sections model
are invertible on a K-flat associated-sheaf complex.
Source: Stacks Project, perfect.tex, Tags 08DV, 08DW(2), and 06Z0.
(blueprint: new-affine-pullback-model-comparisons-isIso).
Proof: translate generic module K-flatness into the acyclic tensor criterion using
HomotopyCategory.kFlat_iff_preserves_acyclic and kFlat_quotient_obj_iff.
Apply isKFlat_tilde to obtain sheaf K-flatness. The counit supplied by
exists_derivedPullback is invertible on this complex. Uniqueness of left-derived
functors compares that counit with the fixed counit of
exists_derivedPullbackComposition; both Q/Qh transport factors are isomorphisms.
For the sections comparison, full faithfulness of Spec writes g as Spec.map of a
ring map. The natural tilde pullback isomorphism identifies termwise pullback of K
with tilde of the scalar-extended complex, compatibly with differentials.
Naturality of the right-derived unit transports its invertibility from
this tilde complex, where affineTildeDerivedSectionsUnit_isIso applies. The other
three factors defining affineModelSectionsComparison are isomorphisms. No
boundedness or flatness of the ring map is used. For the zero complex and zero
rings the same comparison maps are maps between zero objects and remain invertible. -/
theorem affinePullbackModelComparisons_isIso
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [hT : (tilde.functor R).Additive] [hP : (Scheme.Modules.tensorPullback g).Additive]
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let K := (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (tilde.functor R) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M
    IsIso (affineModelPullbackComparison g K) ∧
      IsIso (affineModelSectionsComparison B
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj K)) := by sorry

end AlgebraicGeometry
