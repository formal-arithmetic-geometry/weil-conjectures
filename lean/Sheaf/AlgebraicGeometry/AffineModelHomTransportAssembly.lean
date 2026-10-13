/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonData
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.CategoryTheory.HomCongr

/-! # Hom transport from coherent affine object comparisons
Source: Stacks Project, Tags 06Z0 and 09RE.
(blueprint: lem-pc-affine-model-hom-transport-assembly). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_affineTildeHomEquiv (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ h : (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) ≃
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
          _ _ _ _ (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
            (tilde.functor A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ⟶
       DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
          _ _ _ _ (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
            (tilde.functor A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N)),
      ∀ f : M ⟶ N, h (DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
            _ _ _ _ (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
            (tilde.functor A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).map f) := by
  have h := exists_affineQCohDerivedEquivalence.{u, u + 1, w} (A : Type u)
  obtain ⟨e, hα, _⟩ := h
  obtain ⟨α⟩ := hα
  let L : DerivedCategory.{u + 1} (ModuleCat.{u} A) ⥤
      schemeDerivedCategory (Spec A) :=
    e.functor ⋙ (schemeDerivedQCohProperty (Spec A)).ι
  let ff : L.FullyFaithful :=
    e.fullyFaithfulFunctor.comp (schemeDerivedQCohProperty (Spec A)).fullyFaithfulι
  refine ⟨(ff.homEquiv (X := DerivedCategory.Q.obj M) (Y := DerivedCategory.Q.obj N)).trans
    (Iso.homCongr (α.app M) (α.app N)), ?_⟩
  intro f
  change (α.app M).inv ≫ L.map (DerivedCategory.Q.map f) ≫ (α.app N).hom = _
  exact (congrArg (fun z ↦ (α.app M).inv ≫ z) (α.hom.naturality f)).trans
    ((α.app M).inv_hom_id_assoc _)


/-- Convert coherent object comparisons to derived module Hom comparisons.
Source: Stacks Project, Tags 06Z0, 08DW and 09RE.
(blueprint: lem-pc-affine-model-hom-transport-assembly).

Proof: For any ring A, apply exists_affineQCohDerivedEquivalence to obtain the
quasi-coherent derived equivalence and its localization factorization. Compose
its fully faithful functor with the full inclusion into the sheaf-module derived
category. The factorization isomorphism, evaluated at two complexes, conjugates
its Hom equivalence to an equivalence with Homs between the two tilde complexes.
Naturality of that isomorphism shows that localization of a chain map is sent
to localization of its termwise tilde map: precompose naturality by the inverse
component and cancel inverse followed by component. No boundedness is needed.
Choose these Hom equivalences simultaneously over rings and pairs of complexes.
At each stage compose with the fully faithful Hom equivalence of d(j), then
conjugate by alphaE(j), alphaK(j). At the limit use dlim and betaE, betaK.
On any chain map these composites are precisely the conjugated sheafified maps
in hcomp, by the just-proved chain-map formula. Apply its finite-stage and limit
identities. Thus the two displayed compatibility equations follow by congruence
under functor maps, conjugations, and perfectStageMap or perfectLimitMap.
This argument applies to arbitrary complexes, zero rings and zero objects; it
takes F,E,K as parameters and does not provide the geometric comparisons in hcomp.
In particular this is only Hom transport, not the finite-projective or geometric
parts of the specified-model comparison. -/
theorem exists_affineModelHomTransportAssembly
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hcomp : affineModelComparisonData R c i Y s P Q F C E K) :
      ∃ (stage : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
           (derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj Q))
        (limit :
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          stage k (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) =
            perfectStageMap R s j.val.property hjk
              (stage j (DerivedCategory.Q.map f))) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          limit (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
              (C.ι.app ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm)
              E K f)) =
            perfectLimitMap R c s j.val.property
              (stage j (DerivedCategory.Q.map f))) := by sorry

end AlgebraicGeometry
