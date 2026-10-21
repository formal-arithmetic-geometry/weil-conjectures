/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

import all Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle
import Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage
import Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # BoundedConstructibleTensorPreservation

The tensor unit and the two finite truncation inductions for tensor closure.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The coefficient object is bounded constructible and is the tensor unit. This is the unit
clause needed to form the monoidal bounded-constructible subcategory.
Source: the unit clause of `lem-sfb-dc-tensor-preserves` in the blueprint.
(blueprint: lem-sfb-dc-tensor-unit) -/
theorem boundedConstructible_tensor_unit
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    boundedConstructible (condensedRingObj Λ X.left)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left)))) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)
  let U := (𝟙_ (DerivedCategory C))
  let eUnit : (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) ≅ U :=
    DerivedCategory.singleFunctorObjUnitIso C
  have eb : DerivedCategory.TStructure.t.bounded U := by
    refine ⟨⟨0, DerivedCategory.TStructure.t.isGE_of_iso eUnit 0⟩, ?_⟩
    exact ⟨0, DerivedCategory.TStructure.t.isLE_of_iso eUnit 0⟩
  letI : U.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eUnit 0
  letI : U.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eUnit 0
  refine ⟨eb, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (𝟙_ C)
    have hr : IsConstructibleModuleObject (condensedRingObj Λ X.left)
        (Mod.regular (condensedRingObj Λ X.left)) := by
      exact ⟨Scheme.Stratification.trivial X.left, fun i ↦ by
        refine ⟨.singleton (𝟙 X.left) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
        let G := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1}
          ((Scheme.Stratification.trivial X.left).immersion i)
        let F := G.obj (condensedRingObj Λ X.left)
        let H := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1}
          (𝟙 ((Scheme.Stratification.trivial X.left).domain i))
        let e' : (H.mapMod F).obj ((G.mapMod (condensedRingObj Λ X.left)).obj
            (Mod.regular (condensedRingObj Λ X.left))) ≅ Mod.regular (H.obj F) :=
          Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
            MonoidalCategory.whiskerLeft_id, Category.id_comp])
        let e1 : Mod.regular (H.obj F) ≅ Mod.finiteFree (H.obj F) 1 :=
          (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular (H.obj F))).symm
        refine ⟨1, 0, 0, ⟨e'.symm ≪≫ e1 ≪≫ ?_⟩⟩
        exact (cokernelZeroIsoTarget (X := Mod.finiteFree (H.obj F) 0)
          (Y := Mod.finiteFree (H.obj F) 1)).symm⟩
    exact constructible_of_iso (condensedRingObj Λ X.left) e.symm hr
  · by_cases hneg : n < 0
    · have hz := DerivedCategory.isZero_of_isGE U 0 n hneg
      exact constructible_of_isZero (condensedRingObj Λ X.left) hz
    · have hpos : 0 < n := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hn)
      have hz := DerivedCategory.isZero_of_isLE U 0 n hpos
      exact constructible_of_isZero (condensedRingObj Λ X.left) hz


/-- The derived tensor of two bounded constructible module-object complexes is bounded
constructible. This is the tensor-closure clause of the ell-adic finiteness theorem.
Source: `lem-sfb-dc-tensor-preserves` in the blueprint.
(blueprint: lem-sfb-dc-tensor-preserves) -/
theorem boundedConstructible_tensor_closure
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((-⊗ᴸ-(X.left)⟦Λ⟧).obj K).obj L) := by
  let P := boundedConstructible (condensedRingObj Λ X.left)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : P.IsTriangulated := isTriangulated_boundedConstructible_ellAdic Λ X.left
  change P (K ⊗ L)
  apply prop_of_boundedConstructibleModule (P.inverseImage (tensorLeft K)) ?_ hL
  intro G hG
  exact prop_of_boundedConstructibleModule
    (P.inverseImage (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)))
    (fun F hF ↦ boundedConstructible_tensor_single Λ X F G hF hG) hK

end AlgebraicGeometry.ProEtale.CondensedRing
