/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SixFunctors.RingedDerivedTensorDiagrams

/-! # Symmetric monoidal coherence of the canonical derived tensor comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-lift).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons


/-- The tensor and action-unit portion of a lift, with specified representative models.
Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-lift). -/
structure TensorLift {X Y : Site.{u, w}} (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner) where
  monoidal : @Functor.CoreMonoidal Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal e.left
  tensor_canonical : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      e.left monoidal U V).inv =
      (e.tensorComparison rY rX).hom.app (U, V)
  unit_canonical : ∃ j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅
      SheafOfModules.unit X.ring,
    (∀ M : Y.modules,
      (e.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (e.pullback.obj M)).hom =
        e.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
    e.left.map Y.coherence.unitIso.hom ≫
        derivedPullbackComplexComparison e.pullback e.left e.epsilon
          (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            e.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
            (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
        X.coherence.unitIso.inv =
        (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          e.left monoidal).inv
  symmetric : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      e.left monoidal U V).inv ≫
        (X.symmetry.toBraidedCategory.braiding (e.left.obj U) (e.left.obj V)).hom =
      e.left.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫
        (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          e.left monoidal V U).inv

/-- The uniquely characterized tensor comparison has the inherited symmetric strong
monoidal coherence and the canonical scalar-action unit.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT;
Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-ringed-derived-tensor-lift).

Proof:
1. Use the flat-term K-flat complexes on both sites as simultaneous resolving
representatives. Their tensor products and their images under the presented
pullback remain in that class. The representative characterization of the derived
tensor comparison identifies it with the localized cochain comparison.
2. The ordinary canonical comparison determines a unique coefficient-unit map j
by scalar multiplication. Its cochain lift is invertible. The left-derived
comparison at the unit complex is invertible, so conjugating the localized
cochain unit by the two recorded unit identifications gives the unit isomorphism.
3. The cochain comparison satisfies associativity, both action-unit equations,
and signed symmetry. Use the recorded tensor-model equations to replace each
cochain tensor by its derived tensor. The recorded associator, unitors and
braiding have exactly the same homogeneous pure-tensor formulas. The sectionwise
tensor universal property and the direct-sum summand inclusions identify these
maps. Localizing the cochain equations proves all four coherence diagrams on
resolving representatives. Every derived object has such a representative;
naturality conjugates the diagrams to arbitrary objects.
4. Apply CoreMonoidal.mk' to the inverse tensor and unit isomorphisms. Its tensor
map is the specified canonical comparison by construction. The unit normalization
is the formula from step 2, with the ordinary j characterized in step 2; the
signed-braiding equation is the localized symmetry equation from step 3.
No exactness of extension of scalars, boundedness, or flat structural map is used. -/
theorem tensorLift_exists {X Y : Site.{u, w}} (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
    (hY : ∀ P Q hP hQ,
      rY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom)
    (hX : ∀ P Q hP hQ,
      rX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom) :
    Nonempty (TensorLift e rY rX) := by
  obtain ⟨j, hj, _⟩ := canonicalRingedTensorComparison_unit
    Y.A X.A e.inverseRing e.inverse e.algebraic e.ringMap e.pullback e.object_eq
      e.map_eq e.ordinaryTensor
  obtain ⟨ha, hα, hl, hr, hβ⟩ := canonicalTensorDiagrams e rY rX hY hX j hj
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let F : Y.D ⥤ X.D := e.left
  let a : F.obj (𝟙_ Y.D) ⟶ 𝟙_ X.D := canonicalDerivedUnitComparison e j
  let : IsIso a := ha
  let t : ∀ U V : Y.D, F.obj (U ⊗ V) ≅ F.obj U ⊗ F.obj V :=
    fun U V ↦ (e.tensorComparison rY rX).app (U, V)
  let m : F.CoreMonoidal := Functor.CoreMonoidal.mk'
    (asIso a).symm (fun U V ↦ (t U V).symm)
    (by
      intro U V f W
      have h := (e.tensorComparison rY rX).hom.naturality (Prod.mkHom f (𝟙 W))
      change F.map (f ⊗ₘ 𝟙 W) ≫ (t V W).hom =
        (t U W).hom ≫ (F.map f ⊗ₘ F.map (𝟙 W)) at h
      simpa only [Iso.symm_inv, Functor.map_id, tensorHom_id] using h.symm)
    (by
      intro U V W f
      have h := (e.tensorComparison rY rX).hom.naturality (Prod.mkHom (𝟙 W) f)
      change F.map (𝟙 W ⊗ₘ f) ≫ (t W V).hom =
        (t W U).hom ≫ (F.map (𝟙 W) ⊗ₘ F.map f) at h
      simpa only [Iso.symm_inv, Functor.map_id, id_tensorHom] using h.symm)
    hα hl hr
  exact ⟨{
    monoidal := m
    tensor_canonical := fun _ _ ↦ rfl
    unit_canonical := ⟨j, hj, rfl⟩
    symmetric := hβ }⟩

end CategoryTheory.RingedDerivedComparisons
