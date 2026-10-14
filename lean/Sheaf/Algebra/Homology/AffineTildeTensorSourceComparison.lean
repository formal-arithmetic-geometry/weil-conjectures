/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility

/-! # Counit-normalized affine derived tensor source

Source: Stacks Project, Tags 06Y6, 08DW and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) sourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) sourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) sourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := SheafOfModules.instAbelian Y.ringCatSheaf


local instance sourceComparisonTildeAdditive (C : Type u) [CommRing C] :
    (affineTildeFunctor C).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
local instance sourceComparisonTildeHomology (C : Type u) [CommRing C] :
    (affineTildeFunctor C).PreservesHomology := tilde_preservesHomology C
local instance sourceComparisonTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affineTildeFunctor C) :=
  (affineTildeFunctor C).preservesFiniteLimits_of_preservesHomology
local instance sourceComparisonTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affineTildeFunctor C) :=
  (affineTildeFunctor C).preservesFiniteColimits_of_preservesHomology

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance sourceComparisonPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

/-- Ordinary source identification: inverse tensor/tilde comparison followed by
pullback of the affine pushforward comparison. This is a concrete construction.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison). -/
def affineTildeTensorOrdinarySourceIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ≅
    ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let : (Scheme.Modules.tensorPullback g).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj M
  let : (affineTildeFunctor R).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (affineTildeFunctor B).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap R B)).Additive :=
    ModuleCat.extendScalars_additive _
  let θ : affineTildeFunctor R ⋙ Scheme.Modules.tensorPullback g ≅
      ModuleCat.extendScalars (algebraMap R B) ⋙ affineTildeFunctor B :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
  let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let : (affineTildeFunctor A).Additive :=
    instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : P.Additive := inferInstance
  let : (affineTildeFunctor A ⋙ P).Additive := inferInstance
  let : (affineTildeFunctor A ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affineTildeFunctor A).map_zero]
      exact P.map_zero _ _⟩
  let s : ((affineTildeFunctor R).mapHomologicalComplex (.up ℤ)).obj N ≅
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) :=
    (Functor.mapHomologicalComplexCompIso
      (affineTildePushforwardComparison A R (algebraMap R A)) (.up ℤ)).app M
  exact δ.symm ≪≫
    ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).mapIso s

/-- The first two factors of the raw tensor map, before any coefficient map.
Source: Stacks Project, Tags 06Y6 and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison). -/
def affineTildeTensorDerivedCounit
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affineTildeFunctor B)) :
    F₀.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)))) ⟶
    DerivedCategory.Q.obj
      (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj M))) := by
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let N' := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj N
  exact eqToHom (congrArg (fun G ↦ G.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N)))) hF₀) ≫
    (affineTildeFunctor B).mapDerivedCategory.map
      (m.counit.app ((HomotopyCategory.quotient _ _).obj N)) ≫
    ((affineTildeFunctor B).mapDerivedCategoryFactors.app N').hom

/-- The affine source comparison is normalized by its derived counit.
Source: Stacks Project, Tags 06Y6, 08DW, 06Z0, 08D4, 08HY and 0AVW.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).

Proof: first transport along the supplied defining equality of F0.
Resolve the R-restriction of M by a termwise flat K-flat complex P.
The universal counit of m identifies its value on this restriction with the
B-extension of P. Exact tilde sends the augmentation to a quasi-isomorphism.
Its K-flat image computes g-pullback, with the unit-normalized tensor/tilde
identification. Naturality of the two universal counits gives the displayed
normalization equation; comparison on P determines it after localization.
Compose the tensor comparison with pullback of the concrete ordinary affine
pushforward iso. The actual affine pushforward right-derived unit is invertible:
choose a K-injective resolution, apply affinePushforward_resolution_quasiIso,
and use naturality of the unit. Pullback of this unit gives chi with the stated
source. For every commutative affine square, apply the pinned derived-unit
compatibility theorem. Precompose its equality with the source comparison;
the counit normalization proved above gives the displayed universal equation.
This equation involves ordinary exchange, and does not identify the coefficient
map or assert the final mate equality. No boundedness is imposed. For the zero complex and zero
rings the same counit equations hold on the unique zero objects. -/
theorem exists_affineTildeTensorSourceComparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affineTildeFunctor B)) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    ∃ χ : F₀.obj
          (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj M)))) ≅
        (derivedPullback g).obj ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj H)),
      ∀ (φ : A →+* D) (ψ : B →+* D)
        (hw : Spec.map (CommRingCat.ofHom φ) ≫ f =
          Spec.map (CommRingCat.ofHom ψ) ≫ g),
        let p := Spec.map (CommRingCat.ofHom φ)
        let f' := Spec.map (CommRingCat.ofHom ψ)
        χ.hom ≫ schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H) ≫
          (schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H) =
        affineTildeTensorDerivedCounit R A B D M m F₀ hF₀ ≫
          DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
          DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
          (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) := by sorry

end AlgebraicGeometry
