/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProjectionMateExact

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Module-object and ringed-topos derived comparison

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).

## Main definitions and statements

- `ordinary_exact_flat_kflat`, `ordinary_monoidal`: the ordinary equivalence clauses.
- `derivedPullComparison`, `derivedPushComparison`, `derived_homEquiv`: derived operations.
- `tensorPullComparison`, `delta_comparison`, `mu_comparison`: specified tensor maps.
- `composition_comparison`, `projection_comparison`: composition and the proper mate.
- `open_homEquiv`, `openProjection_comparison`: open adjunction and its unit mate.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Additivity, exactness, flatness and the two recorded K-flat definitions agree.
Source: Stacks 00YV, 03EK and 0G7E
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: use internal_section_tensor_comparison on the pulled-back coefficient ring.
It preserves kernels and cokernels on the unchanged abelian sheaf, hence is exact
and additive. The normalized tensor isomorphism conjugates the fixed-factor tensor
functors, giving flatness in both directions. Termwise it identifies the signed
total tensors and preserves and reflects acyclicity. Signed symmetry exchanges
P tensor N with N tensor P, relating IsKFlatModuleObject to the independent
coefficient sheaf definition. The quasi-inverse supplies every target acyclic test. -/
theorem ordinary_exact_flat_kflat (X : Scheme.{u}) :
    (equivalence Λ X).functor.Additive ∧
    exactFunctor _ _ (equivalence Λ X).functor ∧
    (∀ M : internalModules Λ X,
      exactFunctor _ _ (tensorRight M) ↔
        SheafOfModules.IsFlatOnSite ((equivalence Λ X).functor.obj M)) ∧
    (∀ P : CochainComplex (internalModules Λ X) ℤ,
      IsKFlatModuleObject X (CommMon.mk (condensedRingObj Λ X)) P ↔
        CochainComplex.IsKFlatIndependentCoefficients
          (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  obtain ⟨e, e₀, hpure, hunit, hnat, hassoc, hl, hr, hb, ht, ha, hf, hk⟩ := h.2
  refine ⟨inferInstance, h.1, hf, ?_⟩
  intro P
  rw [← hk P]
  constructor
  · intro hP N hN
    exact (hP N hN).of_iso (β_ P N)
  · intro hP N hN
    exact (hP N hN).of_iso (β_ N P)

set_option maxHeartbeats 800000 in
-- Comparing the two normalized monoidal witnesses elaborates the sheaf tensor constraints.
/-- The chosen ordinary tensor maps obey all symmetric-monoidal coherence diagrams.
Source: Stacks 03EK (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: these are exactly the maps chosen from internal_section_tensor_comparison,
whose proof checks the naturality, associator, unitors and symmetry on local pure
tensors. The regular-unit comparison fixes local scalars, so the unit diagrams
are the scalar action laws. Local generation extends each equality to the sheaf. -/
theorem ordinary_monoidal (X : Scheme.{u}) :
    (∀ (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N'),
      (equivalence Λ X).functor.map (f ⊗ₘ g) ≫
          (ordinaryTensorComparison Λ X M' N').hom =
        (ordinaryTensorComparison Λ X M N).hom ≫
          ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g)) ∧
    (∀ M N P : internalModules Λ X,
      (ordinaryTensorComparison Λ X (M ⊗ N) P).hom ≫
          (ordinaryTensorComparison Λ X M N).hom ▷ (equivalence Λ X).functor.obj P ≫
          (α_ _ _ _).hom =
        (equivalence Λ X).functor.map (α_ M N P).hom ≫
          (ordinaryTensorComparison Λ X M (N ⊗ P)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryTensorComparison Λ X N P).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X (𝟙_ _) M).hom ≫
          (ordinaryUnitComparison Λ X).hom ▷ (equivalence Λ X).functor.obj M ≫
          (λ_ _).hom = (equivalence Λ X).functor.map (λ_ M).hom) ∧
    (∀ M : internalModules Λ X,
      (ordinaryTensorComparison Λ X M (𝟙_ _)).hom ≫
          (equivalence Λ X).functor.obj M ◁ (ordinaryUnitComparison Λ X).hom ≫
          (ρ_ _).hom = (equivalence Λ X).functor.map (ρ_ M).hom) ∧
    (∀ M N : internalModules Λ X,
      (ordinaryTensorComparison Λ X M N).hom ≫ (β_ _ _).hom =
        (equivalence Λ X).functor.map (β_ M N).hom ≫
          (ordinaryTensorComparison Λ X N M).hom) := by
  have h := InternalAbelianSheafModule.internal_section_tensor_comparison.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  obtain ⟨e, e₀, hpure, hunit, hnat, hassoc, hleft, hright, hbraid, _⟩ := h.2
  have he (M N : internalModules Λ X) : e M N = ordinaryTensorComparison Λ X M N :=
    (ordinaryTensorComparison_existsUnique Λ X M N).unique (hpure M N)
      (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec
  have he₀ : e₀ = ordinaryUnitComparison Λ X :=
    (ordinaryUnitComparison_existsUnique Λ X).unique hunit
      (ordinaryUnitComparison_existsUnique Λ X).exists.choose_spec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using hnat
  · simpa only [he] using hassoc
  · simpa only [he, he₀] using hleft
  · simpa only [he, he₀] using hright
  · simpa only [he] using hbraid

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The specified internal derived tensor map is invertible.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: resolve both factors by flat-term K-flat complexes. The ordinary pullback
mate is invertible on every pair of modules, so its signed total is invertible.
Pullback preserves flat modules and acyclic complexes, hence these resolutions
compute all three derived tensors and their specified comparison. Localization
and naturality give invertibility on arbitrary unbounded derived objects. -/
@[instance] theorem internalDelta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    IsIso (((internalDelta Λ f).app M).app N) := by
  let _ := (inferInstance : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X))
  unfold internalDelta
  infer_instance

/-- The actual module-object proper projection arrow, the adjoint of counit after delta.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ Y).obj ((internalDerivedPushforward Λ f).obj K)).obj L ⟶
      (internalDerivedPushforward Λ f).obj
        (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((internalDelta Λ f).app ((internalDerivedPushforward Λ f).obj K)).app L ≫
      (((CondensedRing.derivedTensor Λ X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app K)).app
          ((internalDerivedPullback Λ f).obj L)))

/-- The precise ringed projection mate alpha, in the dependency's uncurried interface.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) (L : DerivedCategory (modules Λ Y)) :
    (tensor Λ Y).obj ((derivedPushforward Λ f).obj K, L) ⟶
      (derivedPushforward Λ f).obj ((tensor Λ X).obj (K, (derivedPullback Λ f).obj L)) :=
  derivedProjectionFormulaMate (derivedPullback Λ f) (derivedPushforward Λ f)
    (derivedAdjunction Λ f) (tensor Λ Y) (tensor Λ X) (tensorPullComparison Λ f) K L

/-- Equality of the specified derived Hom bijections; thus both units and counits agree.
Source: Stacks 07A6 and Derived Categories 09T5
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derive the two equal ordinary Hom bijections on K-flat and K-injective
resolutions. The comparisons in derivedPullComparison and derivedPushComparison
are the canonical resolution comparisons, so uniqueness of derived adjunctions
gives this equality on all objects. Applying it to identities gives the unit
and counit statements. -/
theorem derived_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (internalModules Λ Y)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedPullback Λ f).obj M ⟶ N) :
    (derivedAdjunction Λ f).homEquiv _ _
        ((derivedPullComparison Λ f).inv.app M ≫ (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ Y).functor.map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ q) ≫
          (derivedPushComparison Λ f).hom.app N := by
  sorry

/-- Equality of the actual oplax tensor natural transformations under comparison.
Inverting this equation identifies the actual lax maps as well.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the normalized underived maps both send s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). Apply this equality to flat-term K-flat
representatives and totalize with the same signs. The representative square in
tensorPullComparison_existsUnique and uniqueness of two-variable derived tensor
in lem-weil-pbc-site-derived-tensor-descent give the equation on every pair. -/
theorem delta_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) := by
  sorry

/-- The actual lax tensor map is the inverse of the localized strong oplax map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalMu {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedPullback Λ f).obj M)).obj
        ((internalDerivedPullback Λ f).obj N) ⟶
      (internalDerivedPullback Λ f).obj (((CondensedRing.derivedTensor Λ Y).obj M).obj N) :=
  inv (((internalDelta Λ f).app M).app N)

/-- Equality for the actual lax map mu and the inverse canonical ringed tensor map.
Source: Stacks 07A4 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: invert the square in delta_comparison. Both transformations are strong,
so their lax maps are precisely the inverses of their specified oplax maps.
The inverse of the tensor of comparison isomorphisms is the tensor of their
inverses; functors preserve inverses. This gives the displayed equation. -/
theorem mu_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).inv.app M)
        ((derivedPullComparison Λ f).inv.app N)) ≫
        (tensorComparison Λ X).inv.app
          ((internalDerivedPullback Λ f).obj M,
            (internalDerivedPullback Λ f).obj N) ≫
        (derivedEquivalence Λ X).functor.map (internalMu Λ f M N) =
      (tensorPullComparison Λ f).inv.app
          ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app (M, N)) ≫
        (derivedPullComparison Λ f).inv.app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) := by
  have h :
      (derivedEquivalence Λ X).functor.mapIso (asIso (((internalDelta Λ f).app M).app N)) ≪≫
          (tensorComparison Λ X).app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≪≫
          (tensor Λ X).mapIso (Iso.prod ((derivedPullComparison Λ f).app M)
            ((derivedPullComparison Λ f).app N)) =
        (derivedPullComparison Λ f).app (((CondensedRing.derivedTensor Λ Y).obj M).obj N) ≪≫
          (derivedPullback Λ f).mapIso ((tensorComparison Λ Y).app (M, N)) ≪≫
          (tensorPullComparison Λ f).app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) :=
    Iso.ext (delta_comparison Λ f M N)
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv,
    asIso_inv, internalMu, Category.assoc] using congrArg Iso.inv h

set_option maxHeartbeats 1600000 in
-- The comparison instances contain large sheaf tensor constraints.
/-- The module-object proper projection is the precise ringed projection mate alpha.
This statement makes no invertibility assertion about the projection arrow.
Source: Stacks 0B56 (blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: derived_homEquiv identifies the specified Hom bijection and counit, and
delta_comparison identifies its tensor arrow. Their composite therefore has the
same adjoint transpose, which is exactly derivedProjectionFormulaMate used in
ringedProjectionMateExact. Naturality and unit normalization follow from the same
identifications and the adjunction triangle identities. -/
theorem projection_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (internalModules Λ X)) (L : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
          (K, (internalDerivedPullback Λ f).obj L)) ≫
        (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ X).functor.obj K))
          ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app
          ((internalDerivedPushforward Λ f).obj K, L) ≫
        (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K)
          (𝟙 ((derivedEquivalence Λ Y).functor.obj L))) ≫
        projection Λ f ((derivedEquivalence Λ X).functor.obj K)
          ((derivedEquivalence Λ Y).functor.obj L) := by
  let d := Functor.curry.map (tensorPullComparison Λ f).hom ≫
    (Functor.curryObjProdComp (derivedPullback Λ f) (derivedPullback Λ f)
      (tensor Λ X)).hom
  let tX := ((Functor.postcompose₂.obj (derivedEquivalence Λ X).functor).map
      (Functor.currying.unitIso.hom.app (CondensedRing.derivedTensor Λ X))) ≫
    Functor.curry.map (tensorComparison Λ X).hom ≫
    (Functor.curryObjProdComp (derivedEquivalence Λ X).functor
      (derivedEquivalence Λ X).functor (tensor Λ X)).hom
  let tY := ((Functor.postcompose₂.obj (derivedEquivalence Λ Y).functor).map
      (Functor.currying.unitIso.hom.app (CondensedRing.derivedTensor Λ Y))) ≫
    Functor.curry.map (tensorComparison Λ Y).hom ≫
    (Functor.curryObjProdComp (derivedEquivalence Λ Y).functor
      (derivedEquivalence Λ Y).functor (tensor Λ Y)).hom
  have hX (M N : DerivedCategory (internalModules Λ X)) :
      (tX.app M).app N = (tensorComparison Λ X).hom.app (M, N) := by
    change (derivedEquivalence Λ X).functor.map (𝟙 _) ≫
      (tensorComparison Λ X).hom.app (M, N) ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hY (M N : DerivedCategory (internalModules Λ Y)) :
      (tY.app M).app N = (tensorComparison Λ Y).hom.app (M, N) := by
    change (derivedEquivalence Λ Y).functor.map (𝟙 _) ≫
      (tensorComparison Λ Y).hom.app (M, N) ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hd (M N : DerivedCategory (modules Λ Y)) :
      (d.app M).app N = (tensorPullComparison Λ f).hom.app (M, N) := by
    exact Category.comp_id _
  have hs : ∀ M N,
      (derivedPullback Λ f).map ((tY.app M).app N) ≫
        (d.app ((derivedEquivalence Λ Y).functor.obj M)).app
          ((derivedEquivalence Λ Y).functor.obj N) ≫
        ((Functor.curry.obj (tensor Λ X)).map
          ((derivedPullComparison Λ f).inv.app M)).app _ ≫
        ((Functor.curry.obj (tensor Λ X)).obj _).map
          ((derivedPullComparison Λ f).inv.app N) =
      (derivedPullComparison Λ f).inv.app _ ≫
        (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        (tX.app _).app _ := by
    intro M N
    rw [hX, hY, hd]
    change (derivedPullback Λ f).map
        ((tensorComparison Λ Y).hom.app (M, N)) ≫
      ((tensorPullComparison Λ f).hom.app
        ((derivedEquivalence Λ Y).functor.obj M,
          (derivedEquivalence Λ Y).functor.obj N)) ≫
      (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).inv.app M) (𝟙 _)) ≫
      (tensor Λ X).map (Prod.mkHom (𝟙 _) ((derivedPullComparison Λ f).inv.app N)) =
      (derivedPullComparison Λ f).inv.app _ ≫
        (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
        ((tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N))
    rw [← (tensor Λ X).map_comp]
    simp only [prod_comp, Category.comp_id, Category.id_comp]
    rw [← cancel_epi ((derivedPullComparison Λ f).hom.app
      (((CondensedRing.derivedTensor Λ Y).obj M).obj N))]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% (delta_comparison Λ f M N)]
    simp only [← (tensor Λ X).map_comp, prod_comp, Iso.hom_inv_id_app, ← prod_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hc : ∀ A,
      (derivedPullback Λ f).map ((derivedPushComparison Λ f).hom.app A) ≫
        (derivedAdjunction Λ f).counit.app ((derivedEquivalence Λ X).functor.obj A) =
      (derivedPullComparison Λ f).inv.app _ ≫
        (derivedEquivalence Λ X).functor.map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app A) := by
    intro A
    have h := derived_homEquiv Λ f _ A
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app A)
    rw [← (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv_symm_id A,
      Equiv.apply_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp] at h
    have hh := congrArg ((derivedAdjunction Λ f).homEquiv _ _).symm h
    rw [Equiv.symm_apply_apply] at hh
    simpa only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id,
      Category.id_comp] using hh.symm
  have h := Adjunction.rightAdjointProjectionMap_mate
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f) (derivedAdjunction Λ f)
    (T₂ := Functor.curry.obj (tensor Λ X)) (S₂ := Functor.curry.obj (tensor Λ Y))
    (U := (derivedEquivalence Λ Y).functor) (V := (derivedEquivalence Λ X).functor)
    (internalDelta Λ f) d tY tX (derivedPullComparison Λ f).inv
    (derivedPushComparison Λ f).hom hs hc K L
  have hh := congrArg (fun q ↦ q ≫ (derivedPushforward Λ f).map
    ((tensor Λ X).map (Prod.mkHom (𝟙 ((derivedEquivalence Λ X).functor.obj K))
      ((derivedPullComparison Λ f).hom.app L)))) h
  rw [hX, hY] at hh
  change ((derivedEquivalence Λ Y).functor.map (internalProjection Λ f K L) ≫
      (derivedPushComparison Λ f).hom.app _ ≫
      (derivedPushforward Λ f).map ((tensorComparison Λ X).hom.app
        (K, (internalDerivedPullback Λ f).obj L))) ≫
      (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom (𝟙 _)
        ((derivedPullComparison Λ f).hom.app L))) =
    ((tensorComparison Λ Y).hom.app ((internalDerivedPushforward Λ f).obj K, L) ≫
      (tensor Λ Y).map (Prod.mkHom ((derivedPushComparison Λ f).hom.app K) (𝟙 _)) ≫
      projection Λ f ((derivedEquivalence Λ X).functor.obj K)
        ((derivedEquivalence Λ Y).functor.obj L) ≫
      (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom (𝟙 _)
        ((derivedPullComparison Λ f).inv.app L)))) ≫
      (derivedPushforward Λ f).map ((tensor Λ X).map (Prod.mkHom (𝟙 _)
        ((derivedPullComparison Λ f).hom.app L))) at hh
  simp only [Category.assoc, ← (derivedPushforward Λ f).map_comp,
    ← (tensor Λ X).map_comp, prod_comp, Category.id_comp, Iso.inv_hom_id_app,
    ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at hh
  simpa only [(derivedPushforward Λ f).map_comp] using hh


set_option maxHeartbeats 800000 in
-- Comparing the two localized mate squares elaborates the section-module constraints.
/-- Equality of the specified open Hom bijections, hence of their units and counits.
Source: Stacks 03DI and 03DJ
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the comparison inserts the section equivalence unit into the same linearized
extension-by-zero functor. The sheaf open adjunction is unchanged on underlying maps.
The ordinary adjunction triangles give the Hom equality, and applying localization
preserves that equality since both functors are exact. Evaluate at identities for
units and counits. -/
theorem open_homEquiv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (internalModules Λ U)) (N : DerivedCategory (internalModules Λ X))
    (q : (internalDerivedExtension Λ j).obj M ⟶ N) :
    (derivedOpenAdjunction Λ j).homEquiv _ _
        ((derivedExtensionComparison Λ j).inv.app M ≫
          (derivedEquivalence Λ X).functor.map q) =
      (derivedEquivalence Λ U).functor.map ((internalOpenAdjunction Λ j).homEquiv _ _ q) ≫
        (derivedPullComparison Λ j).hom.app N := by
  have hunit := Adjunction.mapDerivedCategoryAdjunction_mate
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (openAdjunction Λ j) (pullComparison Λ j) (extensionComparison Λ j).symm
    (fun A ↦ by
      have h := (InternalModuleOperations.internal_module_operations_transport Λ).2.2.1 j
      rw [← h.2.1 A]
      simp only [extensionComparison, ordinaryExtensionComparison, Iso.symm_hom,
        Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]) M
  let i := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j
  let e := Functor.mapDerivedCategorySquareIso (pullComparison Λ j)
  let a :=
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryAdjunction
  rw [internalOpenAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  change (derivedOpenAdjunction Λ j).homEquiv _ _
      ((derivedExtensionComparison Λ j).inv.app M ≫
        (derivedEquivalence Λ X).functor.map q) =
    (derivedFunctor Λ U).map ((a.homEquiv _ _ q) ≫ i.inv.app N) ≫
      ((derivedFunctor Λ U).map (i.hom.app N) ≫ e.hom.app N)
  rw [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  have he : (derivedExtensionComparison Λ j).inv.app M =
      (Functor.mapDerivedCategorySquareIso (extensionComparison Λ j).symm).hom.app M := by
    simp only [derivedExtensionComparison, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  erw [he, hunit, Category.assoc]
  erw [← e.hom.naturality q]
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- The actual internal adjoint-of-unit open projection arrow, using inverse delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def internalOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (internalDerivedExtension Λ j).obj
        (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ⟶
      ((CondensedRing.derivedTensor Λ X).obj ((internalDerivedExtension Λ j).obj K)).obj L :=
  ((internalOpenAdjunction Λ j).homEquiv _ _).symm
    ((((CondensedRing.derivedTensor Λ U).map
        ((internalOpenAdjunction Λ j).unit.app K)).app ((internalDerivedPullback Λ j).obj L)) ≫
      inv (((internalDelta Λ j).app
        ((internalDerivedExtension Λ j).obj K)).app L))

/-- The ringed adjoint-of-unit open projection arrow, using inverse canonical delta.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison). -/
def openProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (modules Λ U)) (L : DerivedCategory (modules Λ X)) :
    (derivedExtension Λ j).obj ((tensor Λ U).obj (K, (derivedPullback Λ j).obj L)) ⟶
      (tensor Λ X).obj ((derivedExtension Λ j).obj K, L) :=
  ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
    ((tensor Λ U).map (Prod.mkHom ((derivedOpenAdjunction Λ j).unit.app K)
        (𝟙 ((derivedPullback Λ j).obj L))) ≫
      (tensorPullComparison Λ j).inv.app ((derivedExtension Λ j).obj K, L))

set_option maxHeartbeats 1600000 in
-- The curried tensor and derived adjunction interfaces have large instance arguments.
/-- Equality of the actual adjoint-of-unit open projection morphisms.
Source: Stacks 03DJ and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: open_homEquiv identifies the specified unit, and delta_comparison identifies
its inverse, the actual lax map mu. Naturality of the tensor and extension
comparisons identifies their composite. Taking the specified open adjoint transpose
gives precisely the displayed equality, without choosing another projection map. -/
theorem openProjection_comparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (internalModules Λ U)) (L : DerivedCategory (internalModules Λ X)) :
    (derivedEquivalence Λ X).functor.map (internalOpenProjection Λ j K L) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedExtension Λ j).obj K, L) ≫
        (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app K)
          (𝟙 ((derivedEquivalence Λ X).functor.obj L))) =
      (derivedExtensionComparison Λ j).hom.app
          (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensorComparison Λ U).hom.app
          (K, (internalDerivedPullback Λ j).obj L)) ≫
        (derivedExtension Λ j).map ((tensor Λ U).map (Prod.mkHom
          (𝟙 ((derivedEquivalence Λ U).functor.obj K))
          ((derivedPullComparison Λ j).hom.app L))) ≫
        openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
          ((derivedEquivalence Λ X).functor.obj L) := by
  let : ∀ M, IsIso ((internalDelta Λ j).app M) :=
    fun M ↦ NatIso.isIso_of_isIso_app _
  let : IsIso (internalDelta Λ j) := NatIso.isIso_of_isIso_app _
  let d₁ :
      (((Functor.whiskeringLeft₂ _).obj (internalDerivedPullback Λ j)).obj
        (internalDerivedPullback Λ j)).obj (CondensedRing.derivedTensor Λ U) ⟶
      (Functor.postcompose₂.obj (internalDerivedPullback Λ j)).obj
        (CondensedRing.derivedTensor Λ X) := inv (internalDelta Λ j)
  let d₂ := (Functor.curryObjProdComp (derivedPullback Λ j)
      (derivedPullback Λ j) (tensor Λ U)).inv ≫
    Functor.curry.map (tensorPullComparison Λ j).inv
  let tU := (Functor.postcompose₂.obj (derivedEquivalence Λ U).functor).map
      (Functor.currying.unitIso.hom.app (CondensedRing.derivedTensor Λ U)) ≫
    Functor.curry.map (tensorComparison Λ U).hom ≫
    (Functor.curryObjProdComp (derivedEquivalence Λ U).functor
      (derivedEquivalence Λ U).functor (tensor Λ U)).hom
  let tX := (Functor.postcompose₂.obj (derivedEquivalence Λ X).functor).map
      (Functor.currying.unitIso.hom.app (CondensedRing.derivedTensor Λ X)) ≫
    Functor.curry.map (tensorComparison Λ X).hom ≫
    (Functor.curryObjProdComp (derivedEquivalence Λ X).functor
      (derivedEquivalence Λ X).functor (tensor Λ X)).hom
  have hU (M N : DerivedCategory (internalModules Λ U)) :
      (tU.app M).app N = (tensorComparison Λ U).hom.app (M, N) := by
    change (derivedEquivalence Λ U).functor.map (𝟙 _) ≫
      (tensorComparison Λ U).hom.app (M, N) ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hX (M N : DerivedCategory (internalModules Λ X)) :
      (tX.app M).app N = (tensorComparison Λ X).hom.app (M, N) := by
    change (derivedEquivalence Λ X).functor.map (𝟙 _) ≫
      (tensorComparison Λ X).hom.app (M, N) ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hb : ∀ A,
      (derivedOpenAdjunction Λ j).unit.app ((derivedEquivalence Λ U).functor.obj A) ≫
        (derivedPullback Λ j).map ((derivedExtensionComparison Λ j).inv.app A) =
      (derivedEquivalence Λ U).functor.map ((internalOpenAdjunction Λ j).unit.app A) ≫
        (derivedPullComparison Λ j).hom.app ((internalDerivedExtension Λ j).obj A) := by
    intro A
    have h := open_homEquiv Λ j A _ (𝟙 ((internalDerivedExtension Λ j).obj A))
    simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_unit] at h
    erw [Category.comp_id, Category.comp_id] at h
    exact h
  have ht : ∀ M N,
      (derivedEquivalence Λ U).functor.map ((d₁.app M).app N) ≫
        (derivedPullComparison Λ j).hom.app
          (((CondensedRing.derivedTensor Λ X).obj M).obj N) ≫
        (derivedPullback Λ j).map ((tX.app M).app N) =
      (tU.app ((internalDerivedPullback Λ j).obj M)).app
          ((internalDerivedPullback Λ j).obj N) ≫
        ((Functor.curry.obj (tensor Λ U)).map ((derivedPullComparison Λ j).hom.app M)).app _ ≫
        ((Functor.curry.obj (tensor Λ U)).obj _).map
          ((derivedPullComparison Λ j).hom.app N) ≫
        (d₂.app ((derivedEquivalence Λ X).functor.obj M)).app
          ((derivedEquivalence Λ X).functor.obj N) := by
    intro M N
    rw [hU, hX]
    dsimp only [d₁]
    rw [NatIso.isIso_inv_app, NatIso.isIso_inv_app]
    change (derivedEquivalence Λ U).functor.map (internalMu Λ j M N) ≫
        (derivedPullComparison Λ j).hom.app _ ≫
        (derivedPullback Λ j).map ((tensorComparison Λ X).hom.app (M, N)) =
      (tensorComparison Λ U).hom.app
          ((internalDerivedPullback Λ j).obj M, (internalDerivedPullback Λ j).obj N) ≫
        (tensor Λ U).map (Prod.mkHom ((derivedPullComparison Λ j).hom.app M) (𝟙 _)) ≫
        (tensor Λ U).map (Prod.mkHom (𝟙 _) ((derivedPullComparison Λ j).hom.app N)) ≫
        (𝟙 _ ≫ (tensorPullComparison Λ j).inv.app
          ((derivedEquivalence Λ X).functor.obj M, (derivedEquivalence Λ X).functor.obj N))
    rw [Category.id_comp, ← (tensor Λ U).map_comp_assoc]
    simp only [prod_comp, Category.comp_id, Category.id_comp]
    rw [← cancel_epi ((tensorComparison Λ U).inv.app
      ((internalDerivedPullback Λ j).obj M, (internalDerivedPullback Λ j).obj N))]
    simp only [Iso.inv_hom_id_app_assoc]
    let ei := (tensor Λ U).mapIso (Iso.prod ((derivedPullComparison Λ j).app M).symm
      ((derivedPullComparison Λ j).app N).symm)
    have : IsIso ((tensor Λ U).map (Prod.mkHom
        ((derivedPullComparison Λ j).inv.app M) ((derivedPullComparison Λ j).inv.app N))) := by
      change IsIso ei.hom
      infer_instance
    rw [← cancel_epi ((tensor Λ U).map (Prod.mkHom
      ((derivedPullComparison Λ j).inv.app M) ((derivedPullComparison Λ j).inv.app N)))]
    rw [reassoc_of% (mu_comparison Λ j M N)]
    have hei : (tensor Λ U).map (Prod.mkHom
          ((derivedPullComparison Λ j).inv.app M) ((derivedPullComparison Λ j).inv.app N)) ≫
        (tensor Λ U).map (Prod.mkHom
          ((derivedPullComparison Λ j).hom.app M) ((derivedPullComparison Λ j).hom.app N)) =
        𝟙 _ := ei.hom_inv_id
    simp only [Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hei, ← (derivedPullback Λ j).map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h := Adjunction.projectionMap_mate
    (internalOpenAdjunction Λ j) (derivedOpenAdjunction Λ j)
    (internalDerivedPullback Λ j) (derivedPullback Λ j)
    (T₂ := Functor.curry.obj (tensor Λ U)) (T'₂ := Functor.curry.obj (tensor Λ X))
    (U := (derivedEquivalence Λ U).functor) (V := (derivedEquivalence Λ X).functor)
    d₁ d₂ tU tX (derivedPullComparison Λ j).hom (derivedPullComparison Λ j).hom
    (derivedExtensionComparison Λ j).inv hb ht K L
  have hi : (((internalOpenAdjunction Λ j).projectionMap
        (internalDerivedPullback Λ j) (CondensedRing.derivedTensor Λ U)
        (CondensedRing.derivedTensor Λ X) d₁).app K).app L =
      internalOpenProjection Λ j K L := by
    rw [Adjunction.projectionMap_app_app, Adjunction.projectionMapTranspose_app_app]
    simp only [d₁, NatIso.isIso_inv_app]
    rfl
  have ho : (((derivedOpenAdjunction Λ j).projectionMap (derivedPullback Λ j)
        (Functor.curry.obj (tensor Λ U)) (Functor.curry.obj (tensor Λ X)) d₂).app
        ((derivedEquivalence Λ U).functor.obj K)).app
        ((derivedEquivalence Λ X).functor.obj L) =
      openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
        ((derivedEquivalence Λ X).functor.obj L) := by
    rw [Adjunction.projectionMap_app_app, Adjunction.projectionMapTranspose_app_app]
    change ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
      (_ ≫ (𝟙 _ ≫ _)) = _
    rw [Category.id_comp]
    rfl
  rw [hi, ho, hU, hX] at h
  change (derivedExtensionComparison Λ j).inv.app _ ≫
      (derivedEquivalence Λ X).functor.map (internalOpenProjection Λ j K L) ≫
      (tensorComparison Λ X).hom.app ((internalDerivedExtension Λ j).obj K, L) =
    (derivedExtension Λ j).map
        ((tensorComparison Λ U).hom.app (K, (internalDerivedPullback Λ j).obj L)) ≫
      (derivedExtension Λ j).map ((tensor Λ U).map (Prod.mkHom (𝟙 _)
        ((derivedPullComparison Λ j).hom.app L))) ≫
      openProjection Λ j ((derivedEquivalence Λ U).functor.obj K)
        ((derivedEquivalence Λ X).functor.obj L) ≫
      (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).inv.app K) (𝟙 _)) at h
  have hh := congrArg (fun q ↦ q ≫
    (tensor Λ X).map (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app K)
      (𝟙 ((derivedEquivalence Λ X).functor.obj L)))) h
  simp only [Category.assoc, ← (tensor Λ X).map_comp, prod_comp,
    Iso.inv_hom_id_app, Category.id_comp, ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  rw [← cancel_epi ((derivedExtensionComparison Λ j).inv.app
    (((CondensedRing.derivedTensor Λ U).obj K).obj ((internalDerivedPullback Λ j).obj L)))]
  simp only [Iso.inv_hom_id_app_assoc]
  exact hh

/-- Pullback composition is identified with the canonical ringed pasting comparison.
Source: Stacks 03D7 and 07A6
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: the internal composition comparison is the localization of inverse-image
pasting followed by the compatible coefficient isomorphisms alpha. Under E this is
the same scalar-extension pasting map for ringed modules. Its Hom adjunction
characterization and K-flat normalization determine it uniquely. Essential
surjectivity of D(E_Z) extends the equation to all ringed derived objects. -/
theorem composition_comparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ M : DerivedCategory (internalModules Λ Z),
        (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
            (derivedPullbackComposition Λ f g).hom.app ((derivedEquivalence Λ Z).functor.obj M) =
          (derivedEquivalence Λ X).functor.map
              ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
            (derivedPullComparison Λ f).hom.app
              ((internalDerivedPullback Λ g).obj M) ≫
            (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M) := by
  sorry

/-- The specified derived tensor transformation comparison in the paper's field setting.
Together with ordinary_exact_flat_kflat, ordinary_monoidal, tensor_representatives,
derived_homEquiv, composition_comparison, projection_comparison, open_homEquiv and
openProjection_comparison, this states every clause of the comparison lemma.
Source: Stacks 00YV, 03EK, 03D7, 03DJ, 07A4, 07A6 and 0B56
(blueprint: lem-pd-module-ringed-topos-derived-comparison).
Proof: construct the sectionwise equivalence and its normalized ordinary tensor
maps, and identify signed total complexes and the two K-flat tests. Localize on
K-flat and K-injective representatives, identifying the specified adjunction Hom
bijections and composition pasting. The ordinary pure-tensor formula identifies
actual delta, and its inverse identifies actual mu. Transpose counit after delta
for the proper projection map. For an open immersion, localize the exact extension
by zero and transpose unit followed by mu. These are precisely the equalities
stated in the named clauses above; see their proof plans for the individual steps. -/
theorem module_ringed_topos_derived_comparison
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y.left)) :
    (derivedEquivalence Λ X.left).functor.map (((internalDelta Λ f.left).app M).app N) ≫
        (tensorComparison Λ X.left).hom.app
          ((internalDerivedPullback Λ f.left).obj M,
            (internalDerivedPullback Λ f.left).obj N) ≫
        (tensor Λ X.left).map (Prod.mkHom
          ((derivedPullComparison Λ f.left).hom.app M)
          ((derivedPullComparison Λ f.left).hom.app N)) =
      (derivedPullComparison Λ f.left).hom.app
          (((CondensedRing.derivedTensor Λ Y.left).obj M).obj N) ≫
        (derivedPullback Λ f.left).map ((tensorComparison Λ Y.left).hom.app (M, N)) ≫
        (tensorPullComparison Λ f.left).hom.app
          ((derivedEquivalence Λ Y.left).functor.obj M,
            (derivedEquivalence Λ Y.left).functor.obj N) := by
  exact delta_comparison Λ f.left M N

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
