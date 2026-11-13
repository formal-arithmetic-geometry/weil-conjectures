/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
import WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts

/-!
# Algebraic-closure coefficient change and bounded-below direct image

The comparison is the existing coefficient-change mate `derivedPushHom` in the
ordinary ambient derived category of internal module objects. Its algebraic-closure
coefficient ring uses continuous functions with values in one finite subextension.

## References

* Hemo--Richarz--Scholbach, Lemmas 5.3(1) and 5.6
* Hemo--Richarz--Scholbach, Lemmas 5.3(1), 5.6
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

private theorem restrictionReflectsIsomorphisms
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    (comap (D := C) φ).ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro M N f hf
  have : IsIso f.hom := by
    change IsIso ((forget R).map ((comap φ).map f))
    infer_instance
  have : IsIso ((forget S).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (forget S)

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

private theorem isIso_mate_pushHomOfComapIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} (κ : G' ⋙ U' ≅ U ⋙ G) :
    IsIso (mateEquiv adj adj' (pushHomOfComapIso adj adj' κ)) := by
  change IsIso ((mateEquiv adj adj') ((mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ κ.inv)))
  rw [Equiv.apply_symm_apply]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local irreducible] derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction upperStarFromPoint ProEtale.upperStar

private theorem reflectsDerivedIsomorphisms
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem centralUnitCopowerExplicit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {U : B ⥤ A} (adj : L ⊣ U)
    {L' : A' ⥤ B'} {U' : B' ⥤ A'} (adj' : L' ⊣ U')
    {G : A ⥤ A'} {G' : B ⥤ B'} [U'.ReflectsIsomorphisms]
    (β : G ⋙ L' ⟶ L ⋙ G') (hκ : IsIso (mateEquiv adj adj' β))
    (M : A) (I : Type*) [HasCoproduct (fun _ : I ↦ M)]
    [HasCoproduct (fun _ : I ↦ G.obj M)]
    (τ : I → CatCenter B) (τ' : I → CatCenter B')
    (hs : ∀ i K, G'.map ((τ i).app K) = (τ' i).app (G'.obj K))
    (hC : IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
      adj.unit.app M ≫ U.map ((τ i).app (L.obj M))))
    (hD : IsIso (Sigma.desc (f := fun _ : I ↦ G.obj M) fun i ↦
      adj'.unit.app (G.obj M) ≫
        U'.map ((τ' i).app (L'.obj (G.obj M)))))
    (hc : IsIso (Sigma.desc fun i : I ↦ G.map (Sigma.ι (fun _ : I ↦ M) i))) :
    IsIso (β.app M) := by
  have := hC
  have := hD
  apply (Adjunction.isIso_iff_unitCoproductComparison adj adj' β hκ M I
    (fun i ↦ (τ i).app _) (fun i ↦ (τ' i).app _) (fun i ↦ ?_)).2 hc
  exact ((τ' i).naturality (β.app M)).symm.trans
    (congrArg (fun g ↦ β.app M ≫ g) (hs i (L.obj M))).symm

private theorem coefficientDerivedCoproducts (Λ : Sheaf
    (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z))) := by
  let C := Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    CategoryTheory.IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} C (Discrete J)
  exact CategoryTheory.derived_hasCoproducts

-- The scalar mate criterion compares derived adjunctions in four module categories.
/-- Algebraic-closure extension commutes with qcqs direct image on every bounded-below
ambient module complex, without constructibility or finite Tor amplitude.

Proof plan:
1. Transport internal modules to section-ring module sheaves using
   lem-pe-internal-section-tensor-comparison and lem-sfb-internal-module-operations-transport.
   Exact equivalences preserve injective resolutions and the null-homotopy test for
   K-injectivity, so this also preserves
   the derived adjunction and its counit.
2. The finite intermediate fields containing E form a nonempty directed tail. Their
   actual inclusion legs exhibit the algebraic-closure coefficient module as a colimit. Cartesian coefficients identify their pullbacks
   and inclusion maps.
   Finite coefficients are finite free; closure coefficients are flat.
3. Represent C by a complex vanishing below one integer a, using
   def-sbc-standard-tstructure-derived-category. Exact scalar extension preserves this
   common bound. Tensor preserves the coefficient colimit termwise. Filtered module colimits are exact, hence commute with cohomology.
4. The symmetric projection mate at a finite coefficient field is the finite-biproduct
   comparison: naturality and the tensor-unit normalization identify it on every summand. It is therefore invertible.
5. Apply det-pe-bounded-continuity-direct-image to the actual finite-field diagram with
   its common bound a. Naturality gives the cocone equation for the projection mates.
   Thus the closure projection mate induces, on every cohomology sheaf, the colimit of
   the finite-field isomorphisms followed by the continuity isomorphism. Cohomology
   detects invertibility.
6. Restrict the specified coefficient-change map to E. The conservative restriction
   and its adjunction-compatible pushforward comparison identify it with the closure projection
   mate: both adjuncts are the canonical pullback/tensor identification followed by
   scalar extension of the E-coefficient counit. The pulled-back inclusion is the
   same by sk-def-sfb-coefficient-change. Restriction reflects isomorphisms, so the
   specified map is invertible. Transport back to internal modules as in step 1.

Here `derivedPushHom` is the mate of `derivedComapLowerStarIso` under derived scalar
extension/restriction. Equivalently, under the derived geometric adjunction its adjunct
is `(derivedPullIso a f).inv.app (Rf_* C)` followed by extension of the geometric counit,
where a is the actual finite-subfield inclusion. This fixes the canonical map itself. -/
theorem isIso_derivedPushHom_padicAlgCl_of_boundedBelow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (C : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app C.obj) := by
  classical
  have hbounded : ∃ N : ℤ, C.obj.IsGE N := C.property
  obtain ⟨N, hN⟩ := hbounded
  have : C.obj.IsGE N := hN
  -- Use the scalar basis to identify this very mate with a bounded copower comparison.
  have hb := condensedQbar_derived_scalar_basis.{u} ℓ E
  unfold CondensedQbarDerivedScalarBasis at hb
  rcases hb with ⟨I, τ, hunit, hscalar⟩
  have : HasCoproduct (fun _ : I ↦ C.obj) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) X I).has_colimit _
  have : HasCoproduct (fun _ : I ↦ R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj C.obj) :=
    (coefficientDerivedCoproducts (Profinite.continuousMapRingObj E) Y I).has_colimit _
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)).ReflectsIsomorphisms :=
    Mod.restrictionReflectsIsomorphisms (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)
  have : (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          Y)).mapDerivedCategory.ReflectsIsomorphisms :=
    reflectsDerivedIsomorphisms _
  have hκ : IsIso
      (mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
          (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)) := by
    unfold derivedPushHom
    exact Adjunction.isIso_mate_pushHomOfComapIso
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
      (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
  refine centralUnitCopowerExplicit
    (G := R((f)_*⟦Profinite.continuousMapRingObj E⟧))
    (G' := R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y))
    (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) hκ C.obj I
    (τ X) (τ Y) ?_ ?_ ?_ ?_
  · exact fun i K ↦ hscalar f i K
  · exact hunit X C.obj
  · exact hunit Y (R((f)_*⟦Profinite.continuousMapRingObj E⟧).obj C.obj)
  · exact condensedSubfield_bounded_copower_comparison.{u} ℓ E f I C.obj N

end AlgebraicGeometry.ProEtale.CondensedRing
