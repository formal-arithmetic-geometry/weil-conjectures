/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars

/-!
# Ordinary derived realization of condensed scalar extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-finite-extension.md, ordinary scalar functor, and the first paragraph
of its proof (blueprint: lem-pur-legacy-ordinary-scalar-realization).

All coefficients below are pulled-back condensed rings and all derived categories are
ordinary unbounded derived categories of internal module objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section ScalarMap

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- The left-derived resolution transformation on an arbitrary complex, transported from
`Qh` to `Q` using the canonical quotient factorizations. No resolution is chosen here.
Source: the ordinary termwise scalar realization in the first proof paragraph of
`lem-coef-integral-finite-extension`
(blueprint: lem-pur-legacy-ordinary-scalar-realization). -/
noncomputable def ordinaryScalarResolutionMap
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ℤ) :
    (Mod.extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((Mod.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  let B := Mod.extendScalars φ
  B.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    B.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map ((B.mapHomotopyCategoryFactors _).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)).hom.app
        ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- The representative normalization `epsilon_P theta_QP = phi_P`, with categorical
composition read from left to right. Source: first proof paragraph of
`lem-coef-integral-finite-extension`
(blueprint: lem-pur-legacy-ordinary-scalar-realization). -/
def ordinaryScalarNormalized [PreservesFiniteLimits (Mod.extendScalars φ)]
    (θ : (Mod.extendScalars φ).mapDerivedCategory ≅
      (Mod.extendScalars φ).leftDerivedFunctor) : Prop :=
  ∀ P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ℤ,
    θ.hom.app (DerivedCategory.Q.obj P) ≫ ordinaryScalarResolutionMap φ P =
      (Mod.extendScalars φ).mapDerivedCategoryFactors.hom.app P

/-- The conclusions for either of the two coefficient pairs. This predicate bundles the
node's clauses, without supplying data or adding exactness as a hypothesis.
Source: ordinary scalar functor and first proof paragraph of
`lem-coef-integral-finite-extension`
(blueprint: lem-pur-legacy-ordinary-scalar-realization). -/
def HasOrdinaryCondensedScalarRealization : Prop :=
  ∃ h : PreservesFiniteLimits (Mod.extendScalars φ),
    letI := h
    let B := Mod.extendScalars φ
    B.Additive ∧ PreservesFiniteColimits B ∧ B.mapDerivedCategory.IsTriangulated ∧
    ∃ θ : B.mapDerivedCategory ≅ B.leftDerivedFunctor,
      ordinaryScalarNormalized φ θ ∧
      (∀ θ' : B.mapDerivedCategory ≅ B.leftDerivedFunctor,
        ordinaryScalarNormalized φ θ' → θ' = θ) ∧
      θ = B.leftDerivedFunctorIsoMapDerivedCategory.symm ∧
      (∀ j : ℤ, Nonempty
        (B.leftDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ j ≅
          DerivedCategory.homologyFunctor _ j ⋙ B)) ∧
      (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
          (I : Set ℤ), Set.OrdConnected I →
        (∀ j : ℤ, j ∉ I →
          IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) →
        ∀ j : ℤ, j ∉ I →
          IsZero ((DerivedCategory.homologyFunctor _ j).obj (B.leftDerivedFunctor.obj K))) ∧
      ∃ (hD : ∀ K, boundedConstructible R K →
          boundedConstructible S (B.mapDerivedCategory.obj K))
        (hT : ∀ K, boundedConstructible R K →
          boundedConstructible S (B.leftDerivedFunctor.obj K)),
        let Dc := (boundedConstructible S).lift
          ((boundedConstructible R).ι ⋙ B.mapDerivedCategory)
          (fun K ↦ hD K.obj K.property)
        let Tc := (boundedConstructible S).lift
          ((boundedConstructible R).ι ⋙ B.leftDerivedFunctor)
          (fun K ↦ hT K.obj K.property)
        ∃ θc : Dc ≅ Tc, ∀ K : BoundedConstructible R,
          (boundedConstructible S).ι.map (θc.hom.app K) = θ.hom.app K.obj ∧
          (boundedConstructible S).ι.map (θc.inv.app K) = θ.inv.app K.obj

end ScalarMap

/-- Identity normalization: under the tensor-unit identifications, the normalized
comparison becomes the identity. The right hand side is the termwise tensor-unit
comparison; the left hand side first uses `theta` and then the left-derived tensor unit.
Source: identity-extension compatibility of `lem-coef-integral-finite-extension`
(blueprint: lem-pur-legacy-ordinary-scalar-realization). -/
def OrdinaryCondensedScalarUnitNormalization {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∃ h : PreservesFiniteLimits (Mod.extendScalars (𝟙 R)),
    letI := h
    let B := Mod.extendScalars (𝟙 R)
    ∀ θ : B.mapDerivedCategory ≅ B.leftDerivedFunctor,
      ordinaryScalarNormalized (𝟙 R) θ →
      θ ≪≫ B.leftDerivedFunctorNatIso (Mod.extendScalarsId (R := R)) ≪≫
          Functor.leftDerivedFunctorIsoMapDerivedCategory
            (𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) ≪≫
          Functor.mapDerivedCategoryIdIso _ =
        Functor.mapDerivedCategoryNatIso (Mod.extendScalarsId (R := R)) ≪≫
          Functor.mapDerivedCategoryIdIso _

/-- Ordinary derived realization for integral and rational condensed coefficients,
including the canonical tensor-unit normalization for the identity extension.

Source: `lem-coef-integral-finite-extension.md`, ordinary scalar functor, and the first
paragraph of its proof (blueprint: lem-pur-legacy-ordinary-scalar-realization).

Proof:
1. The cartesian finite-free coefficient theorem gives finite-limit preservation for
   both scalar functors. They are additive and are left adjoints, hence preserve finite
   colimits. Exact-functor localization gives their triangulated termwise descents.
2. A K-flat resolution computes the left derived scalar functor. Exactness makes the
   image of its resolving quasi-isomorphism invertible, so epsilon is invertible on
   every complex. The maps epsilon^{-1} phi descend through Q to theta. Localization
   gives uniqueness. This is the canonical exact/left-derived comparison.
3. Exact-functor cohomology comparison gives the natural isomorphisms in every integer
   degree. Additivity preserves zero objects, hence preserves the same support interval.
   Exact scalar extension preserves finite stratifications with locally finitely
   presented cohomology, so both realizations preserve bounded constructibility.
4. Fullness restricts theta and its inverse to these full subcategories, with precisely
   the stated component equations. For the identity extension the ordinary tensor unit
   sends a tensor m to am. Applying it termwise and left deriving it gives the displayed
   unit comparison equation, by the same representative normalization and uniqueness.
-/
theorem ordinaryCondensedScalarRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    HasOrdinaryCondensedScalarRealization
        (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) X) ∧
      HasOrdinaryCondensedScalarRealization (padicSubfieldRingObjMap X ℓ h) ∧
      OrdinaryCondensedScalarUnitNormalization
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) ∧
      OrdinaryCondensedScalarUnitNormalization (padicSubfieldRingObj X ℓ E) ∧
      coefficientMap (finiteCoefficientIntegersPointMap ℓ (le_refl E)) X = 𝟙 _ ∧
      padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.ProEtale
