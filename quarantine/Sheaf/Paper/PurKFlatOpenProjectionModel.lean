/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module
public import Sheaf.Paper.PurKFlatOpenModelMaps

import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
/-! # Canonical K-flat open tensor coordinates
Source: Stacks 06YS, 07A4, 0FPI
(blueprint: lem-pur-kflat-open-projection-model). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] HomologicalComplex.monoidalCategoryStruct
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.KFlatOpenProjection
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.leftAdjoint Functor.rightAdjoint Functor.leftDerivedFunctor
  upperStar lowerStar ProEtale.pbcFixedScalarExtension derivedTensor
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {U P : Scheme.{u}}
/-- The coefficient projection, transported to j^*T_P L using the specified
scalar/pullback comparison. It is the scalar mate of the derived counit.
Source: Stacks 0GL6, 0FPI (blueprint: lem-pur-kflat-open-projection-model). -/
def coefficientProjection (φ : A →+* B) (j : U ⟶ P)
    (L : DerivedCategoryModule A P) :
    (scalarExtension φ P).obj (R(lowerStar (ModuleCat.{u + 1} A) j).obj
      (L(upperStar (ModuleCat.{u + 1} A) j).obj L)) ⟶
        R(lowerStar (ModuleCat.{u + 1} B) j).obj
          (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L)) :=
  (scalarMate φ j).app (L(upperStar (ModuleCat.{u + 1} A) j).obj L) ≫
    R(lowerStar (ModuleCat.{u + 1} B) j).map ((scalarPullbackIso φ j).inv.app L)

/-- Exactly the five bounded-below assumptions of the open projection model.
Source: Stacks 0FPI and the bounded-below scalar comparisons of 0D6J
(blueprint: lem-pur-kflat-open-projection-model). -/
def boundedDomain (φ : A →+* B) (j : U ⟶ P)
    (L : DerivedCategoryModule A P) : Prop :=
  (∃ n : ℤ, L.IsGE n) ∧
  (∃ n : ℤ, (R(lowerStar (ModuleCat.{u + 1} A) j).obj
    (L(upperStar (ModuleCat.{u + 1} A) j).obj L)).IsGE n) ∧
  (∃ n : ℤ, ((scalarExtension φ P).obj L).IsGE n) ∧
  (∃ n : ℤ, ((scalarExtension φ P).obj
    (R(lowerStar (ModuleCat.{u + 1} A) j).obj
      (L(upperStar (ModuleCat.{u + 1} A) j).obj L))).IsGE n) ∧
  (∃ n : ℤ, (R(lowerStar (ModuleCat.{u + 1} B) j).obj
    (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L))).IsGE n)

/-- The specified ordinary K-flat tensor map computes the coefficient projection,
with its canonical target identification, its projection-formula identification,
its exact derived transpose, and naturality on the stated bounded-below domain.
The representative isomorphisms are pinned by explicit equality to their canonical
formulas; the unique tau is pinned by its canonical comparison equation; no arbitrary
identification or strict B-action is an input.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 07A4 and 0FPI,
with the tensor/scalar specialization of the DAG proof
(blueprint: lem-pur-kflat-open-projection-model).

Proof:
1. Apply the fixed-K-flat tensor lemma to every X. On a flat-term K-flat
resolution R -> X, both Q tensor R -> Q tensor X and Q tensor R -> B tensor R
are quasi-isomorphisms, by K-flatness of Q and R respectively. Signed symmetry,
augmentation and normalized scalar extension give modelScalarIdentification.
Apply the same construction to C and the canonical comparison to obtain sigma.
2. Resolve X as above. Pullback preserves flat-term K-flat complexes. The
ordinary cochain comparison on (Q,R) is the representative of the derived tensor
comparison. Naturality and cancellation of the localized maps for R -> X give
the same comparison for arbitrary X. The signed symmetry equation fixes its sign.
3. Apply lem-sp-etale-derived-chain-transpose to v and to the identity of C.
Its canonical counit square identifies the localized ordinary counit with the
derived counit, using exactly the assumed invertible comparison maps.
4. In the target replace ell J by ell(Q tensor I) using the inverse of this
very ell a. Pullback of ell a then cancels. What remains is the localized
cochain tensor comparison, tensor of the ordinary counit, and the inverse
comparison. Steps 1--3 give exactly c^der followed by epsilon tensor 1_B.
5. The canonical projection-formula map is the adjunct of this transpose.
The adjunction Hom bijection therefore identifies the normalized ell v with PF.
6. lem-pur-etale-scalar-mate-projection identifies PF with restricted beta.
Exact pullback preserves the required lower bounds; boundedDomain supplies the
other bounds for the canonical direct-image/restriction comparison. This
comparison is invertible, so its equation specifies a unique tau, and the
coefficient equality follows. Naturality follows from the natural tensor,
localization and scalar comparisons and the naturality of adjunction mates.
No argument assumes restriction preserves injectives or coefficient flatness. -/
theorem computes_coefficient_projection
    (φ : A →+* B) (j : U ⟶ P)
    (Q I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (b : Q ⟶ (CochainComplex.singleFunctor _ 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso b] (L : DerivedCategoryModule A P) (eI : _root_.DerivedCategory.Q.obj I ≅ L)
    (a : Q ⊗ I ⟶ J) [QuasiIso a]
    [IsIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I))]
    [IsIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj J))]
    [Finite A] [Finite B] [IsOpenImmersion j]
    (_hflat : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (_hDomain : boundedDomain φ j L) :
    ∃ modelTensorIdentification :
    _root_.DerivedCategory.Q.obj (Q ⊗ I) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) P).obj L).obj (scalarCoefficient φ P),
      modelTensorIdentification =
        KFlatSupportComparison.tensorModel φ Q b hQ I L eI ≪≫
          (scalarTensorIso φ P).app L ∧
    ∃ modelScalarIdentification :
    _root_.DerivedCategory.Q.obj (Q ⊗ I) ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj L),
      modelScalarIdentification =
        KFlatSupportComparison.tensorModel φ Q b hQ I L eI ∧
    ∃ replacementScalarIdentification :
    _root_.DerivedCategory.Q.obj J ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj L),
      replacementScalarIdentification =
        (asIso (_root_.DerivedCategory.Q.map a)).symm ≪≫
          modelScalarIdentification ∧
    ∃ replacementTensorIdentification :
    _root_.DerivedCategory.Q.obj J ≅
      ((derivedTensor (ModuleCat.{u + 1} A) P).obj L).obj (scalarCoefficient φ P),
      replacementTensorIdentification =
        (asIso (_root_.DerivedCategory.Q.map a)).symm ≪≫
          modelTensorIdentification ∧
    ∃ projectionSourceIdentification :
    _root_.DerivedCategory.Q.obj (Q ⊗ openComplex j I) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) P).obj
        (R(lowerStar (ModuleCat.{u + 1} A) j).obj
          (L(upperStar (ModuleCat.{u + 1} A) j).obj L))).obj (scalarCoefficient φ P),
      projectionSourceIdentification =
        KFlatSupportComparison.tensorModel φ Q b hQ (openComplex j I)
          (R(lowerStar (ModuleCat.{u + 1} A) j).obj
            (L(upperStar (ModuleCat.{u + 1} A) j).obj L))
          (directImageIdentification j I L eI) ≪≫
          (scalarTensorIso φ P).app (R(lowerStar (ModuleCat.{u + 1} A) j).obj
            (L(upperStar (ModuleCat.{u + 1} A) j).obj L)) ∧
    ∃ scalarSourceIdentification :
    _root_.DerivedCategory.Q.obj (Q ⊗ openComplex j I) ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj (R(lowerStar (ModuleCat.{u + 1} A) j).obj
          (L(upperStar (ModuleCat.{u + 1} A) j).obj L))),
      scalarSourceIdentification =
        projectionSourceIdentification ≪≫
          (scalarTensorIso φ P).symm.app (R(lowerStar (ModuleCat.{u + 1} A) j).obj
            (L(upperStar (ModuleCat.{u + 1} A) j).obj L)) ∧
    ∃ projectionTargetIdentification :
    _root_.DerivedCategory.Q.obj (openComplex j J) ≅
      R(lowerStar (ModuleCat.{u + 1} A) j).obj
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj
          (L(upperStar (ModuleCat.{u + 1} A) j).obj L)).obj
            (L(upperStar (ModuleCat.{u + 1} A) j).obj (scalarCoefficient φ P))),
      projectionTargetIdentification =
        asIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj J)) ≪≫
          R(lowerStar (ModuleCat.{u + 1} A) j).mapIso
            ((pullbackRepresentativeIso j J).symm ≪≫
              L(upperStar (ModuleCat.{u + 1} A) j).mapIso
                (replacementTensorIdentification) ≪≫
              leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j L (scalarCoefficient φ P)) ∧
    ∃ scalarTargetNormalization :
    _root_.DerivedCategory.Q.obj (openComplex j J) ⟶
      R(lowerStar (ModuleCat.{u + 1} A) j).obj
        ((Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).obj
          (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L))),
      scalarTargetNormalization =
        (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj J) ≫
          R(lowerStar (ModuleCat.{u + 1} A) j).map
            ((pullbackRepresentativeIso j J).inv ≫
              L(upperStar (ModuleCat.{u + 1} A) j).map
                (replacementScalarIdentification).hom ≫
              (scalarRestrictionPullbackIso φ j).hom.app ((scalarExtension φ P).obj L)) ∧
    IsIso ((scalarRestrictionDirectImageMap φ j).app
      (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L))) ∧
    (∃! τ : _root_.DerivedCategory.Q.obj (openComplex j J) ≅
        (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
          (R(lowerStar (ModuleCat.{u + 1} B) j).obj
            (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L))),
      (τ.hom ≫ (scalarRestrictionDirectImageMap φ j).app
          (L(upperStar (ModuleCat.{u + 1} B) j).obj ((scalarExtension φ P).obj L)) =
        scalarTargetNormalization) ∧
      (_root_.DerivedCategory.Q.map (ordinaryMap j Q I J a) ≫ τ.hom =
        (scalarSourceIdentification).hom ≫
          (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
            (coefficientProjection φ j L))) ∧
    (_root_.DerivedCategory.Q.map (ordinaryMap j Q I J a) ≫
        (projectionTargetIdentification).hom =
      (projectionSourceIdentification).hom ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
          (L(upperStar (ModuleCat.{u + 1} A) j).obj L)).app (scalarCoefficient φ P)) ∧
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm
        ((projectionSourceIdentification).inv ≫
          _root_.DerivedCategory.Q.map (ordinaryMap j Q I J a) ≫
          (projectionTargetIdentification).hom) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) j).app
        (R(lowerStar (ModuleCat.{u + 1} A) j).obj
          (L(upperStar (ModuleCat.{u + 1} A) j).obj L))).app (scalarCoefficient φ P) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) U).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
            (L(upperStar (ModuleCat.{u + 1} A) j).obj L))).app
              (L(upperStar (ModuleCat.{u + 1} A) j).obj (scalarCoefficient φ P))) ∧
    (∀ (L' : DerivedCategoryModule A P), boundedDomain φ j L' → ∀ (k : L ⟶ L'),
      (scalarExtension φ P).map (R(lowerStar (ModuleCat.{u + 1} A) j).map
          (L(upperStar (ModuleCat.{u + 1} A) j).map k)) ≫ coefficientProjection φ j L' =
        coefficientProjection φ j L ≫ R(lowerStar (ModuleCat.{u + 1} B) j).map
          (L(upperStar (ModuleCat.{u + 1} B) j).map ((scalarExtension φ P).map k))) := by
  sorry


attribute [instance] HomologicalComplex.monoidalCategoryStruct

end AlgebraicGeometry.Etale.KFlatOpenProjection
