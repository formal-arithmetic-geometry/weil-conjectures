/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.ZetaSeries
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Topology.JacobsonSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.AlgebraicGeometry.ProperCompactCoincidence
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint

/-! # Finite-scheme evaluation for pulled-back condensed coefficients

Source: current blueprint, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
lem-a1-finite-boundary-weights.proof.md, opening evaluation assertion, corrected to geometric
fibres as in the reviewed DAG (blueprint: lem-a1-condensed-finite-evaluation).

The coefficient category is the actual condensed constructible heart. Compact cohomology
uses the identity-open compactification of the finite structure map. No Weil structure,
reducedness, nonemptiness, integral lattice, or common coefficient stage is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (Z₀ : Over (Spec (.of D.k₀))) [IsFinite Z₀.hom]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The geometric structure map is the base change of the given finite map.
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, finite geometric fibre
(blueprint: lem-a1-condensed-finite-evaluation). -/
instance a1CondensedFiniteStructureFinite : IsFinite (D.geometricFiber Z₀).hom :=
  inferInstanceAs (IsFinite (pullback.snd Z₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Geometric H_c^0 on the finite geometric fibre, using the existing cohomology functor
with the identity-open compactification of its proper structure map.
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, opening evaluation
(blueprint: lem-a1-condensed-finite-evaluation). -/
def a1CondensedFiniteCompactH0 :=
  DerivedCategory.singleFunctor _ 0 ⋙
    CondensedRing.condensedCompactCohomology ℓ
      (.ofIsProper (D.geometricFiber Z₀).hom) 0

/-- Canonical proper degree-zero normalization: cancel extension by zero along the identity,
then use H^0(Ra_* M) = a_* M, with the existing terminal-section coefficient action.
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, opening evaluation
(blueprint: lem-a1-condensed-finite-evaluation). -/
def a1CondensedFiniteCompactH0Iso :
    a1CondensedFiniteCompactH0 D Z₀ ℓ ≅
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).hom ⋙
        CondensedRing.condensedCoefficientSections ℓ (Spec (.of D.k)) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        (CondensedRing.derivedOpenImmersionLowerShriekId
          (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left)
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber Z₀).hom).rightDerivedFunctor ≪≫
          Functor.leftUnitor _))
    (DerivedCategory.homologyFunctor _ 0 ⋙
      CondensedRing.condensedCoefficientSections ℓ (Spec (.of D.k))) ≪≫
    Functor.isoWhiskerRight
      (Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).hom))
      (CondensedRing.condensedCoefficientSections ℓ (Spec (.of D.k)))

/-- Terminal sections of the actual pullback to a geometric k-point, with its Qbar action.
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, evaluation display
(blueprint: lem-a1-condensed-finite-evaluation). -/
def a1CondensedFiniteFibre
    (z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) z.val ⋙
    CondensedRing.condensedCoefficientSections ℓ (Spec (.of D.k))

/-- The canonical compact degree-zero evaluation: proper H^0 normalization, inverse identity
pullback comparison, then the canonical stalk restriction (composition comparison and counit).
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, opening evaluation
(blueprint: lem-a1-condensed-finite-evaluation). -/
def a1CondensedFiniteEvaluationMap
    (M : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left)
    (z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))) :
    (a1CondensedFiniteCompactH0 D Z₀ ℓ).obj M.obj ⟶
      (a1CondensedFiniteFibre D Z₀ ℓ z).obj M.obj :=
  (a1CondensedFiniteCompactH0Iso D Z₀ ℓ).hom.app M.obj ≫
    (CondensedRing.condensedCoefficientSections ℓ (Spec (.of D.k))).map
      ((CondensedRing.upperStarId (Profinite.padicAlgClRingObj ℓ) (Spec (.of D.k))).inv.app
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
          (D.geometricFiber Z₀).hom).obj M.obj) ≫
        CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj ℓ) z.property M.obj)

set_option maxHeartbeats 1000000 in
-- The double dependent sum and its naturality require elaborating large module functors.
open Classical in
/-- Finite geometric evaluation, including the residue-field indexing and Frobenius cycles.
Source: current blueprint, lem-a1-finite-boundary-weights.proof.md, opening evaluation,
with the geometric correction and orbit normalization of the reviewed DAG
(blueprint: lem-a1-condensed-finite-evaluation).

Proof in words: (1) A finite scheme over k₀ is affine with finite-dimensional coordinate
algebra. Its spectrum is finite and all points are closed. Its residue fields are finite
extensions of k₀ of positive degree. The fibre-product universal property and the
classification of maps from a field spectrum identify the k-points above x with the
k₀-embeddings of κ(x) into k. Such an embedding exists because k is algebraically closed.
The finite-field Galois group consists of the d distinct q-power automorphisms; normality
makes every embedding a unique composite of a fixed embedding with one of them.
(2) In affine tensor coordinates T(z)=g z h⁻¹ corresponds to γ⁻¹ composed with the
residue-field embedding. This is precomposition by q-power Frobenius on κ(x), hence the
points over x form a single d-cycle. Iterating the formula gives g^d z=z h^d.
(3) Finite maps are proper, also after base change. The identity-open compactification
and exact evaluation at the algebraically closed point identify H_c^0 with Γ(s,a_*M).
(4) Apply the non-Weil finite-fibre comparison of
lem-zl-condensed-finite-fibre-frobenius to a₀:Z₀→Spec(k₀), with base point id_s. It identifies
Γ(s,a_*M) with the finite sum of Γ(s,z^*M), naturally in all module maps. Its maps are the
canonical counit restrictions used by a1CondensedFiniteEvaluationMap, and all fibres are
finite dimensional. (5) Reindex by the partition over closed points. The resulting
isomorphism is linear and natural. A finite union of finite bases proves finite
dimensionality. Empty schemes give empty sums and 0≅0; the finite-fibre comparison includes
nonreduced fibres. None of these steps uses a Weil structure. -/
theorem a1_condensed_finite_evaluation (hℓp : ℓ ≠ D.p) :
    Finite (closedPoints Z₀.left) ∧
    (∀ x : closedPoints Z₀.left,
      (∃ E :
          {z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k))) //
            (z.val ≫ pullback.fst Z₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val} ≃
          {ι : Z₀.left.residueField x.val →+* D.k //
            ι.comp (Z₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k},
        ∀ z,
          z.val.val ≫ pullback.fst Z₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
            Spec.map (CommRingCat.ofHom (E z).val) ≫ Z₀.left.fromSpecResidueField x.val) ∧
      Nat.card {z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k))) //
        (z.val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val} =
        Z₀.hom.degreeOver x.val ∧
      1 ≤ Z₀.hom.degreeOver x.val) ∧
    (∃ e : ∀ M :
        ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left,
      (a1CondensedFiniteCompactH0 D Z₀ ℓ).obj M.obj ≃ₗ[CondensedRing.CohomologyScalar.{u} ℓ]
        (⨁ x : closedPoints Z₀.left,
          ⨁ z : {z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k))) //
            (z.val ≫ pullback.fst Z₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val},
            (a1CondensedFiniteFibre D Z₀ ℓ z.val).obj M.obj),
      (∀ M t x z, (e M t) x z = a1CondensedFiniteEvaluationMap D Z₀ ℓ M z.val t) ∧
      (∀ (M N :
          ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left)
        (f : M ⟶ N) (z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k))))
        (t : (a1CondensedFiniteCompactH0 D Z₀ ℓ).obj M.obj),
        a1CondensedFiniteEvaluationMap D Z₀ ℓ N z
            ((a1CondensedFiniteCompactH0 D Z₀ ℓ).map f.hom t) =
          (a1CondensedFiniteFibre D Z₀ ℓ z).map f.hom
            (a1CondensedFiniteEvaluationMap D Z₀ ℓ M z t)) ∧
      (∀ M :
          ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left,
        FiniteDimensional (CondensedRing.CohomologyScalar.{u} ℓ)
          ((a1CondensedFiniteCompactH0 D Z₀ ℓ).obj M.obj)) ∧
      (∀ (M :
          ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) (D.geometricFiber Z₀).left)
        (z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))),
        FiniteDimensional (CondensedRing.CohomologyScalar.{u} ℓ)
          ((a1CondensedFiniteFibre D Z₀ ℓ z).obj M.obj))) ∧
    (∃ T : Equiv.Perm ((D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))),
      (∀ z, (T z).val =
        Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
            D.field_base (Fintype.ofFinite D.k₀) D.field_closure D.algebra_closure
              (inferInstance : Algebra.IsAlgebraic D.k₀ D.k)).symm.toRingHom) ≫
            z.val ≫ (D.geometricFrobenius Z₀).hom) ∧
      (∀ z, ((T z).val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default =
        (z.val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default) ∧
      (∀ (x : closedPoints Z₀.left)
        (z z' : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))),
        (z.val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val →
        (z'.val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val →
        ∃! j : Fin (Z₀.hom.degreeOver x.val), (T ^ j.val) z = z') ∧
      (∀ (x : closedPoints Z₀.left)
        (z : (D.geometricFiber Z₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))),
        (z.val ≫ pullback.fst Z₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) default = x.val →
        z.val ≫ ((D.geometricFrobenius Z₀) ^ Z₀.hom.degreeOver x.val).hom =
          (CategoryTheory.End.asHom
            (CategoryTheory.End.of (Spec.map (CommRingCat.ofHom
              (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
                D.field_base (Fintype.ofFinite D.k₀) D.field_closure D.algebra_closure
                (inferInstance : Algebra.IsAlgebraic D.k₀ D.k)).toRingHom)) ^
                Z₀.hom.degreeOver x.val)) ≫ z.val)) := by
  sorry

end WeilConjectures
