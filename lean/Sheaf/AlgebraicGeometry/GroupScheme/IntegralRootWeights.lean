module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Full character weights on a relative tangent module

Source: Conrad, Reductive group schemes, Definition 5.1.1 and Proposition 5.1.6,
pp.136--138 (blueprint: def-sfb-integral-root-weights).

Weights are tested after every algebra extension, including nonreduced extensions.
This is the functor-of-points form of the full torus coaction eigenmodule.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.IntegralRootWeights

/-- Scalar extension with its pulled-back group law. Source: Conrad, §5.1
(blueprint: def-sfb-integral-root-weights). -/
def scalarChange (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Grp (Over (Spec (.of R))) ⥤ Grp (Over (Spec (.of A))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).mapGrp

/-- Evaluation of the character e_m on an algebra-valued torus point.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-integral-root-weights). -/
def characterValue {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]
    {A : Type u} [CommRing A] [Algebra R A]
    (t : points (ringDiagonalizableGroup R M).X A) (m : M) : A :=
  (Scheme.ΓSpecIso (.of A)).hom
    (t.left.appTop ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra R M))).inv
      (AddMonoidAlgebra.single m 1)))

/-- The character corresponding to m, with e_n sent to e_(n m).
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-integral-root-weights). -/
def character (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] (m : M) :
    ringDiagonalizableGroup R M ⟶ ringDiagonalizableGroup R (ULift.{u} ℤ) :=
  ringDiagonalizableGroupMap R
    ((zmultiplesHom M m).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toAddMonoidHom)

/-- The cocharacter corresponding to the integer dual vector ν, with e_m sent to e_(ν m).
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-integral-root-weights). -/
def cocharacter (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M]
    (ν : Module.Dual ℤ M) :
    ringDiagonalizableGroup R (ULift.{u} ℤ) ⟶ ringDiagonalizableGroup R M :=
  ringDiagonalizableGroupMap R
    (((ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toAddMonoidHom).comp ν.toAddMonoidHom)

/-- Recognition of the geometric coroot by its normalizer reflection formula.
The equality is tested on every scheme over the field; thus it is a scheme identity,
including on nonreduced test schemes. Together with <α,ν> = 2 and the given root α,
this characterizes the usual geometric group coroot (Conrad, §4.2 and Proposition 5.1.6).
(blueprint: def-sfb-integral-root-weights). -/
def IsGeometricCoroot {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]
    (G : Grp (Over (Spec (.of R)))) (i : ringDiagonalizableGroup R M ⟶ G)
    (α : M) (ν : Module.Dual ℤ M) (F : Type u) [Field F] [Algebra R F] : Prop :=
  ∃ n : 𝟙_ (Over (Spec (.of F))) ⟶ ((scalarChange R F).obj G).X,
    ∀ (W : Over (Spec (.of F)))
      (t : W ⟶ ((scalarChange R F).obj (ringDiagonalizableGroup R M)).X),
      (CategoryTheory.CartesianMonoidalCategory.toUnit W ≫ n) *
          (t ≫ ((scalarChange R F).map i).hom.hom) *
          (CategoryTheory.CartesianMonoidalCategory.toUnit W ≫ n)⁻¹ =
        (t / (t ≫ ((scalarChange R F).map (character R α)).hom.hom ≫
          ((scalarChange R F).map (cocharacter R ν)).hom.hom)) ≫
            ((scalarChange R F).map i).hom.hom

/-- The tangent point of a scalar-extended group, projected to the original group.
Source: Conrad, §5.1 (blueprint: def-sfb-integral-root-weights). -/
def tangentPointOver {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : Grp (Over (Spec (.of R)))) (C : Type u) [CommRing C]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (v : GrpObj.Lie ((scalarChange R A).obj G).X) :
    points G.X (DualNumber C) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (DualNumber.mapAlgebraMap C (K := A)).toRingHom) ≫
    (GrpObj.tangentPoint v).left ≫ pullback.fst G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (by
    have hw := (GrpObj.tangentPoint v).w
    change (GrpObj.tangentPoint v).left ≫ pullback.snd G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
        Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A))) at hw
    simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc (GrpObj.tangentPoint v).left, hw]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x <;> simp [DualNumber.mapAlgebraMap, TrivSqZeroExt.algebraMap_eq_inl',
      IsScalarTower.algebraMap_apply R A C])


/-- The m-eigenmodule after scalar extension. The defining equations use conjugation
on dual-number points and every C-valued torus point, for every A-algebra C. Their
solution set is A-linear; its submodule span is therefore exactly that solution set.
Source: Conrad, Definition 5.1.1, pp.136--137
(blueprint: def-sfb-integral-root-weights). -/
def weight {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {M : Type u} [AddCommGroup M] (G : Grp (Over (Spec (.of R))))
    (i : ringDiagonalizableGroup R M ⟶ G) (m : M) :
    Submodule A (GrpObj.Lie ((scalarChange R A).obj G).X) :=
  Submodule.span A {v | ∀ (C : Type u) [CommRing C]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (t : points (ringDiagonalizableGroup R M).X C),
    (points.map G.X ((Algebra.ofId C (DualNumber C)).restrictScalars R) (t ≫ i.hom.hom)) *
        tangentPointOver G C v *
        (points.map G.X ((Algebra.ofId C (DualNumber C)).restrictScalars R) (t ≫ i.hom.hom))⁻¹ =
      points.map G.X ((DualNumber.scale (characterValue (R := R) (A := C) t m)).restrictScalars R)
        (tangentPointOver G C v)}


end AlgebraicGeometry.IntegralRootWeights
