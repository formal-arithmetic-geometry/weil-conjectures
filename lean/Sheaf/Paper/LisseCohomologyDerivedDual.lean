/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.ConstructibleTruncations
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.HomFiniteProjective
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.SpecifiedHomScalarEvaluation

/-! # Evaluation duality for complexes with lisse cohomology

Source: blueprint main-20261015, prop-zl-smooth-proper-relative-purity, Step 3,
paragraph beginning "By Step 1 the cohomology sheaves"; Stacks 08JI for the local
finite-projective computation (blueprint: lem-zl-lisse-cohomology-derived-dual).

The formula is stated in the derived category, retaining the degree of each cohomology
sheaf: Q_i K = (tau GE i)(tau LE i K) = H^i(K)[-i]. Thus the displayed isomorphism
Q_{-i}(K dual) = RHom(Q_i K,unit) is precisely H^{-i}(K dual) = Hom(H^i(K),unit),
after shifting both sides by -i. The evaluation equation fixes the comparison itself.
The right side is concentrated in degree -i; it is ordinary sheaf duality, not a
choice of a splitting of K or an arbitrary isomorphism with its dual.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open AlgebraicGeometry
namespace WeilConjectures.LisseCohomologyDual

/-- A package of the already defined coefficient operations, for writing the same formula
at a finite and at the common coefficient stage. It introduces no new category or operation.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
structure Operations (C : Type a) [Category.{b} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] where
  t : TStructure C
  tensor : C × C ⥤ C
  permitted : ObjectProperty (Cᵒᵖ × C)
  hom : permitted.FullSubcategory ⥤ C
  closed : PodPartialClosed tensor permitted hom
  unit : C
  leftUnitor : ∀ K : C, tensor.obj (unit, K) ≅ K
  lisse : C → Prop

section Formula
variable {C : Type a} [Category.{b} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (A : Operations C)

/-- The cohomology sheaf retained in degree i. Source: blueprint Step 3, truncation
triangles (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def piece (i : ℤ) : C ⥤ C := A.t.truncLE i ⋙ A.t.truncGE i

/-- The permitted coefficient-dual pair, with exactly the bounded-constructibility
hypothesis of the node. Source: blueprint Step 3
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def pair (K : C) (h : A.permitted (op K, A.unit)) : A.permitted.FullSubcategory :=
  ⟨(op K, A.unit), h⟩

/-- The specified coefficient dual. Source: blueprint Step 3
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def dual (K : C) (h : A.permitted (op K, A.unit)) : C := A.hom.obj (pair A K h)

/-- Precomposition in the actual internal-Hom functor, allowing arbitrary rational or
common-stage arrows. Source: blueprint Step 3, naturality
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def dualMap {K L : C} (hK : A.permitted (op K, A.unit))
    (hL : A.permitted (op L, A.unit)) (f : K ⟶ L) : dual A L hL ⟶ dual A K hK :=
  A.hom.map (ObjectProperty.homMk (X := pair A L hL) (Y := pair A K hK)
    (Prod.mkHom f.op (𝟙 A.unit)))

/-- Evaluation restricted to the two canonical upper truncations. Source: blueprint
Step 3, maps u and v (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def restrictedEvaluation (K : C) (hK : A.permitted (op K, A.unit)) (i : ℤ) :=
  A.tensor.map (Prod.mkHom ((A.t.truncLEι (-i)).app (dual A K hK))
    ((A.t.truncLEι i).app K)) ≫ A.closed.evaluation (pair A K hK)

/-- The quotient route for an evaluation comparison. No splitting or basis is selected.
Source: blueprint Step 3, canonical truncation-edge map
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def quotientEvaluation (K : C) (hK : A.permitted (op K, A.unit)) (i : ℤ)
    (hP : A.permitted (op ((piece A i).obj K), A.unit))
    (e : (piece A (-i)).obj (dual A K hK) ⟶ dual A ((piece A i).obj K) hP) :=
  A.tensor.map (Prod.mkHom
    ((A.t.truncGEπ (-i)).app ((A.t.truncLE (-i)).obj (dual A K hK)))
    ((A.t.truncGEπ i).app ((A.t.truncLE i).obj K))) ≫
  A.tensor.map (Prod.mkHom e (𝟙 ((piece A i).obj K))) ≫
  A.closed.evaluation (pair A ((piece A i).obj K) hP)

/-- All cohomology sheaves, allowing zero sheaves and all integer degrees, are lisse.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def LisseCohomology (K : C) : Prop :=
  ∀ i : ℤ, A.lisse ((shiftFunctor C i).obj ((piece A i).obj K))

/-- The evaluation-normalized isomorphisms. The bounds on the target identify it with
ordinary sheaf Hom in degree -i. Uniqueness fixes the map, not only its endpoints.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
structure Comparison (K : C) (hK : A.permitted (op K, A.unit)) where
  cohomology_permitted : ∀ i : ℤ, A.permitted (op ((piece A i).obj K), A.unit)
  iso : ∀ i : ℤ, (piece A (-i)).obj (dual A K hK) ≅
    dual A ((piece A i).obj K) (cohomology_permitted i)
  target_bounds : ∀ i : ℤ,
    A.t.le (-i) (dual A ((piece A i).obj K) (cohomology_permitted i)) ∧
    A.t.ge (-i) (dual A ((piece A i).obj K) (cohomology_permitted i))
  evaluation : ∀ i : ℤ, restrictedEvaluation A K hK i =
    quotientEvaluation A K hK i (cohomology_permitted i) (iso i).hom
  unique : ∀ (i : ℤ)
    (f : (piece A (-i)).obj (dual A K hK) ⟶
      dual A ((piece A i).obj K) (cohomology_permitted i)),
    restrictedEvaluation A K hK i =
      quotientEvaluation A K hK i (cohomology_permitted i) f → f = (iso i).hom

/-- The per-degree cohomology isomorphism, obtained by shifting the derived comparison.
The target is the ordinary dual of H^i K: its concentration and the evaluation equation
are fields of Comparison. Source: blueprint Step 3
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def Comparison.sheafIso {K : C} {hK : A.permitted (op K, A.unit)}
    (e : Comparison A K hK) (i : ℤ) :
    (shiftFunctor C (-i)).obj ((piece A (-i)).obj (dual A K hK)) ≅
      (shiftFunctor C (-i)).obj
        (dual A ((piece A i).obj K) (e.cohomology_permitted i)) :=
  (shiftFunctor C (-i)).mapIso (e.iso i)

/-- A simultaneous comparison for every complex satisfying precisely the node's two
hypotheses, with contravariant naturality on every morphism. Source: blueprint Step 3
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
structure Family where
  comparison : ∀ (K : C), LisseCohomology A K →
    ∀ hK : A.permitted (op K, A.unit), Comparison A K hK
  naturality : ∀ (K L : C) (k : LisseCohomology A K) (l : LisseCohomology A L)
    (hK : A.permitted (op K, A.unit)) (hL : A.permitted (op L, A.unit)) (f : K ⟶ L)
    (i : ℤ),
    (piece A (-i)).map (dualMap A hK hL f) ≫ ((comparison K k hK).iso i).hom =
      ((comparison L l hL).iso i).hom ≫
        dualMap A ((comparison K k hK).cohomology_permitted i)
          ((comparison L l hL).cohomology_permitted i) ((piece A i).map f)
end Formula

section Transport
variable {C : Type a} [Category.{b} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type c} [Category.{d} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  (A : Operations C) (A' : Operations B) (F : C ⥤ B)

/-- Normalized transport data: truncation comparisons commute with their canonical
unit and counit; the dual comparison carries evaluation to evaluation. The tensor
and unit comparisons are supplied by the recorded operation, not chosen freely.
Source: blueprint Step 3, isomorphism and scalar compatibility
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
structure Transport (tensor : ∀ K L : C,
    F.obj (A.tensor.obj (K, L)) ≅ A'.tensor.obj (F.obj K, F.obj L))
    (unit : F.obj A.unit ≅ A'.unit) where
  tensor_naturality : ∀ (K L M N : C) (f : K ⟶ M) (g : L ⟶ N),
    F.map (A.tensor.map (Prod.mkHom f g)) ≫ (tensor M N).hom =
      (tensor K L).hom ≫ A'.tensor.map (Prod.mkHom (F.map f) (F.map g))
  unit_normalization : ∀ K : C,
    (tensor A.unit K).hom ≫ A'.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
      (A'.leftUnitor (F.obj K)).hom = F.map (A.leftUnitor K).hom
  le : ∀ i : ℤ, A.t.truncLE i ⋙ F ≅ F ⋙ A'.t.truncLE i
  ge : ∀ i : ℤ, A.t.truncGE i ⋙ F ≅ F ⋙ A'.t.truncGE i
  le_counit : ∀ (i : ℤ) (K : C), (le i).hom.app K ≫
    (A'.t.truncLEι i).app (F.obj K) = F.map ((A.t.truncLEι i).app K)
  ge_unit : ∀ (i : ℤ) (K : C), F.map ((A.t.truncGEπ i).app K) ≫
    (ge i).hom.app K = (A'.t.truncGEπ i).app (F.obj K)
  permitted : ∀ (K : C), A.permitted (op K, A.unit) →
    A'.permitted (op (F.obj K), A'.unit)
  dual : ∀ (K : C) (hK : A.permitted (op K, A.unit)),
    F.obj (LisseCohomologyDual.dual A K hK) ≅
      LisseCohomologyDual.dual A' (F.obj K) (permitted K hK)
  dual_naturality : ∀ (K L : C) (hK : A.permitted (op K, A.unit))
    (hL : A.permitted (op L, A.unit)) (f : K ⟶ L),
    F.map (dualMap A hK hL f) ≫ (dual K hK).hom =
      (dual L hL).hom ≫ dualMap A' (permitted K hK) (permitted L hL) (F.map f)
  evaluation : ∀ (K : C) (hK : A.permitted (op K, A.unit)),
    (tensor (LisseCohomologyDual.dual A K hK) K).hom ≫
      A'.tensor.map (Prod.mkHom (dual K hK).hom (𝟙 _)) ≫
      A'.closed.evaluation (pair A' (F.obj K) (permitted K hK)) =
    F.map (A.closed.evaluation (pair A K hK)) ≫ unit.hom
  lisse : ∀ (K : C), LisseCohomology A K → LisseCohomology A' (F.obj K)

variable {tensor : ∀ K L : C,
    F.obj (A.tensor.obj (K, L)) ≅ A'.tensor.obj (F.obj K, F.obj L)}
  {unit : F.obj A.unit ≅ A'.unit}

/-- The cohomology-piece comparison induced by the uniquely normalized truncation maps.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def Transport.piece (p : Transport A A' F tensor unit) (i : ℤ) (K : C) :
    F.obj ((piece A i).obj K) ≅ (piece A' i).obj (F.obj K) :=
  (p.ge i).app ((A.t.truncLE i).obj K) ≪≫
    (A'.t.truncGE i).mapIso ((p.le i).app K)

/-- The explicit commuting comparison square, including the dual of the cohomology
comparison on the right. Source: blueprint Step 3
(blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def Compatible (a : Family A) (a' : Family A')
    (p : Transport A A' F tensor unit) : Prop :=
  ∀ (K : C) (k : LisseCohomology A K) (hK : A.permitted (op K, A.unit)) (i : ℤ),
    F.map ((a.comparison K k hK).iso i).hom ≫
      (p.dual ((piece A i).obj K) ((a.comparison K k hK).cohomology_permitted i)).hom ≫
      dualMap A' ((a'.comparison (F.obj K) (p.lisse K k) (p.permitted K hK)).cohomology_permitted i)
        (p.permitted ((piece A i).obj K) ((a.comparison K k hK).cohomology_permitted i))
        (Transport.piece A A' F p i K).inv =
    (Transport.piece A A' F p (-i) (dual A K hK)).hom ≫
      (piece A' (-i)).map (p.dual K hK).hom ≫
      ((a'.comparison (F.obj K) (p.lisse K k) (p.permitted K hK)).iso i).hom
end Transport

section ActualOperations
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The finite-stage operations are literally the recorded raw rationalization and Hom.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def rational (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : LisseRealization.Base D l hl) :
    Operations (sfRationalConstructibleCategory l E X.scheme) where
  t := sfRationalStandardTStructure l E X.scheme D hl
  tensor := rationalDerivedTensor l E X.scheme
  permitted := constructibleRationalHomPairs l E X.scheme
  hom := rationalDerivedInternalHom l E X.scheme
  closed := podRationalClosed l E X.scheme
  unit := pullbackTensorRationalUnit l E X.scheme
  leftUnitor := pullbackTensorRationalLeftUnitor l E X.scheme
  lisse := rationalLisseHeartProperty l E X.scheme

/-- The common-stage operations use the existing finite-field pair category.
Source: blueprint Step 3 (blueprint: lem-zl-lisse-cohomology-derived-dual). -/
def common (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : LisseRealization.Base D l hl) :
    Operations (generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme) where
  t := sfCommonStageStandardTStructure l X.scheme Ω D hl
  tensor := commonStageDerivedTensor l Ω X.scheme
  permitted := commonStageHomPairs l Ω X.scheme
  hom := commonStageDerivedInternalHom l Ω X.scheme
  closed := podCommonClosed l Ω X.scheme
  unit := pullbackTensorCommonUnit l Ω X.scheme
  leftUnitor := pullbackTensorCommonLeftUnitor l Ω X.scheme
  lisse := fun K ↦ sfCommonStageHeartProperty l X.scheme Ω K ∧
    IsCommonStageLisse l Ω X.scheme K

/-- The coefficient-dual cohomology theorem, as evaluation-normalized derived isomorphisms
and contravariant naturality at every finite and common coefficient stage.

Source: blueprint main-20261015, prop-zl-smooth-proper-relative-purity, Step 3,
paragraph beginning "By Step 1 the cohomology sheaves"; local computation: Stacks 08JI
(blueprint: lem-zl-lisse-cohomology-derived-dual).

Proof plan (the node's nine steps):
1. Internal Hom reverses triangles and sends a shift s to -s in the ambient completed
ringed category. Linear scalar localization gives the same assertion rationally;
common-stage finite diagrams give it over the algebraic closure.
2. Lisse heart objects are locally finite free. Their higher coefficient Ext sheaves
vanish by lem-sf-hom-finite-projective; evaluation identifies the degree-zero Hom
with the ordinary sheaf dual. The lisse realization preserves this evaluation.
3. Induct on the finite cohomological interval using truncation triangles. Dualizing
[a,b] gives [-b,-a]. Intermediate duals are finite extensions of the constructible
heart duals, so their constructibility is a conclusion, not a new hypothesis.
4. At i restrict to tau LE i K. The dual maps from K and from Q_i K induce inverse
edge isomorphisms in degree -i: the neighboring cohomologies of their dual cones vanish.
Their composite gives the displayed comparison, including degrees outside the support.
5. Functoriality of the two truncation arrows proves naturality. Their evaluation
pairings descend to the two quotients, giving the defining equation. Orthogonality
and the tensor-Hom adjunction prove uniqueness; the signed shift comparison gives
exactly ordinary evaluation on H^i K, with no splitting chosen.
6. Scheme-isomorphism inverse image is an exact equivalence preserving units.
lem-pod-derived-automorphism-hom-evaluation preserves evaluation; unique t-exact
truncation comparisons transport both edge maps and hence their composite.
7. Finite free completed scalar change is exact and t-exact. The actual specified
Hom comparison is the evaluation transpose by lem-zl-specified-hom-scalar-evaluation,
not merely by tower coherence. The same two-edge-map square proves scalar compatibility.
8. Descend each finite diagram to a common finite coefficient field. The specified
Hom scalar maps, their identity and tower laws make the comparison and its equations
independent of representatives, preserving evaluation and both inverse equations.
9. Apply isomorphism-pullback compatibility to geometric Frobenius, then naturality
to theta^{-1}. The dual Frobenius is Hom(theta^{-1},1) after the normalized pullback
comparison, so the resulting equality is exactly the Weil-morphism equation. -/
theorem lisseCohomologyDerivedDual :
    ∃ (a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (X : LisseRealization.Base D l hl) [IsSeparated (X.scheme ↘ Spec (.of D.k))],
        Family (rational D l hl E X))
      (b : ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (X : LisseRealization.Base D l hl) [IsSeparated (X.scheme ↘ Spec (.of D.k))],
        Family (common D l hl Ω X)),
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (X : LisseRealization.Base D l hl) [IsSeparated (X.scheme ↘ Spec (.of D.k))]
        (Y : LisseRealization.Base D l hl) [IsSeparated (Y.scheme ↘ Spec (.of D.k))]
        (h : X.scheme ≅ Y.scheme),
        ∃ (e : (rationalDerivedPullback l E h.hom).obj (rational D l hl E Y).unit ≅
          (rational D l hl E X).unit)
          (p : Transport (rational D l hl E Y) (rational D l hl E X)
          (rationalDerivedPullback l E h.hom)
          (fun K L ↦ canonicalRationalPullbackTensor l E h.hom K L) e),
          Compatible _ _ _ (a E Y) (a E X) p) ∧
      (∀ (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
        [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L) (X : LisseRealization.Base D l hl)
        [IsSeparated (X.scheme ↘ Spec (.of D.k))],
        ∃ p : Transport (rational D l hl E X) (rational D l hl L X)
          (sfRationalScalarExtension l E X.scheme 0 (Fact.out : l.Prime).ne_zero L ι)
          (fun K M ↦ (rationalTensorScalarComparison l E L ι X.scheme).app (K, M))
          (pullbackTensorRationalScalarUnit l E L ι X.scheme),
          Compatible _ _ _ (a E X) (a L X) p) ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (X : LisseRealization.Base D l hl) [IsSeparated (X.scheme ↘ Spec (.of D.k))]
        (Y : LisseRealization.Base D l hl) [IsSeparated (Y.scheme ↘ Spec (.of D.k))]
        (h : X.scheme ≅ Y.scheme),
        ∃ (e : (commonStageDerivedPullback l Ω h.hom).obj (common D l hl Ω Y).unit ≅
          (common D l hl Ω X).unit)
          (p : Transport (common D l hl Ω Y) (common D l hl Ω X)
          (commonStageDerivedPullback l Ω h.hom)
          (fun K L ↦ canonicalCommonStagePullbackTensor l Ω h.hom K L) e),
          Compatible _ _ _ (b Ω Y) (b Ω X) p) ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (X : LisseRealization.Base D l hl) [IsSeparated (X.scheme ↘ Spec (.of D.k))]
        (E : AlgebraicallyClosedCoefficients.Index l Ω),
        ∃ (tensor : ∀ K L : sfRationalConstructibleCategory l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X.scheme,
            (GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := Ω) (Y := X.scheme) E).obj
                ((rational D l hl
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).tensor.obj (K, L)) ≅
            (common D l hl Ω X).tensor.obj
              ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K,
                (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj L))
          (unit : (GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := Ω) (Y := X.scheme) E).obj
                (rational D l hl
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).unit ≅
                    (common D l hl Ω X).unit)
          (p : Transport
            (rational D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X)
            (common D l hl Ω X) (GeneralAlgebraicallyClosedCoefficients.inclusion E)
            tensor unit),
          Compatible _ _ _ (a (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X)
            (b Ω X) p) := by
  sorry

end ActualOperations

section WeilEquation
variable {C : Type a} [Category.{b} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (A : Operations C) (F : C ⥤ C)
  (tensor : ∀ K L : C, F.obj (A.tensor.obj (K, L)) ≅
    A.tensor.obj (F.obj K, F.obj L)) (unit : F.obj A.unit ≅ A.unit)

/-- The explicit Weil-morphism equation for the contragredient structure. Specializing
F to sfWeilFrobeniusPullback or sfCommonStageWeilFrobeniusPullback and theta to the
structure isomorphism of the recorded fixed pair gives exactly the node's Weil clause.
The source Frobenius is Q_{-i}(D(theta^{-1}) c_K); the target Frobenius is
D((Q_i(theta) q_K)^{-1}) c_{Q_i K}. Thus this is a commuting square of actual arrows,
not an existential choice of a new Weil structure.

Source: blueprint Step 3, Frobenius-equivariant cohomology identification
(blueprint: lem-zl-lisse-cohomology-derived-dual).
Proof: apply Compatible to K, then naturality of the comparison to theta^{-1}.
Functoriality of the canonical truncation comparisons identifies Q_i(theta) q_K
with the induced cohomology Weil structure. Contravariance identifies its inverse
with the dual structure. The resulting equality is the displayed square. This is
step 9 of the owning node; the preceding steps supply the compatible families. -/
theorem weil_equation (a : Family A) (p : Transport A A F tensor unit)
    (hp : Compatible A A F a a p) (K : C) (k : LisseCohomology A K)
    (hK : A.permitted (op K, A.unit)) (theta : F.obj K ≅ K) (i : ℤ) :
    ∃ hQ : A.permitted (op (F.obj ((piece A i).obj K)), A.unit),
      F.map ((a.comparison K k hK).iso i).hom ≫
          (p.dual ((piece A i).obj K) ((a.comparison K k hK).cohomology_permitted i)).hom ≫
          dualMap A ((a.comparison K k hK).cohomology_permitted i) hQ
            (((Transport.piece A A F p i K) ≪≫ (piece A i).mapIso theta).inv) =
        (Transport.piece A A F p (-i) (dual A K hK)).hom ≫
          (piece A (-i)).map ((p.dual K hK).hom ≫
            dualMap A hK (p.permitted K hK) theta.inv) ≫
          ((a.comparison K k hK).iso i).hom := by
  sorry
end WeilEquation
end WeilConjectures.LisseCohomologyDual
