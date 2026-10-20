/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ProjectiveBundleFormula
public import Sheaf.Paper.KummerAdditivity
public import Sheaf.Paper.SupportedCup
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-!
# Ordinary finite-coefficient Chern classes

Source: Stacks Project, Tag 0FI5, `proposition-chern-class` and
`equation-chern-classes`; blueprint Step 4 (L4) (blueprint: def-pur-chern-classes).

The classes live on the small pro-etale site. The published positive Tate powers
already include the shift by twice their degree. The signed projective-bundle
relation, the unit in degree zero, and vanishing above the rank determine the
entire family uniquely. No projective bundle is required in rank zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Full-support ordinary pro-etale cohomology H^(2j)(T,A(j)), in the derived-Hom
presentation of supported cohomology. The target already includes [2j].
Source: Stacks Tag 0FI5 and the finite coefficient conventions
(blueprint: def-pur-chern-classes). -/
abbrev ordinaryFiniteCohomology (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (j : ℕ) :=
  P.projectiveBundleUnit T ⟶ P.diagonalTwist T j

/-- The unit in degree zero, with no further cohomological shift.
Source: Stacks Tag 0FI5, c_0=1 (blueprint: def-pur-chern-classes). -/
def ordinaryFiniteCohomologyOne (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ordinaryFiniteCohomology P T 0 :=
  𝟙 _

/-- Pullback of a full-support class through the canonical unit and Tate comparisons.
The coefficient transport is the root-normalized transport used by the recorded
projective-bundle formula. Source: Stacks Tag 0FI5, q* in the defining relation
(blueprint: def-pur-chern-classes). -/
def ordinaryFiniteCohomologyPullback (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (i : ℕ)
    (α : ordinaryFiniteCohomology P T i) : ordinaryFiniteCohomology P T' i :=
  (ProEtale.kummerCoefficientPullback P.Coefficient f
      (Etale.ordinaryFiniteUnit P.Coefficient T)
      (Etale.ordinaryFiniteUnit P.Coefficient T')
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f)).inv ≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.map α ≫
    (ProEtale.kummerCoefficientPullback P.Coefficient f
      (P.diagonalTwistEtale T i) (P.diagonalTwistEtale T' i)
      (P.projectiveBundlePositivePullback t f hT i)).hom

/-- Multiply a pro-etale class by a specified Kummer class, in the ordered shifted
Tate coordinates. This is the full-support cup product: the diagonal is inverse
unit multiplication and the exact monoidal comparison identifies the output power.
Source: Stacks Tag 0FI5, equation-chern-classes
(blueprint: def-pur-chern-classes). -/
def ordinaryFiniteHyperplaneStepRaw (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit A T ⟶ (Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
    (i : ℕ)
    (α : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient A N hA T i)) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.affineLinearBaseCoefficient A N hA T (i + 1)) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  let C := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let tensor := ProEtale.derivedTensor (ModuleCat.{u + 1} A) T
  C.map (WeilConjectures.projectiveBundleUnitDiagonal A T) ≫
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (Etale.ordinaryFiniteUnit A T)).app
        (Etale.ordinaryFiniteUnit A T)).hom ≫
    (tensor.map α).app (C.obj (Etale.ordinaryFiniteUnit A T)) ≫
    (tensor.obj (C.obj (Etale.affineLinearBaseCoefficient A N hA T i))).map (C.map h) ≫
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (Etale.affineLinearBaseCoefficient A N hA T i)).app
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)).inv

/-- The preceding full-support cup product for the fixed finite coefficient datum.
Source: Stacks Tag 0FI5, equation-chern-classes
(blueprint: def-pur-chern-classes). -/
def ordinaryFiniteHyperplaneStep (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : ordinaryFiniteCohomology P T i) :
    ordinaryFiniteCohomology P T (i + 1) :=
  ordinaryFiniteHyperplaneStepRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T h i α

/-- The full-support product alpha cup h^j, with h^0=1, using the ordered tensor
powers already employed in projectiveBundleCupPower. Source: Stacks Tag 0FI5,
equation-chern-classes (blueprint: def-pur-chern-classes). -/
def ordinaryFiniteHyperplaneProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α : ordinaryFiniteCohomology P T i) :
    (j : ℕ) → ordinaryFiniteCohomology P T (i + j)
  | 0 => α
  | j + 1 => P.ordinaryFiniteHyperplaneStep T h (i + j)
      (P.ordinaryFiniteHyperplaneProduct T h i α j)

/-- The signed inverse-coordinate relation h^r=sum_i (-1)^(i-1) q*c_i cup h^(r-i).
This is exactly Phi applied to the signed, reverse-ordered Chern coefficients.
All classes and the equality are on the pro-etale site. Source: Stacks Tag 0FI5,
equation-chern-classes (blueprint: def-pur-chern-classes). -/
def ordinaryFiniteProjectiveRelation (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T : Scheme.{u}} {F : T.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization T F)
    (hL : D.L.IsInvertible) (r : ℕ)
    (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i) : Prop :=
  (∑ i : Fin r, (-1 : ℤ) ^ i.val •
    (P.ordinaryFiniteHyperplaneProduct D.A.data.relProj (P.projectiveBundleChern a D hL)
      (i.val + 1)
      (P.ordinaryFiniteCohomologyPullback t D.A.data.relProjHom
        (P.diagonalExponent_isUnit a) (i.val + 1) (c (i.val + 1)))
      (r - (i.val + 1)) ≫
      eqToHom (congrArg (P.diagonalTwist D.A.data.relProj)
        (Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt))))) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
      D.A.data.relProj).mapDerivedCategory.map
        (P.projectiveBundleCupPower D.A.data.relProj (P.projectiveBundleChern a D hL) r)

/-- The unit, above-rank vanishing and the defining projective-bundle relation.
The relation is tested on every normalized quotient-convention realization and
canonical root transport, so no geometry or transport choice enters the classes.
In rank zero the last condition is vacuous. Source: Stacks Tag 0FI5
(blueprint: def-pur-chern-classes). -/
def IsOrdinaryFiniteChernClasses (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (F : T.Modules) (r : ℕ)
    (c : ∀ i : ℕ, ordinaryFiniteCohomology P T i) : Prop :=
  c 0 = P.ordinaryFiniteCohomologyOne T ∧
    (∀ i : ℕ, r < i → c i = 0) ∧
    (0 < r → ∀ (D : ProjectiveBundleRealization T F) (hL : D.L.IsInvertible)
      (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates),
      P.ordinaryFiniteProjectiveRelation t a D hL r c)

/-- Existence and uniqueness needed to extract the projective-bundle coefficients.
Source: Stacks Tag 0FI5, equation-chern-classes; blueprint Step 4 (L4)
(blueprint: def-pur-chern-classes).

Proof: if r=0, set c_0=1 and every positive component to zero. If r>0,
lem-pur-projective-bundle-tautological-geometry supplies the normalized quotient
projective bundle of F, of relative dimension r-1, and its invertible O(1).
Use the root-normalized transport of lem-pur-kummer-additivity and apply
thm-pur-projective-bundle-formula in degree 2r and twist r. Derived adjunction,
finite direct sums and Tate duality identify its cohomology map with Phi:
(a_j) maps to sum q*a_j cup h^j. The displayed recursive cup product is the
full-support product of def-pur-supported-cup: its unit diagonal is inverse
coefficient multiplication and the tensor comparison gives the same total-complex
shift signs. All degrees are even. Take the inverse image of h^r, and set
c_i=(-1)^(i+1) a_(r-i) for 1<=i<=r, c_0=1 and c_i=0 for i>r.
The projective-bundle isomorphism proves uniqueness of these coefficients.
Normalized relative Proj and tautological twist comparisons carry the equation to
every realization; root normalization identifies every permitted transport.
Thus the same unique family satisfies the predicate independently of those data.
No section, supported Euler class or purity isomorphism occurs in this argument. -/
theorem existsUniqueOrdinaryFiniteChernClasses (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] :
    ∃! c : ∀ i : ℕ, ordinaryFiniteCohomology P T i,
      P.IsOrdinaryFiniteChernClasses a F r c := by
  sorry

/-- Ordinary finite-coefficient Chern classes, the uniquely determined signed
coefficients of the projective-bundle relation, including c_0=1 and c_i=0 for i>r.
Source: Stacks Tag 0FI5, equation-chern-classes; blueprint Step 4 (L4)
(blueprint: def-pur-chern-classes). -/
def ordinaryFiniteChernClasses (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] : ∀ i : ℕ, ordinaryFiniteCohomology P T i :=
  (P.existsUniqueOrdinaryFiniteChernClasses a F r).exists.choose

/-- The i-th component of the uniquely characterized ordinary Chern family.
Its degree-zero and above-rank conventions are part of its defining predicate.
Source: Stacks Tag 0FI5 (blueprint: def-pur-chern-classes). -/
def ordinaryFiniteChernClass (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r i : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] : ordinaryFiniteCohomology P T i :=
  P.ordinaryFiniteChernClasses a F r i

end WeilConjectures.PurityFiniteSetting
