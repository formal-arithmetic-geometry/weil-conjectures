module

public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
public import Sheaf.Paper.FiniteTateSiteDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Canonical finite Tate coordinates for the two purity constructions

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
model paragraph and lem-pur-projection-purity-agreement.
(blueprint: def-pur-affine-diagonal-tate-coordinates)

## Main declarations

* `projectionRootTransition`: the uniquely root-normalized exponent transition.
* `projectionLineIso`: its shifted exact derived site realization, with inverse direction.
* `projectionDiagonalUnit`: the canonical degree-zero unit constraint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

/-- Choice from a proposition that fixes a unique object.
Source: normalized coordinates (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionChooseUnique {α : Sort v} {p : α → Prop} (h : ∃! x, p x) : α :=
  Classical.choose h.exists

/-- The existing finite setting at the positive level n+1; this indexes all n>=1.
Source: finite conventions (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
abbrev projectionSetting (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) : PurityFiniteSetting.{u} :=
  ⟨F, C, E, n + 1, Nat.succ_pos n⟩

/-- The root-power transition needed to put the two existing finite-line presentations
in the same coordinates. It sends each larger root to its ell-th power, tensored
with the identity of A; the normalized equation determines the map uniquely.
Source: Stacks 03PK; finite_tate_site_descent
(blueprint: def-pur-affine-diagonal-tate-coordinates).
Proof: the exponent ell^(n+1) annihilates A. On an etale primitive-root cover,
raising an ell^(n+2)-root to ell identifies the two extended root lines with A
and gives the identity. The pure tensors generate, so these local maps and their
inverses glue uniquely. The same calculation gives the displayed normalization. -/
theorem projectionRootTransition_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    ∃! e : Scheme.finiteEtaleTateTwist T (C.l ^ (n + 2))
        (projectionSetting F C E n).Coefficient (annihilates (projectionSetting F C E n)) 1 ≅
      Scheme.finiteEtaleTateTwist T (C.l ^ (n + 1))
        (projectionSetting F C E n).Coefficient
          (projectionSetting F C E n).diagonalExponent_annihilates 1,
      Scheme.IsFiniteTateEtaleTransition C.l E n T n (n + 1)
        (projectionSetting F C E n).diagonalExponent_annihilates
        (annihilates (projectionSetting F C E n)) 1 e := by
  sorry

/-- The uniquely root-normalized exponent comparison.
Source: the exponent-independence convention
(blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionRootTransition
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :=
  projectionChooseUnique (projectionRootTransition_existsUnique F C E n T aT)

/-- Exact site pullback of a single unit, followed by its specified unit map.
Source: comparison monoidality (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionSingleUnitIso (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (T : Scheme.{u}) (e : (ProEtale.comparisonUpperStar V T).obj (𝟙_ _) ≅ 𝟙_ _) :
    (ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≅
      𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)) :=
  ((ProEtale.comparisonUpperStar V T).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
      _root_.DerivedCategory.singleFunctorObjUnitIso _

/-- The literal single-unit transport, before identifying its ordinary constant source.
Source: comparison monoidality (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionUnitRaw (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  projectionSingleUnitIso (ModuleCat.{u + 1} A) T (ProEtale.comparisonUpperStarUnitIso A T)

/-- The Hom coordinates for exact realization of a shifted single-sheaf isomorphism.
Source: finite twist realization (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def ProjectionSingleShiftIsoType (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] (T : Scheme.{u})
    (G H : Sheaf T.smallEtaleTopology V) :=
  (ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦(2 : ℤ)⟧) ≅
    (ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)

/-- Exact site realization of an isomorphism between degree-zero sheaves, shifted by two.
Source: finite twist realization (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionSingleShiftIso (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] (T : Scheme.{u})
    {G H : Sheaf T.smallEtaleTopology V} (e : G ≅ H) :
    ProjectionSingleShiftIsoType V T G H :=
  (ProEtale.comparisonUpperStar V T).mapDerivedCategory.mapIso
    ((shiftFunctor _ (2 : ℤ)).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e))

/-- The tensor unit, cached at a general coefficient category.
Source: derived tensor conventions (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionTensorUnit (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (T : Scheme.{u}) : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V) := 𝟙_ _

/-- The recorded shifted-line comparison type, cached before selecting its normalized map.
Source: finite Tate coordinates (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def ProjectionLineIsoType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :=
  (ProEtale.VectorIntegrationSite.comparison (projectionSetting F C E n).Coefficient T).obj
    ((Etale.ordinaryFiniteLine (projectionSetting F C E n).Coefficient (C.l ^ (n + 1))
      (projectionSetting F C E n).diagonalExponent_annihilates T)⟦(2 : ℤ)⟧) ≅
    shiftedLine (projectionSetting F C E n) T

/-- The raw root comparison has the two recorded shifted-line endpoints.
Source: coefficient normalization (blueprint: def-pur-affine-diagonal-tate-coordinates).
Proof: finiteEtaleTateTwist at degree one is finiteEtaleTateLine. Unfold ordinaryFiniteLine
and shiftedLine and the positive-level setting; the raw endpoints become the displayed
ones. Transport the raw isomorphism along these equalities. HEq fixes the transported
isomorphism uniquely. -/
theorem projectionLineIso_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    ∃! e : ProjectionLineIsoType F C E n T,
      HEq e (projectionSingleShiftIso
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) T
          (projectionRootTransition F C E n T aT).symm) := by
  sorry

/-- The uniquely root-normalized shifted-line comparison.
Source: coefficient normalization (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionLineIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) :
    ProjectionLineIsoType F C E n T :=
  @projectionChooseUnique (ProjectionLineIsoType F C E n T) _
    (projectionLineIso_existsUnique F C E n T aT)

/-- The diagonal coefficient's degree-zero unit constraint, as a cached type.
Source: finite twist unit (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def ProjectionDiagonalUnitType (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  P.diagonalTwist T 0 ≅ projectionTensorUnit (ModuleCat.{u + 1} P.Coefficient) T

/-- Degree zero of the diagonal twist is the coefficient unit with the raw unit map.
Source: coefficient normalization (blueprint: def-pur-affine-diagonal-tate-coordinates).
Proof: diagonalTwistEtale at zero is ordinaryFiniteUnit. The raw single-unit map
therefore has this source after exact site pullback. Transport along that source equality;
HEq determines the transported isomorphism uniquely. -/
theorem projectionDiagonalUnit_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :
    ∃! e : ProjectionDiagonalUnitType (projectionSetting F C E n) T,
      HEq e (projectionUnitRaw (projectionSetting F C E n).Coefficient T) := by
  sorry

/-- The normalized unit constraint in diagonal-twist coordinates.
Source: coefficient normalization (blueprint: def-pur-affine-diagonal-tate-coordinates). -/
def projectionDiagonalUnit
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :
    ProjectionDiagonalUnitType (projectionSetting F C E n) T :=
  projectionChooseUnique (projectionDiagonalUnit_existsUnique F C E n T)

end WeilConjectures.PurityFiniteSetting
