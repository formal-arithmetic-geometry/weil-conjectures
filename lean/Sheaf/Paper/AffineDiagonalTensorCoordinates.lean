module

public import Sheaf.Paper.AffineDiagonalTateCoordinates
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Tensor coordinates between diagonal and ordered affine purity

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
model paragraph and lem-pur-projection-purity-agreement.
(blueprint: def-pur-affine-diagonal-tensor-coordinates)

## Main declarations

* `projectionTensorActionGeneric`: actual generic ordered tensor recursion.
* `projectionTensorStep`: canonical comparison-monoidal and root-power successor.
* `projectionTensorActionIso`: its normalized specialization to the two purity sources.
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

/-- The successor ell-power annihilator in the fixed positive-level scalar ring.
Source: finite coefficient conventions
(blueprint: def-pur-affine-diagonal-tensor-coordinates).
Proof: diagonalExponent_annihilates gives ell^(n+1)=0. Multiply this equality by ell
and use pow_succ and Nat.cast_mul to obtain ell^(n+2)=0, without any ramification bound. -/
theorem projectionNextAnnihilator
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E] (n : ℕ) :
    ((C.l ^ (n + 2) : ℕ) : (projectionSetting F C E n).Coefficient) = 0 := by
  sorry

/-- The recorded shifted line in literal fixed-scalar coordinates.
Source: finite Tate line (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionShiftedLine
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) T).mapDerivedCategory.obj
      ((Etale.ordinaryFiniteLine (projectionSetting F C E n).Coefficient
        (C.l ^ (n + 2)) (projectionNextAnnihilator F C E n) T)⟦(2 : ℤ)⟧)

/-- Generic ordered tensor action in the existing monoidal category. It uses only
its tensor, associator and right unitor, so specialization shares one monoidal instance.
Source: twist-additivity conventions (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorActionGeneric (B : Type v) [Category.{w} B] [MonoidalCategory B]
    (L : ℕ → B) (line : B) (e0 : L 0 ≅ 𝟙_ B)
    (es : ∀ d : ℕ, L (d + 1) ≅ ((curriedTensor B).obj (L d)).obj line) (M : B) :
    (d : ℕ) → ((curriedTensor B).obj M).obj (L d) ≅
      (action ((curriedTensor B).flip.obj line) d).obj M
  | 0 => ((curriedTensor B).obj M).mapIso e0 ≪≫ ρ_ M
  | d + 1 => ((curriedTensor B).obj M).mapIso (es d) ≪≫
      (α_ M (L d) line).symm ≪≫
      ((curriedTensor B).flip.obj line).mapIso
        (projectionTensorActionGeneric B L line e0 es M d)

/-- Comparison monoidality followed by tensoring the specified second-factor map,
checked once at an abstract coefficient category.
Source: derived exact comparison monoidality
(blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorStepGeneric (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (T : Scheme.{u}) [(ProEtale.comparisonUpperStar V T).PreservesFlat]
    (M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology V))
    (B : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))
    (e : (ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj N ≅ B) :
    (ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj
      (((Etale.derivedTensor V T).obj M).obj N) ≅
    ((ProEtale.derivedTensor V T).obj
      ((ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj M)).obj B :=
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso V M).app N ≪≫
    ((ProEtale.derivedTensor V T).obj
      ((ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj M)).mapIso e

/-- Comparison monoidality with the shifted single realization of a specified sheaf map.
Source: the coefficient successor constraint
(blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorStepFromSheafGeneric
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (T : Scheme.{u}) [(ProEtale.comparisonUpperStar V T).PreservesFlat]
    (M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology V))
    {G H : Sheaf T.smallEtaleTopology V} (e : G ≅ H) :
    Σ X Y : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V), X ≅ Y :=
  ⟨_, _, projectionTensorStepGeneric V T M
    (((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦(2 : ℤ)⟧)
    ((ProEtale.comparisonUpperStar V T).mapDerivedCategory.obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧))
    (projectionSingleShiftIso V T e)⟩

/-- The finite-module specialization, with the coefficient ring still an abstract type.
Source: finite coefficient successor (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorStepFromSheaf (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (M : Etale.DerivedCategoryModule A T)
    {G H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (e : G ≅ H) :
    Σ X Y : AlgebraicGeometry.ProEtale.AffineSpacePurity.C A T, X ≅ Y :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  projectionTensorStepFromSheafGeneric (ModuleCat.{u + 1} A) T M e

/-- The exact successor coefficient-comparison type.
Source: finite Tate coordinates (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def ProjectionTensorStepType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (d : ℕ) :=
  (projectionSetting F C E n).diagonalTwist T (d + 1) ≅
    ((ProEtale.derivedTensor
      (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) T).obj
        ((projectionSetting F C E n).diagonalTwist T d)).obj
      (projectionShiftedLine F C E n T)

/-- Normalization by the literal finite-scalar comparison-monoidal map. Every
presentation datum, including the two root-line sheaves, is pinned to the actual one.
Source: successor twist coordinates
(blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def IsProjectionTensorStep
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ)
    (e : ProjectionTensorStepType F C E n T d) : Prop :=
  ∀ (A : Type (u + 1)) [hA : CommRing A] [Finite A]
    (M : Etale.DerivedCategoryModule A T)
    (G H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (s : G ≅ H),
    HEq A (projectionSetting F C E n).Coefficient →
    HEq hA (coefficientCommRing (projectionSetting F C E n)) →
    HEq M ((projectionSetting F C E n).diagonalTwistEtale T d) →
    HEq G (Scheme.finiteEtaleTateTwist T (C.l ^ (n + 1))
      (projectionSetting F C E n).Coefficient
        (projectionSetting F C E n).diagonalExponent_annihilates 1) →
    HEq H (Scheme.finiteEtaleTateTwist T (C.l ^ (n + 2))
      (projectionSetting F C E n).Coefficient (annihilates (projectionSetting F C E n)) 1) →
    HEq s (projectionRootTransition F C E n T aT).symm →
    HEq e (projectionTensorStepFromSheaf A T M s).2.2

/-- The successor coefficient has the raw tensor-comparison endpoints.
Source: ordered finite twist (blueprint: def-pur-affine-diagonal-tensor-coordinates).
Proof: diagonalTwistEtale is affineLinearBaseCoefficient, whose successor is the
previous power tensored with the shifted ordinary line. Exact site pullback gives
the source of the displayed finite-scalar tensor constraint. Its target is the previous
comparison power tensored with the shifted line, by the root-normalized
sheaf map. Transport along those equalities;
The normalization ranges over every sheaf-map presentation of the given root map;
the ring, structure, diagonal coefficient and both root-line sheaves are pinned by HEq,
so after substituting them the root map itself is pinned by ordinary equality.
Take A to be the existing coefficient ring with coefficientCommRing and its finite
instance, and take the actual root line pair and diagonal coefficient as a presentation;
it exists without a purity map. HEq then fixes the transported isomorphism uniquely. -/
theorem projectionTensorStep_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    ∃! e : ProjectionTensorStepType F C E n T d,
      IsProjectionTensorStep F C E n T aT d e := by
  sorry

/-- The canonically normalized successor tensor constraint.
Source: ordered finite twist (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorStep
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k)) (d : ℕ) :
    ProjectionTensorStepType F C E n T d :=
  projectionChooseUnique (projectionTensorStep_existsUnique F C E n T aT d)

/-- The normalized tensor-action comparison type in the recorded source coordinates.
Source: twist additivity (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def ProjectionTensorActionIsoType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u})
    (M : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T) (d : ℕ) :=
  ((smoothPurityTensor (projectionSetting F C E n).Coefficient T).obj M).obj
    ((projectionSetting F C E n).diagonalTwist T d) ≅
    (action ((tensor (projectionSetting F C E n).Coefficient T).flip.obj
      (shiftedLine (projectionSetting F C E n) T)) d).obj M

/-- Endpoint-independent characterization by the actual generic tensor recursion.
It quantifies over every presentation of the fixed unit and successor isomorphisms.
Source: canonical tensor-coordinate transport
(blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def IsProjectionTensorAction
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T) (d : ℕ)
    (e : ProjectionTensorActionIsoType F C E n T M d) : Prop :=
  ∀ (L : ℕ → AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T)
    (line : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T)
    (e0 : L 0 ≅ 𝟙_ (AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T))
    (es : ∀ i : ℕ, L (i + 1) ≅
      ((curriedTensor (AlgebraicGeometry.ProEtale.AffineSpacePurity.C
        (projectionSetting F C E n).Coefficient T)).obj (L i)).obj line),
    (∀ i : ℕ, HEq (L i) ((projectionSetting F C E n).diagonalTwist T i)) →
    HEq line (projectionShiftedLine F C E n T) →
    HEq e0 (projectionDiagonalUnit F C E n T) →
    (∀ i : ℕ, HEq (es i) (projectionTensorStep F C E n T aT i)) →
    HEq e (projectionTensorActionGeneric
      (AlgebraicGeometry.ProEtale.AffineSpacePurity.C
        (projectionSetting F C E n).Coefficient T) L line e0 es M d)

/-- The generic tensor recursion has the exact cached tensor endpoints of the two
published purity maps. It specifies only coordinates, independently of either arrow.
Source: tensor reassociation (blueprint: def-pur-affine-diagonal-tensor-coordinates).
Proof: smoothPurityTensor and tensor are the same published derived tensor. At the
positive setting Q, AffineLinePurity.Ring Q is Q.Coefficient: (n+1)-1 reduces to n.
The literal projectionShiftedLine is therefore the recorded shiftedLine, with the
annihilator proofs identified by proof irrelevance. Unfold these endpoint aliases in
the displayed generic recursion. Transport the resulting isomorphism to the displayed
endpoints. For the quantified normalization, take L to be the diagonal powers, line
to be the fixed shifted line, and e0 and es to be the specified constraints, after
unfolding the tensor aliases. This tuple exists independently of purity. Every other
normalized tuple is the same after the endpoint equalities. Hence its recursion
transports to the same isomorphism, and this one tuple proves uniqueness. -/
theorem projectionTensorActionIso_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T) (d : ℕ) :
    ∃! e : ProjectionTensorActionIsoType F C E n T M d,
      IsProjectionTensorAction F C E n T aT M d e := by
  sorry

/-- The canonical ordered tensor reassociation in the recorded source coordinates.
Source: tensor reassociation (blueprint: def-pur-affine-diagonal-tensor-coordinates). -/
def projectionTensorActionIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (T : Scheme.{u}) (aT : T ⟶ Spec (.of F.k))
    (M : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient T) (d : ℕ) :
    ProjectionTensorActionIsoType F C E n T M d :=
  projectionChooseUnique (projectionTensorActionIso_existsUnique F C E n T aT M d)

attribute [local irreducible] projectionTensorActionIso projectionTensorActionGeneric
  projectionTensorStep projectionLineIso projectionUnitRaw

end WeilConjectures.PurityFiniteSetting
