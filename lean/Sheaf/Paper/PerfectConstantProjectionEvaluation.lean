/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Finite perfect coefficients in a normalized strict projection

The finite-level perfect projection formula on the original small pro-etale site.
Its object universe is one larger than its morphism universe. This interface records
ordinary coefficient balancing and the derived counits, so it applies to any derived
model of an ordinary strict diagram, independently of that diagram's transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ConstantPerfectProjection

section ModelPullNormalization

variable {B C T U : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [Category T] [Abelian T] [Category U] [Abelian U]
  [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory T] [HasDerivedCategory U]
  (F : B ⥤ T) [F.Additive] (G : C ⥤ U) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
  (DF : DerivedReductionModelData F M) (DG : DerivedReductionModelData G N)
  (e : F ⋙ H ≅ P ⋙ G)

set_option linter.defProp false in
/-- Counit normalization for an exact square of derived models.
Source: Stacks Tag 06YY (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def PullNormalized
    (η : DF.reduction ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ DG.reduction) : Prop :=
      ∀ K : CochainComplex B ℤ, M K →
        η.hom.app (DerivedCategory.Q.obj K) ≫
          DG.reduction.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            DG.complexCounit ((P.mapHomologicalComplex (.up ℤ)).obj K) =
        H.mapDerivedCategory.map (DF.complexCounit K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)

end ModelPullNormalization

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The specified finite quotient map from constant coefficients.
Source: Stacks 099M (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def coefficient (X : Scheme.{t}) (n : ℕ) :
    exchangeConstantRing X A ⟶ d.finiteRing X n := exchangeScalar d X ≫ d.projection X n

/-- Scalar extension followed by restriction to the original constant coefficients.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def scalarLevel (X : Scheme.{t}) (n : ℕ) :
    proEtaleRingModules X (exchangeConstantRing X A) ⥤
      proEtaleRingModules X (exchangeConstantRing X A) :=
  reductionChange X (coefficient d X n) ⋙ reductionRestrict X (coefficient d X n)

/-- Naturality of the constant-to-finite quotient map.
Source: Stacks 099M (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
theorem coefficient_comm {U V : Scheme.{t}} (f : U ⟶ V) (n : ℕ) :
    (exchangeConstantIso f A).hom ≫ coefficient d U n =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map (coefficient d V n) ≫
        (d.finiteRingIso f n).hom := by
  unfold coefficient
  rw [← Category.assoc, exchangeScalar_comm, Category.assoc, d.projection_comm]
  rw [← Category.assoc, ← Functor.map_comp]

variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The scalar-extension comparison, as the mate of restriction/pullback.
Source: Stacks 0D6D (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def scalarPullInv (n : ℕ) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (coefficient d V n))
    (proEtaleRingExtensionAdjunction (coefficient d U n))).symm
      (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n)
        (coefficient d V n) (coefficient d U n)
        (exchangeConstantIso f A) (d.finiteRingIso f n) (coefficient_comm d f n))

/-- The canonical ordinary tensor/pullback comparison at one quotient.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def ordinaryComparison (n : ℕ) [IsIso (scalarPullInv d f n)] :
    scalarLevel d V n ⋙ proEtaleRingModulePullback f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ scalarLevel d U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (coefficient d V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A)
        (d.finiteRing U n) (coefficient d V n) (coefficient d U n)
        (exchangeConstantIso f A) (d.finiteRingIso f n) (coefficient_comm d f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A)
          (d.finiteRing U n) (coefficient d V n) (coefficient d U n)
          (exchangeConstantIso f A) (d.finiteRingIso f n) (coefficient_comm d f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (scalarPullInv d f n)).symm
      (proEtaleRingRestrictScalars (coefficient d U n)) ≪≫
    Functor.associator _ _ _

section Models
variable
  (FV : proEtaleRingModules V (exchangeConstantRing V A) ⥤
    exchangeTowers V (exchangeConstantRing V A)) [FV.Additive]
  (FU : proEtaleRingModules U (exchangeConstantRing U A) ⥤
    exchangeTowers U (exchangeConstantRing U A)) [FU.Additive]
  (DV : DerivedReductionModelData FV
    (CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A)))
  (DU : DerivedReductionModelData FU
    (CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing U A)))
  (e : FV ⋙ exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A) ≅
    proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A) ⋙ FU)
  (τ : DV.reduction ⋙ exchangeConstantPull (A := A) f ≅
    proEtaleRingDerivedPullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A) ⋙ DU.reduction)

/-- The counit adjunct whose finite evaluation is the perfect projection formula.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-perfect-constant-projection-evaluation). -/
def projection (K : reductionDerivedCategory U (exchangeConstantRing U A)) :
    DV.reduction.obj ((proEtaleRingDerivedDirectImage f (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso f A)).obj K) ⟶
    (exchangeConstantPush (A := A) f).obj (DU.reduction.obj K) :=
  (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)).homEquiv _ _
      (τ.hom.app ((proEtaleRingDerivedDirectImage f (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso f A)).obj K) ≫
        DU.reduction.map ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).counit.app K))

/-- A single perfect constant coefficient makes the normalized projection invertible
at that evaluation. No compatibility between different evaluations is assumed.
Source: Stacks Tags 0B56 and 0944, with evaluation of K-injective diagrams as in 0941
(blueprint: lem-sf-cbc-perfect-constant-projection-evaluation).

Proof: take a bounded finite-projective A-complex representing A/I^(n+1), supplied
by d.quotientPerfect. The exact constant-module functor takes it to a bounded
complex whose terms are explicit retracts of finite free constant sheaves. The
canonical finite-coefficient comparison identifies its degree-zero derived object
with the coefficient of scalarLevel. The two maps ev applied to DV.counit and
DU.counit are invertible on flat-term K-flat representatives. Hence their
localization comparisons identify the evaluated reductions with tensor by this
constant perfect complex. The displayed ordinary balancing square and PullNormalized
identify the evaluated pullback comparison with the canonical tensor comparison:
check on flat-term K-flat representatives and use their localization property.
Choose a K-injective representative of K. Evaluation of a K-injective strict tower
is K-injective because its left adjoint is exact. Thus evaluation of the tower
adjunction counit is the ordinary derived counit, under the canonical direct-image
evaluation comparison. The evaluated projection is consequently the ordinary
counit-tensor projection. For a finite free coefficient this is the finite-product
comparison, including rank zero; for a finite-projective term restrict the finite
free inverse along its inclusion and retraction. Form the finite signed total
maps for the bounded coefficient complex. The two inverse equations hold on
each summand, so localization gives inverse morphisms in the unbounded derived
category. Conjugating by the previously specified model and evaluation comparisons
proves the assertion. This argument is at one index and uses no faithfulness or
conservativity assertion about the family of derived evaluations. -/
theorem evaluation_isIso (n : ℕ) [IsIso (scalarPullInv d f n)]
    (hτ : PullNormalized FV FU
      (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A))
      (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)) DV DU e τ)
    (eV : FV ⋙ (CategoryTheory.evaluation ℕᵒᵖ (proEtaleRingModules V
      (exchangeConstantRing V A))).obj (op n) ≅ scalarLevel d V n)
    (eU : FU ⋙ (CategoryTheory.evaluation ℕᵒᵖ (proEtaleRingModules U
      (exchangeConstantRing U A))).obj (op n) ≅ scalarLevel d U n)
    (he : ∀ M : proEtaleRingModules V (exchangeConstantRing V A),
      (e.hom.app M).app (op n) ≫
          eU.hom.app ((proEtaleRingModulePullback f (exchangeConstantRing V A)
            (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M) =
        (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A)).map (eV.hom.app M) ≫
            (ordinaryComparison d f n).hom.app M)
    (K : reductionDerivedCategory U (exchangeConstantRing U A)) :
    IsIso (((CategoryTheory.evaluation ℕᵒᵖ (proEtaleRingModules V (exchangeConstantRing V A))).obj
      (op n)).mapDerivedCategory.map (projection f FV FU DV DU τ K)) := by sorry

end Models
end AlgebraicGeometry.Scheme.ConstantPerfectProjection
