/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Homology.KFlatTotalTensorModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Paper.CompletedConstantAlgebraFlatQuotients
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor

/-! # Principal Koszul strict replacements of completed quotient towers

Source: Stacks Project, Tags 093M, 099L and 06YS; the explicit principal argument
in proof steps 1--8 (blueprint: lem-a1-principal-koszul-strict-replacement).
The index `n : ℕ` denotes exponent `n + 1`. Tensor products keep the order `P ⊗ Q`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.PrincipalKoszulStrictReplacement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The canonical size witness, without identifying the two input universes.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance siteSmall : EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u} _

/-- Canonical additive sheafification at the actual coefficient size.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance (priority := 4000) abSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

/-- The canonical locally bijective criterion at the actual coefficient size.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
instance (priority := 4000) abLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

/-- The existing completed coefficient module category.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev Modules := SheafOfModules.{max u (t + 1)}
  (completedIntegralCoefficientSheafUnrestricted l E W)

/-- The constant uniformizer, sent into the specified inverse limit.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def uniformizer :
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (integralConstantToCompletionOfUniverses l E W).hom.app U
      ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
            (ULift.up (Padic.coefficientExtensionUniformizer l E))))
    (by
      intro U V f
      let c := integralConstantToCompletionOfUniverses l E W
      let η := toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))
      let a := ULift.up (Padic.coefficientExtensionUniformizer l E)
      have hc := congrArg (fun h ↦ h (η.app U a)) (c.hom.naturality f)
      have hη := congrArg (fun h ↦ h a) (η.naturality f)
      change c.hom.app V ((integralConstantRingOfUniverses l E W).obj.map f
        (η.app U a)) = (completedIntegralCoefficientSheafUnrestricted l E W).obj.map f
          (c.hom.app U (η.app U a)) at hc
      change η.app V a = (integralConstantRingOfUniverses l E W).obj.map f
        (η.app U a) at hη
      exact hc.symm.trans (congrArg (c.hom.app V) hη.symm))

/-- The actual constant quotient module, restricted along the limit projection.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def residue (n : ℕ) : Modules l E W :=
  (SheafOfModules.restrictScalars
    (limit.π (integralCoefficientSheafSystem l E W) (op n))).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))

/-- The specified projection, as a linear map from the unit.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def projection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      residue l E W n :=
  (residue l E W n).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E W n).obj.obj U))
      (by
        intro U V f
        change (integralCoefficientSheaf l E W n).obj.map f 1 = 1
        exact map_one _))

/-- The existing two-term mapping-cone Koszul complex.
Source: Stacks 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev koszul (n : ℕ) : CochainComplex (Modules l E W) ℤ :=
  principalKoszul (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) n

/-- The existing multiplication endomorphism raised to exponent n+1.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
abbrev multiplication (n : ℕ) :=
  endoPow (globalSectionMultiplication (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W)) (n + 1)

/-- The actual projection kills the indicated uniformizer power.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: compose the constant-to-limit map with its nth projection. This is the constant
quotient homomorphism, which kills t^(n+1); multiplication then kills every section. -/
theorem multiplication_projection (n : ℕ) :
    multiplication l E W n ≫ projection l E W n = 0 := by
  sorry

/-- The canonical cokernel comparison, fixed by the actual projection.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def quotientComparison (n : ℕ) :
    principalQuotient (completedIntegralCommRingSheafUnrestricted l E W)
      (uniformizer l E W) n ⟶ residue l E W n :=
  cokernel.desc (multiplication l E W n) (projection l E W n) (multiplication_projection l E W n)

/-- The quotient augmentation is zero on the shifted summand and pi_n on degree zero.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def augmentation (n : ℕ) : koszul l E W n ⟶
    (CochainComplex.singleFunctor (Modules l E W) 0).obj (residue l E W n) :=
  principalAugmentation (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) n ≫
      (CochainComplex.singleFunctor (Modules l E W) 0).map (quotientComparison l E W n)

/-- Total tensor with P in the first variable, using the recorded direct-sum total.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def tensorWith (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (Modules l E W) ℤ ⥤ CochainComplex (Modules l E W) ℤ :=
  (SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
    (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.obj P

/-- The source strict tower, whose successive transition is id_P tensor (t,1).
Source: Stacks 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def sourceTower (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E W)
    (uniformizer l E W) ⋙ tensorWith l E W P

/-- The actual quotient map on the restricted quotient modules.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def residueStep (n : ℕ) : residue l E W (n + 1) ⟶ residue l E W n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (residue l E W (n + 1)).val.obj U)
        (Y := (residue l E W n).val.obj U)
        { toFun := (integralCoefficientSheafTransition l E W n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            let p (k : ℕ) : completedIntegralCoefficientSheafUnrestricted l E W ⟶
                integralCoefficientSheaf l E W k :=
              limit.π (integralCoefficientSheafSystem l E W) (op k)
            change (integralCoefficientSheaf l E W (n + 1)).obj.obj U at x
            change (integralCoefficientSheafTransition l E W n).hom.app U
              ((p (n + 1)).hom.app U r
                * x) =
              (p n).hom.app U r *
                (integralCoefficientSheafTransition l E W n).hom.app U x
            rw [map_mul]
            congr 1
            have h := limit.w (integralCoefficientSheafSystem l E W)
              (homOfLE n.le_succ).op
            simp only [integralCoefficientSheafSystem,
              Functor.ofOpSequence_map_homOfLE_succ] at h
            exact ConcreteCategory.congr_hom (congrArg (fun h ↦ h.hom.app U) h) r }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((integralCoefficientSheafTransition l E W n).hom.naturality f) x }

/-- The strict target tower uses actual quotient maps before any localization.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def targetTower (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  Functor.ofOpSequence (residueStep l E W) ⋙
    CochainComplex.singleFunctor (Modules l E W) 0 ⋙ tensorWith l E W P

/-- Strict augmentation compatibility with adjacent quotient maps.
Source: Stacks 093M, 0A0E (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: on degree zero the equality is pi_(n+1) followed by q = pi_n, the limit-cone
equation. In degree -1 both augmentations vanish. Tensor functoriality preserves it. -/
theorem augmentation_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    (sourceTower l E W P).map (homOfLE n.le_succ).op ≫
        (tensorWith l E W P).map (augmentation l E W n) =
      (tensorWith l E W P).map (augmentation l E W (n + 1)) ≫
        (targetTower l E W P).map (homOfLE n.le_succ).op := by
  sorry

/-- The required strict tower morphism, with components id_P tensor epsilon_n.
Source: Stacks 099L (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def comparison (P : CochainComplex (Modules l E W) ℤ) :
    sourceTower l E W P ⟶ targetTower l E W P :=
  NatTrans.ofOpSequence (fun n ↦ (tensorWith l E W P).map (augmentation l E W n))
    (augmentation_compatible l E W P)

/-- The coefficient datum and its explicit principal two-term free resolutions.
Source: Stacks 00PD, 0657, 099L (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: the coefficient DVR theorem gives a nonzero uniformizer generating the maximal
ideal. Principal ideals are finitely generated, so A is Noetherian. The finite-quotient
theorem gives every positive quotient finite. Since the extending absolute value of ell
is less than one, ell lies in (t), killing A/(t). Multiplication by any t^(n+1) is
injective in the domain A; its image is precisely the kernel of the quotient map.
The resulting two-term resolution has free rank-one terms and is bounded, proving
perfectness of every quotient. These are exactly the fields of AdicCoefficientDatum. -/
theorem coefficient_datum :
    ∃ d : AlgebraicGeometry.Scheme.AdicCoefficientDatum
        (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E} ∧
      ∀ n : ℕ,
        Function.Injective (fun a : Padic.coefficientExtensionIntegers l E ↦
          Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a) ∧
        Function.Exact (fun a : Padic.coefficientExtensionIntegers l E ↦
          Padic.coefficientExtensionUniformizer l E ^ (n + 1) * a)
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) ∧
        Function.Surjective
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  sorry

/-- Exactness through the specified completed projection, and the canonical quotient iso.
Source: Stacks 093M (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: apply the exact constant-module functor to the coefficient free resolution.
The completed-constant-algebra flat-quotient theorem preserves its exactness under
extension to R_W and identifies its last map with pi_n by b tensor a mapping to
pi_n(b)a. Thus its first map is monic, its last map epic and its middle homology zero.
The cokernel comparison defined from that very projection is consequently invertible. -/
theorem completed_exact (n : ℕ) :
    (ShortComplex.mk (multiplication l E W n) (projection l E W n)
      (multiplication_projection l E W n)).ShortExact ∧
      IsIso (quotientComparison l E W n) := by
  sorry

/-- Principal Koszul tensor levels are flat-term K-flat replacements of actual reductions.
Source: Stacks 093M, 06YQ, 06YP, 07A2, 099L
(blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: completed_exact identifies H^0 of Q with S via the actual projection and makes
H^-1 zero, so epsilon is a quasi-isomorphism. Its two unit terms are flat, and the
bounded-flat theorem makes Q K-flat. K-flat tensor invariance and the signed symmetry
give a quasi-isomorphism id_P tensor epsilon. The total-tensor model theorem makes
P tensor Q K-flat with flat terms, even for unbounded P. The target is precisely the
strict reduction tower on the K-flat representative P, with the actual quotient maps;
finite constant coefficients identify it with the adic datum's reduction tower. -/
theorem principal_koszul_strict_replacement
    (P : CochainComplex (Modules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) :
    ∀ n : ℕ, QuasiIso ((comparison l E W P).app (op n)) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E W)
        ((sourceTower l E W P).obj (op n)) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E W)
        (((sourceTower l E W P).obj (op n)).X i) := by
  sorry

/-- The strict source-tower map induced by f tensor identity.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def sourceTowerMap {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    sourceTower l E W P ⟶ sourceTower l E W P' :=
  Functor.whiskerLeft
    (principalKoszulTower (completedIntegralCommRingSheafUnrestricted l E W)
      (uniformizer l E W))
    ((SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.map f)

/-- The strict actual reduction-tower map induced by f tensor identity.
Source: Stacks 06YM (blueprint: lem-a1-principal-koszul-strict-replacement). -/
def targetTowerMap {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    targetTower l E W P ⟶ targetTower l E W P' :=
  Functor.whiskerLeft
    (Functor.ofOpSequence (residueStep l E W) ⋙
      CochainComplex.singleFunctor (Modules l E W) 0)
    ((SheafOfModules.KFlatTotalTensorModel.tensor.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W)).map₂CochainComplex.map f)

/-- Naturality in the representative as an equality of strict tower morphisms.
Source: Stacks 06YM, 099L (blueprint: lem-a1-principal-koszul-strict-replacement).
Proof: both composites on a homogeneous tensor p tensor q send it to
f(p) tensor epsilon(q). With a transition in place of epsilon both send it to
f(p) tensor tau(q). Balanced tensor functoriality and total direct sums extend
these formulas to equalities of chain maps. This works for every chain map, hence
in particular for chain maps between the flat-term K-flat representatives above. -/
theorem comparison_naturality
    {P P' : CochainComplex (Modules l E W) ℤ} (f : P ⟶ P') :
    sourceTowerMap l E W f ≫ comparison l E W P' =
      comparison l E W P ≫ targetTowerMap l E W f := by
  sorry

end WeilConjectures.PrincipalKoszulStrictReplacement
