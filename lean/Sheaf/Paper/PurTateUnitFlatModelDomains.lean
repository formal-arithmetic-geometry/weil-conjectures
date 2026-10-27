module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
public import Sheaf.Paper.TwistPreservesFiniteness
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Sheaf.Paper.IntegralCtfTriangulated

/-! # K-flat Tate-unit models and uniform finite-reduction domains

Source: latest blueprint, sec-smooth-purity/sk-thm-purity-transport,
`sk-thm-purity-transport.proof.md`, Step 3; agent auxiliary, Old Steps 1–3:
actual K-flat unit/line models and all uniform reduction Tor domains
(the node source place); Stacks Tags 06YQ and 06YY
(blueprint: lem-pur-tate-unit-flat-model-domains).

The finite indices below only enumerate the three displayed models and objects.
The coefficient rings, lines, scalar functors and reductions are the published ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
  (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]
  (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]

/-- The three module models: R, J and R tensor J, in this order.
The residue inverse is inherited from the structure map, not assumed.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatModelModule (m : ℕ) (i : Fin 3) : scalarReductionSource P.coefficients.l E S :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  match i with
  | 0 => SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted P.coefficients.l E S)
  | 1 => integralTwistLine P.coefficients.l E S (m : ℤ)
  | 2 => (integralSheafTwist P.coefficients.l E S (m : ℤ)).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted P.coefficients.l E S))

/-- Each displayed degree-zero complex, with any integer shift.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
abbrev tateFlatModel (m : ℕ) (i : Fin 3) (s : ℤ) :=
  ((HomologicalComplex.single (scalarReductionSource P.coefficients.l E S) (.up ℤ) 0).obj
    (P.tateFlatModelModule E S m i))⟦s⟧

/-- The actual objects U, V = U(m), W = V[n], in this order.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatDomainObject (m : ℕ) (n : ℤ) (i : Fin 3) :
    DerivedCategory (scalarReductionSource P.coefficients.l E S) :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  match i with
  | 0 => integralConstantCoefficientObject P.coefficients.l E S
  | 1 => (sfIntegralTwistingFunctor P.coefficients.l E S (m : ℤ)).obj
      (integralConstantCoefficientObject P.coefficients.l E S)
  | 2 => ((sfIntegralTwistingFunctor P.coefficients.l E S (m : ℤ)).obj
      (integralConstantCoefficientObject P.coefficients.l E S))⟦n⟧

/-- The finite modules A_j, A_j(m), A_j(m), with j encoded as j+1.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatReductionModule (m j : ℕ) (i : Fin 3) :
    scalarReductionTarget P.coefficients.l E S j :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  if i = 0 then SheafOfModules.unit (integralCoefficientSheaf P.coefficients.l E S j)
  else finiteCoefficientTwist P.coefficients.l E S j (m : ℤ)

/-- The shifts 0,0,n for U,V,W. Their Tor degrees are their negatives.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatReductionShift (n : ℤ) (i : Fin 3) : ℤ := if i = 2 then n else 0

/-- The standard exact-functor comparison identifying U(m) with (R tensor J)[0].
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatTwistModelIso (m : ℕ) :
    P.tateFlatDomainObject E S m 0 1 ≅
      (DerivedCategory.singleFunctor _ 0).obj (P.tateFlatModelModule E S m 2) :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  ((integralSheafTwist P.coefficients.l E S (m : ℤ)).mapDerivedCategorySingleFunctor 0).app
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted P.coefficients.l E S))

/-- The actual quotient-derived line map: transpose the uniquely root/power/evaluation-
normalized semilinear map through the published derived tensor/restriction adjunction.
The unique witness in twist-preserves fixes the map; no arbitrary line isomorphism is chosen.
Source: purity transport Step 3; twist-preserves, finite reduction clause
(blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatLineReductionMap (m j : ℕ) :
    (scalarReductionDerivedExtension P.coefficients.l E S j).obj
        ((DerivedCategory.singleFunctor _ 0).obj (P.tateFlatModelModule E S m 1)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (P.tateFlatReductionModule E S m j 1) :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  let c := (((twist_preserves_finiteness P.coefficients.l E S
    (AlgebraicClosure (Padic P.coefficients.l)) (m : ℤ)).2.2.1 j).exists.choose) (m : ℤ)
  ((derivedScalarExtensionRestrictionAdjunction P.coefficients.l E S j).choose.homEquiv
    _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map c ≫
      ((scalarReductionRestriction P.coefficients.l E S j).mapDerivedCategorySingleFunctor
        0).inv.app (finiteCoefficientTwist P.coefficients.l E S j (m : ℤ)))

/-- The canonical reduction of V, using the exact tensor comparison, coefficient
multiplication mu, and the actual quotient-derived line map.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatTwistedReductionMap (m j : ℕ)
    (μ : P.tateFlatModelModule E S m 2 ≅ P.tateFlatModelModule E S m 1) :
    (scalarReductionDerivedExtension P.coefficients.l E S j).obj
        (P.tateFlatDomainObject E S m 0 1) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (P.tateFlatReductionModule E S m j 1) :=
  (scalarReductionDerivedExtension P.coefficients.l E S j).map
      ((P.tateFlatTwistModelIso E S m).hom ≫ (DerivedCategory.singleFunctor _ 0).map μ.hom) ≫
    P.tateFlatLineReductionMap E S m j

/-- The expected reductions A_j[0], A_j(m)[0], A_j(m)[n].
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatReductionObject (m j : ℕ) (n : ℤ) (i : Fin 3) :
    DerivedCategory (scalarReductionTarget P.coefficients.l E S j) :=
  match i with
  | 0 => (DerivedCategory.singleFunctor _ 0).obj (P.tateFlatReductionModule E S m j 0)
  | 1 => (DerivedCategory.singleFunctor _ 0).obj (P.tateFlatReductionModule E S m j 1)
  | 2 => ((DerivedCategory.singleFunctor _ 0).obj
      (P.tateFlatReductionModule E S m j 1))⟦n⟧

/-- The specified derived reduction maps for U,V,W. For W the shift comparison is
that of the same published universal derived-change-of-rings witness.
Source: purity transport Step 3; Stacks 06YY
(blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatReductionMap (m j : ℕ) (n : ℤ)
    (μ : P.tateFlatModelModule E S m 2 ≅ P.tateFlatModelModule E S m 1) (i : Fin 3) :
    (scalarReductionDerivedExtension P.coefficients.l E S j).obj
        (P.tateFlatDomainObject E S m n i) ⟶ P.tateFlatReductionObject E S m j n i :=
  match i with
  | 0 => constantCoefficientReductionMap P.coefficients.l E S j
  | 1 => P.tateFlatTwistedReductionMap E S m j μ
  | 2 =>
    let h := (scalarReductionDerivedExistence P.coefficients.l E S j).choose_spec.choose_spec
    let cs := h.2.1.choose
    (Functor.commShiftIso (scalarReductionDerivedExtension P.coefficients.l E S j)
      (self := cs) n).hom.app (P.tateFlatDomainObject E S m 0 1) ≫
      (shiftFunctor _ n).map (P.tateFlatTwistedReductionMap E S m j μ)

/-- The expected tensor with a degree-zero test module: M, M tensor A_j(m),
then the latter shifted by n. The shift is applied in the derived category.
Source: purity transport Step 3 (blueprint: lem-pur-tate-unit-flat-model-domains). -/
def tateFlatTestTensor (m j : ℕ) (n : ℤ) (i : Fin 3)
    (M : scalarReductionTarget P.coefficients.l E S j) :
    DerivedCategory (scalarReductionTarget P.coefficients.l E S j) :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (if i = 0 then M else
      (SheafOfModules.siteSheafTensorRight
        (A := integralCoefficientCommRingSheaf P.coefficients.l E S j)
        (P.tateFlatReductionModule E S m j i)).obj M))⟦tateFlatReductionShift n i⟧

variable [hft : LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
  [hqc : QuasiCompact (S ↘ Spec (.of P.field.k))]
  [hsep : IsSeparated (S ↘ Spec (.of P.field.k))]

include hft hqc hsep in
/-- The actual flat-term K-flat models, completed comparison, reductions and uniform
containing Tor intervals for U, V = U(m), W = V[n]. Level j denotes exponent j+1.
Source: purity transport Step 3; Stacks 06YQ, 06YY; Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pur-tate-unit-flat-model-domains).

Proof:
1. Twist preservation makes J a locally free rank-one module. R is free of rank one,
   and multiplication R tensor J -> J, inverse z -> 1 tensor z, identifies the third
   model with J. Locally-free-derived-scalars gives flatness. The one-term complexes
   and their shifts are bounded above with flat terms; bounded-above-flat-kflat-site
   gives K-flatness. Derived-change-of-rings computes extension using their identity
   resolutions, with the specified universal counits. Exact tensor identifies V with
   J[0] and W with J[0][n].
2. Constant-coefficient-objects-constructible identifies the actual reduction of U
   by the transpose of the coefficient projection. For J use the K-flat counit for
   that same projection. The ordinary line comparison is uniquely fixed by the
   root-of-unity, unit, tensor-power and evaluation normalization in twist-preserves.
   Reduction commutes with shifts, giving the displayed finite lines in degrees
   0, 0 and -n. The identifications use these canonical comparisons.
3. The finite coefficient ring and its finite Tate line are locally free of rank one.
   Locally-free-derived-scalars and bounded-above-flat-kflat-site give their flat
   K-flat identity models. Tensor with any degree-zero module M then has just M,
   M tensor A_j(m), or its n-shift, with zero differentials. Multiplication identifies
   the first tensor with M; symmetry gives the displayed order in the other two.
   Hence cohomology vanishes outside [0,0], [0,0], [-n,-n], uniformly in j.
4. The unit is constructible and derived complete by constant-coefficient-objects-
   constructible. Twist-preserves gives these properties for V. Step 3 gives the
   uniform integral finite-Tor bounds. Integral-ctf-triangulated gives shift closure
   for W. These remain containing intervals for an empty scheme or zero M.
5. The models and all their shifts are complete. Finite-free-completed-scalar-
   comparison makes the specified natural chi invertible on them, identifying the
   ordinary K-flat computation with the strict quotient tower. Its representative
   equation gives the displayed normalization; for H=L it is multiplication followed
   by the independently constructed completeness unit. No inclusion is assumed strict.
-/
theorem tateUnitFlatModelDomains (m : ℕ) (n : ℤ) :
    ∃ μ : P.tateFlatModelModule E S m 2 ≅ P.tateFlatModelModule E S m 1,
    (∀ μ' : P.tateFlatModelModule E S m 2 ≅ P.tateFlatModelModule E S m 1,
      (∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted P.coefficients.l E S).obj.obj U)
      (z : (P.tateFlatModelModule E S m 1).val.obj U),
      μ'.hom.val.app U (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted P.coefficients.l E S)
        (P.tateFlatModelModule E S m 0) (P.tateFlatModelModule E S m 1) U a z) = a • z) ↔
        μ' = μ) ∧
    (∀ (i : Fin 3) (s : ℤ),
      ∃ hP : integralOperationsGoodComplex P.coefficients.l E S (P.tateFlatModel E S m i s),
      IsDerivedCompleteUnrestricted P.coefficients.l E S
        (DerivedCategory.Q.obj (P.tateFlatModel E S m i s)) ∧
      ((completedScalarComparison P.coefficients.l E E
          (AlgHom.id (Padic P.coefficients.l) E) S).app
        (DerivedCategory.Q.obj (P.tateFlatModel E S m i s)) ≫
          (integralScalarExtensionComparisonOfUniverses P.coefficients.l E E
            (AlgHom.id (Padic P.coefficients.l) E) S).hom.app
              ⟨P.tateFlatModel E S m i s, hP⟩ =
        completedScalarCounit P.coefficients.l E E (AlgHom.id (Padic P.coefficients.l) E) S
          (P.tateFlatModel E S m i s) ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication
            P.coefficients.l E S).hom.app (P.tateFlatModel E S m i s)) ≫
          DerivedCategory.Q.map ((completedScalarIdentityUnit P.coefficients.l E S).app
            (P.tateFlatModel E S m i s))) ∧
      ∀ (H : Type u) [Field H] [Algebra (Padic P.coefficients.l) H]
        [FiniteDimensional (Padic P.coefficients.l) H]
        (ι : E →ₐ[Padic P.coefficients.l] H),
        IsIso (completedScalarCounit P.coefficients.l E H ι S
          (P.tateFlatModel E S m i s)) ∧
        IsIso ((completedScalarComparison P.coefficients.l E H ι S).app
          (DerivedCategory.Q.obj (P.tateFlatModel E S m i s))) ∧
        (completedScalarComparison P.coefficients.l E H ι S).app
            (DerivedCategory.Q.obj (P.tateFlatModel E S m i s)) ≫
            (integralScalarExtensionComparisonOfUniverses P.coefficients.l E H ι S).hom.app
              ⟨P.tateFlatModel E S m i s, hP⟩ =
          completedScalarCounit P.coefficients.l E H ι S (P.tateFlatModel E S m i s) ≫
            DerivedCategory.Q.map ((completedScalarChainComparison
              P.coefficients.l E H ι S).app (P.tateFlatModel E S m i s))) ∧
    (∀ i : Fin 3,
      finiteTorConstructibleIntegral P.coefficients.l E S
        (P.tateFlatDomainObject E S m n i) ∧
      ∀ j : ℕ,
        IsIso (P.tateFlatReductionMap E S m j n μ i) ∧
        (∀ M : scalarReductionTarget P.coefficients.l E S j,
          Nonempty ((finiteIntrinsicDerivedTensor P.coefficients.l E S j).obj
              ((scalarReductionDerivedExtension P.coefficients.l E S j).obj
                (P.tateFlatDomainObject E S m n i),
                (DerivedCategory.singleFunctor _ 0).obj M) ≅
            P.tateFlatTestTensor E S m j n i M)) ∧
        HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing P.coefficients.l E (j + 1))
          ((scalarReductionDerivedExtension P.coefficients.l E S j).obj
            (P.tateFlatDomainObject E S m n i))
          (-tateFlatReductionShift n i) (-tateFlatReductionShift n i)) ∧
    (∀ (i : Fin 3) (s : ℤ) (j : ℕ),
      IsIso ((scalarReductionCounit P.coefficients.l E S j).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (P.tateFlatModel E S m i s)))) := by
  sorry

end PurityFiniteSetting
end WeilConjectures
