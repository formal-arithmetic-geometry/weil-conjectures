/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.SiteClosedCounitTransport
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.Compactification.Affine
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Descent of the closed exceptional coefficient mate

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-descent).

The ordinary closed right adjoint is the compact-support right adjoint for the
identity-open compactification, with its adjunction transported through the canonical
proper forget-supports isomorphism. Thus the transported functor is exactly the
published finite exceptional functor. All scalar and site comparisons are the named
canonical maps, and the exceptional arrow is characterized by its counit equation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- The complete closed descent assertion at a specified ordinary etale input.
This only assembles the recorded functors and maps: the local names in the body are
abbreviations, and no comparison map is supplied as an arbitrary parameter. The
ordinary closed adjunction is normalized by the proper forget-supports isomorphism.
The two displayed scalar/site paths are actual B-linear morphisms. The final
existential first asserts the independent invertibility needed to take inverses,
then characterizes the ordinary arrow uniquely by its exceptional counit.

Source: blueprint finite-dualizing proof, paragraph 3, expanded closed descent and
normalized coefficient square (blueprint: lem-coef-dualizing-closed-descent). -/
def CoefficientClosedDescent
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) P) : Prop :=
  letI : HasCompactification i := (Compactification.ofIsProper i).hasCompactification
  let RA := ULift.{u + 1, u} A
  let RB := ULift.{u + 1, u} B
  let SA := fun W : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} RA) W).mapDerivedCategory
  let SB := fun W : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} RB) W).mapDerivedCategory
  let IA := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} RA) i
  let IB := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} RB) i
  let adjA := (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} RA) i
    ).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} RA) i)
  let adjB := (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} RB) i
    ).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} RB) i)
  let Te := fun W : Scheme.{u} ↦ ProEtale.pbcFixedScalarExtension W.smallEtaleTopology φ
  let Tp := finiteClosedScalar φ
  let N := IA.obj M
  let MB := (Te P).obj M
  let NB := (Te Y).obj N
  let H := (SA P).obj M
  let Q := (SA Y).obj N
  let K := (finiteClosedExceptional A i).obj H
  let αA := (SA Y).map
    (IA.map ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} RA) P).unit.app M))
  let αB := (SB Y).map
    (IB.map ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} RB) P).unit.app MB))
  let t := fun W : Scheme.{u} ↦ (ProEtale.pbcComparisonReduction W φ).symm
  let κ₁ := (t Y).hom.app N ≫ (Tp Y).map αA
  let κ₂ := αB ≫ (finiteClosedExceptional B i).map ((t P).hom.app M)
  let ce := Etale.finiteCoefficientDirectImageMap φ i N
  let cpQ := ProEtale.finiteCoefficientChangeDirectImageMap φ i Q
  let cpK := ProEtale.finiteCoefficientChangeDirectImageMap φ i K
  let δA := (ProEtale.directImageComparisonAmbient RA i).app N
  let δB := (ProEtale.directImageComparisonAmbient RB i).app NB
  DerivedCategory.TStructure.t.plus M ∧
  DerivedCategory.TStructure.t.plus N ∧
  DerivedCategory.TStructure.t.plus MB ∧
  DerivedCategory.TStructure.t.plus NB ∧
  DerivedCategory.TStructure.t.plus (IB.obj MB) ∧
  DerivedCategory.TStructure.t.plus
    ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} RB) i).obj NB) ∧
  IsIso αA ∧ IsIso αB ∧ IsIso δA ∧ IsIso δB ∧
  IsIso cpQ ∧ IsIso cpK ∧ IsIso κ₁ ∧
  ((t P).hom.app ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} RA) i).obj N) ≫
      (Tp P).map δA ≫ cpQ =
    (SB P).map ce ≫ δB ≫
      (finiteClosedPush B i).map ((t Y).hom.app N)) ∧
  ∃ hce : IsIso ce, ∃ hκ₂ : IsIso κ₂,
    ∃ b : NB ⟶ IB.obj MB,
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} RB) i).map b ≫
          adjB.counit.app MB =
        @inv _ _ _ _ ce hce ≫ (Te P).map (adjA.counit.app M) ∧
      (∀ b' : NB ⟶ IB.obj MB,
        (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} RB) i).map b' ≫
            adjB.counit.app MB =
          @inv _ _ _ _ ce hce ≫ (Te P).map (adjA.counit.app M) → b' = b) ∧
      IsIso b ∧
      (SB Y).map b = κ₁ ≫ finiteClosedShriekMap φ i H ≫ @inv _ _ _ _ κ₂ hκ₂

/-- The counit-defined closed exceptional coefficient mate at the affine-space
ordinary dualizing input is invertible and has exactly the specified pro-etale image.
Positive coefficient levels are indexed by m+1 and n+1, with m ≤ n.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-descent).

Proof:
1. lem-coef-dualizing-closed-site gives finite-Tor constructibility of M, N, MB
and IB(MB). Choose a Tor interval for N and the etale flat model of lem-sf-flat-model.
Tensoring that bounded flat complex with B proves NB bounded below, independently
of any comparison arrow. Closed direct image is exact by lem-coef-dualizing-closed-chart,
so i_* NB is bounded below too.
2. Apply lem-sfb-etale-proetale-scalar-mate to i and N. Its beta is the canonical
counit mate delta of lem-weil-pbc-comparison-direct-image-canonical-mate; its scalar
comparison is t inverse. Rearranging its equality gives the displayed normalized square.
3. B is cyclic over A. lem-coef-finite-direct-image makes ce and cpQ invertible.
Naturality along alphaA, an isomorphism, then makes cpK invertible.
4. lem-coef-finite-closed-shriek gives the counit-defined pro-etale isomorphism
at H = SA(M). Its endpoints are identified by kappa1 and kappa2, using precisely
J = S I U of def-weil-exceptional-inverse-image; no unbounded pro-etale adjoint is used.
5. thm-weil-pbc-site-comparison lifts the conjugated isomorphism and its inverse
through full faithfulness on the two bounded-below endpoints NB and IB(MB).
6. Use lem-coef-site-closed-counit-transport over A and B, naturality of deltaB
at the lifted arrow, and naturality of the pro-etale counit at tP(M). Substitute
cpK inverse times i_*(Tp alphaA) = Tp(i_* alphaA) times cpQ inverse. The A-counit
transport and the normalized coefficient square cancel deltaA and cpQ. Finally
naturality of tP at the A-counit gives S(eB i_* b) = S(Te(eA) ce inverse).
7. Faithfulness only on Hom(i_* NB, MB), whose endpoints were bounded below in
step 1, descends that equation. The ordinary closed adjunction gives uniqueness
of b from this counit equation, proving it is the named ordinary comparison.
8. If Y is empty, its module derived category is zero and this is the unique
isomorphism. The same formulas include m=n and r=0; no positivity of r is used. -/
theorem coefficientDualizingClosedDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))
    [IsClosedImmersion i]
    (_hi : i ≫ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k) = aY) :
    CoefficientClosedDescent
      (RingHom.ulift.{u + 1, u + 1}
        (Ideal.Quotient.factor
          (S := Padic.coefficientExtensionIdeal l E (n + 1))
          (T := Padic.coefficientExtensionIdeal l E (m + 1))
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)))) i
      (Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E n)))
        (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k))) := by
  sorry

end WeilConjectures
