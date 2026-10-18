/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.EtaleLocallyClosedShriek
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.FiniteCoefficientReductionFlatModel
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-! # Étale recovery of the closed exceptional quotient comparison

Source: literature/blueprint/master/blueprint/sec-six-functors/
  sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md,
  proof paragraph 3 (blueprint: lem-coef-finite-etale-descent).

The module records the ordinary étale coefficient-change statement.  The auxiliary
exceptional functor is the right adjoint supplied by the closed-immersion ambient
adjunction at each positive finite coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- The ordinary étale exceptional functor at a positive finite coefficient stage.
Source: the closed-immersion right-adjoint construction in
`lem-exc-closed-ambient` (blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleExceptional
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    AlgebraicGeometry.Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X ⥤
      AlgebraicGeometry.Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Z := by
  letI : Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  exact (R(AlgebraicGeometry.Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) i)).rightAdjoint

/-- The adjunction whose right adjoint is `finiteEtaleExceptional`.
Source: `lem-exc-closed-ambient` (blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleExceptionalAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    R(AlgebraicGeometry.Etale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) i) ⊣
      finiteEtaleExceptional l E n hn i := by
  letI : Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  exact Adjunction.ofIsLeftAdjoint _

/-- The canonical reduction map between positive finite coefficient stages.
Source: the quotient map in `def-weil-l-adic-coefficient-extension`
(blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hmn : m ≤ n) :
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m) :=
  RingHom.ulift (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m)
    (Ideal.pow_le_pow_right hmn))

/-- Transport from the small étale to the small pro-étale derived category.
Source: `def-weil-pbc-site-comparison-morphism`
(blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleProComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n) (T : Scheme.{u}) :
    AlgebraicGeometry.Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T ⥤
      finiteClosedDerived T (Padic.coefficientExtensionRing l E n) := by
  letI : Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n _hn)
  exact (AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E n))) T).mapDerivedCategory

/-- The recorded transported exceptional functor in positive coefficient coordinates.
This only supplies the finite-ring instance to `finiteClosedExceptional`.
Source: blueprint finite coefficient descent, proof step 3
(blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleProExceptional
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    finiteClosedDerived X (Padic.coefficientExtensionRing l E n) ⥤
      finiteClosedDerived Z (Padic.coefficientExtensionRing l E n) := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact finiteClosedExceptional (Padic.coefficientExtensionRing l E n) i

/-- The canonical exceptional transport map. First identify the two ordinary etale
right adjoints using their counits and the canonical proper direct-image identification;
then apply the exceptional functor and comparison pullback to the derived comparison unit.
Its invertibility on the inputs in question is asserted in the theorem below, so this
construction needs no choice of an unspecified isomorphism.
Source: blueprint finite coefficient descent, proof steps 3 and 5
(blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleExceptionalComparisonMap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AlgebraicGeometry.Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X) :
    (finiteEtaleProComparison l E n hn Z).obj
        ((finiteEtaleExceptional l E n hn i).obj M) ⟶
      (finiteEtaleProExceptional l E n hn i).obj
        ((finiteEtaleProComparison l E n hn X).obj M) := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  letI := (Compactification.ofIsProper i).hasCompactification
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
  let G := AlgebraicGeometry.Etale.rightDerivedUpperShriek C i
  let e := Adjunction.rightAdjointUniq (finiteEtaleExceptionalAdjunction l E n hn i)
    ((AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction C i).ofNatIsoLeft
      (AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar C i))
  exact (finiteEtaleProComparison l E n hn Z).map
    (e.hom.app M ≫ G.map ((ProEtale.derivedComparisonAdjunction C X).unit.app M))

/-- The specified pro-etale closed-shriek map at the quotient A_n to A_m.
This only supplies the positive-stage finite-ring instances to `finiteClosedShriekMap`;
its data is exactly that recorded comparison, with its exceptional-counit normalization.
Source: blueprint finite coefficient descent, proof steps 5 and 6
(blueprint: lem-coef-finite-etale-descent). -/
noncomputable def finiteEtaleClosedShriekMap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≤ n) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : finiteClosedDerived X (Padic.coefficientExtensionRing l E n)) :
    (finiteClosedScalar (finiteEtaleReduction l E m n hmn) Z).obj
        ((finiteEtaleProExceptional l E n hn i).obj M) ⟶
      (finiteEtaleProExceptional l E m hm i).obj
        ((finiteClosedScalar (finiteEtaleReduction l E m n hmn) X).obj M) := by
  letI := Padic.finite_coefficientExtensionRing l E m hm
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact finiteClosedShriekMap (finiteEtaleReduction l E m n hmn) i M

/--
For the fixed finite-field datum, quotient coefficient map, separated finite-type schemes,
and a closed immersion, finite-Tor constructible étale complexes have exceptional inverse
images compatible with derived coefficient change.  The comparison is the unique
exceptional-counit transpose and is an isomorphism; the transported pro-étale map is the
corresponding finite closed-shriek comparison, and faithfulness of the site comparison
reflects equality of diagrams.

Source: literature/blueprint/master/blueprint/sec-six-functors/
  sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md,
  proof paragraph 3 (blueprint: lem-coef-finite-etale-descent).
Proof (the seven steps of the DAG node):
1. The schemes are Noetherian since they are finite type over a field. Apply the
closed case of lem-coef-etale-locally-closed-shriek at the identity quotient A_n to A_n;
its preservation clause puts N = G_A M in the finite-Tor constructible category.
2. Choose bounded flat constructible models for M and N in their Tor intervals.
Termwise tensor with B represents derived reduction, retains those intervals and has
flat B-terms. On strata these terms are constant finite B-modules. The constructible
Serre property gives constructible cohomology. Hence TM and TN are bounded constructible
with finite Tor intervals, without flatness of the quotient B over A.
3. Apply exceptional preservation at the identity B quotient to TM. Both requested
outputs are bounded below. Comparison preserves their finite Tor intervals. The
canonical tensor pullback identifies C_B T with T^p C_A. The comparison unit identifies
C_Z G_R with G_R^p C_X; uniqueness of right adjoints uses the proper direct-image
identification, so this identification preserves the exceptional counit.
4. The closed immersion is qcqs and finite type by its affine quotient charts.
Apply the canonical direct-image comparison delta. The square of delta, tensor
pullback, and ordinary coefficient change commutes: transpose both sides under
ordinary pullback/direct image; both become the coefficient extension of the same
ordinary counit. On flat representatives the tensor identification sends x tensor b
to the pullback of x tensor b. Injectivity of the Hom adjunction gives the square.
5. Under the transported exceptional Hom chain the counit is the preimage of the
identity. Thus epsilon^p = C(epsilon^e) delta^{-1}. This applies over A to M and over
B to TM because all Hom arguments above are bounded below.
6. Define b by the etale exceptional transpose T(epsilon_A) c^{-1}. Conjugate its
comparison pullback by the canonical tensor and exceptional identifications. Step 5
identifies its transported transpose, and step 4 rewrites it as
T^p(epsilon_A^p) (c^p)^{-1}. This is precisely the transpose defining
finiteClosedShriekMap. Injectivity of the relative exceptional Hom bijection gives
the displayed equality. Only bounded constructible etale-origin inputs are used.
7. The pro-etale closed-shriek coefficient theorem makes that map invertible.
Full faithfulness of C_Z on bounded-below objects lifts its inverse and reflects
both inverse equations, proving IsIso b. The same faithfulness tests equality of
any two paths in diagrams between bounded-below etale outputs.
-/
theorem finiteCoefficientEtaleDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≤ n)
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : AlgebraicGeometry.Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X.left)
    (hM : AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) X.left M) :
    AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) Z.left
      ((finiteEtaleExceptional l E n hn i.left).obj M) ∧
    AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E m))) X.left
      ((AlgebraicGeometry.Etale.scalarExtension (finiteEtaleReduction l E m n hmn) X.left).obj M) ∧
    AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E m))) Z.left
      ((finiteEtaleExceptional l E m hm i.left).obj
        ((AlgebraicGeometry.Etale.scalarExtension
          (finiteEtaleReduction l E m n hmn) X.left).obj M)) ∧
    AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E m))) Z.left
      ((AlgebraicGeometry.Etale.scalarExtension (finiteEtaleReduction l E m n hmn) Z.left).obj
        ((finiteEtaleExceptional l E n hn i.left).obj M)) ∧
    (∀ (K N : AlgebraicGeometry.Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m)) Z.left),
      DerivedCategory.TStructure.t.plus K → DerivedCategory.TStructure.t.plus N →
      ∀ f g : K ⟶ N,
        f = g ↔ (finiteEtaleProComparison l E m hm Z.left).map f =
          (finiteEtaleProComparison l E m hm Z.left).map g) ∧
    ∃ b :
      (AlgebraicGeometry.Etale.scalarExtension (finiteEtaleReduction l E m n hmn) Z.left).obj
        ((finiteEtaleExceptional l E n hn i.left).obj M) ⟶
      (finiteEtaleExceptional l E m hm i.left).obj
        ((AlgebraicGeometry.Etale.scalarExtension (finiteEtaleReduction l E m n hmn) X.left).obj M),
      IsIso b ∧
      IsIso (AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap
          (finiteEtaleReduction l E m n hmn) i.left
          ((finiteEtaleExceptional l E n hn i.left).obj M)) ∧
      ∃ cInv :
        (R(AlgebraicGeometry.Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E m))) i.left)).obj
          ((AlgebraicGeometry.Etale.scalarExtension
            (finiteEtaleReduction l E m n hmn) Z.left).obj
            ((finiteEtaleExceptional l E n hn i.left).obj M)) ⟶
        (AlgebraicGeometry.Etale.scalarExtension
          (finiteEtaleReduction l E m n hmn) X.left).obj
          ((R(AlgebraicGeometry.Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E n))) i.left)).obj
            ((finiteEtaleExceptional l E n hn i.left).obj M)),
        (AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap
            (finiteEtaleReduction l E m n hmn) i.left
            ((finiteEtaleExceptional l E n hn i.left).obj M)) ≫ cInv = 𝟙 _ ∧
        cInv ≫ (AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap
            (finiteEtaleReduction l E m n hmn) i.left
            ((finiteEtaleExceptional l E n hn i.left).obj M)) = 𝟙 _ ∧
        b = (finiteEtaleExceptionalAdjunction l E m hm i.left).homEquiv _ _
          (cInv ≫ (AlgebraicGeometry.Etale.scalarExtension
            (finiteEtaleReduction l E m n hmn) X.left).map
              ((finiteEtaleExceptionalAdjunction l E n hn i.left).counit.app M)) ∧
        (AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap
            (finiteEtaleReduction l E m n hmn) i.left
            ((finiteEtaleExceptional l E n hn i.left).obj M)) ≫
          (R(AlgebraicGeometry.Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E m))) i.left)).map b ≫
            (finiteEtaleExceptionalAdjunction l E m hm i.left).counit.app
              ((AlgebraicGeometry.Etale.scalarExtension
                (finiteEtaleReduction l E m n hmn) X.left).obj M) =
          (AlgebraicGeometry.Etale.scalarExtension
            (finiteEtaleReduction l E m n hmn) X.left).map
            ((finiteEtaleExceptionalAdjunction l E n hn i.left).counit.app M) ∧
      ∃ (eA : (finiteEtaleProComparison l E n hn Z.left).obj
            ((finiteEtaleExceptional l E n hn i.left).obj M) ≅
          (finiteEtaleProExceptional l E n hn i.left).obj
            ((finiteEtaleProComparison l E n hn X.left).obj M))
        (eB : (finiteEtaleProComparison l E m hm Z.left).obj
            ((finiteEtaleExceptional l E m hm i.left).obj
              ((AlgebraicGeometry.Etale.scalarExtension
                (finiteEtaleReduction l E m n hmn) X.left).obj M)) ≅
          (finiteEtaleProExceptional l E m hm i.left).obj
            ((finiteEtaleProComparison l E m hm X.left).obj
              ((AlgebraicGeometry.Etale.scalarExtension
                (finiteEtaleReduction l E m n hmn) X.left).obj M))),
        eA.hom = finiteEtaleExceptionalComparisonMap l E n hn i.left M ∧
        eB.hom = finiteEtaleExceptionalComparisonMap l E m hm i.left
          ((AlgebraicGeometry.Etale.scalarExtension
            (finiteEtaleReduction l E m n hmn) X.left).obj M) ∧
        (finiteEtaleProComparison l E m hm Z.left).map b ≫ eB.hom ≫
            (finiteEtaleProExceptional l E m hm i.left).map
              ((ProEtale.pbcComparisonReduction X.left
                (finiteEtaleReduction l E m n hmn)).inv.app M) =
          (ProEtale.pbcComparisonReduction Z.left
              (finiteEtaleReduction l E m n hmn)).inv.app
                ((finiteEtaleExceptional l E n hn i.left).obj M) ≫
            (finiteClosedScalar (finiteEtaleReduction l E m n hmn) Z.left).map eA.hom ≫
              finiteEtaleClosedShriekMap l E m n hm hn hmn i.left
                ((finiteEtaleProComparison l E n hn X.left).obj M)
    := by
  sorry

end WeilConjectures
