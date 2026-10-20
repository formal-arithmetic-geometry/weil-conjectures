/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Paper.PurityFrameKummer
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.Paper.SupportedCup
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.ExtExactFunctorCocycle
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Pullback and symmetry of supported Kummer cup products

Source: Stacks Project, Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
main-20261015, lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

The Boolean site parameter is false for the small etale site and true for the
small pro-etale site. All constructions use the published sites, coefficients,
Kummer classes, exact inverse images and derived tensors.

## Main definitions and statement

* `functorialCupPullback`: the canonically normalized supported pullback.
* `functorialCup`: the prescribed tensor-morphism cup product on either site.
* `FunctorialCupAlgebraLaws`, `FunctorialCupLocalizationLaws`, and
  `FunctorialCupComparisonLaws`: the clauses of the statement.
* `supportedCupFunctoriality`: all these clauses for both sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The two existing sheaf categories. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  match pro with
  | false => Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  | true => Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)

/-- The existing category structure, by cases on the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The existing abelian structure. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The existing small localization. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance

/-- The existing derived category, with its localization shared explicitly.
Source: supported tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupDerived (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory (P.functorialCupSheaves pro X) _ _ (P.functorialCupHasDerived pro X)

/-- The existing finite constant module. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstant (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X :=
  match pro with
  | false => P.constantEtale X
  | true => P.constant X

/-- The published comparison inverse image, with its actual exact structure.
Source: Stacks 099R (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupComparisonFunctor (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.functorialCupSheaves false X ⥤ P.functorialCupSheaves true X :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X

/-- Additivity of the same exact site comparison, with selected-site endpoints.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_additive (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : (P.functorialCupComparisonFunctor X).Additive :=
  inferInstanceAs ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).Additive)

/-- Left exactness of the same canonical comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_limits (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : PreservesFiniteLimits (P.functorialCupComparisonFunctor X) :=
  inferInstanceAs (PreservesFiniteLimits
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))

/-- Right exactness of the same canonical comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_colimits (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : PreservesFiniteColimits (P.functorialCupComparisonFunctor X) :=
  inferInstanceAs (PreservesFiniteColimits
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))

/-- The existing strong monoidal structure of the canonical site comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_monoidal (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : (P.functorialCupComparisonFunctor X).Monoidal :=
  inferInstanceAs ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).Monoidal)

/-- The signed finite Tate sheaf at the actual annihilator ell^n. Source: the
arbitrary-index Kummer prescription in def-pur-frame-class
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwist (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (r : ℤ) : P.functorialCupSheaves pro X :=
  match pro with
  | false => Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r
  | true => (P.functorialCupComparisonFunctor X).obj
      (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
        P.diagonalExponent_annihilates r)

/-- The existing degree-zero embedding. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0

/-- The actual underived direct image of constants from the closed support.
Source: def-pur-supported-cup, supported-Hom model
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.functorialCupSheaves pro X :=
  match pro with
  | false => (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale C)
  | true => (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)

/-- Restriction of local constants, exactly the coefficient map of the supported cup.
Source: def-pur-supported-cup and the etale coefficient lemma
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupConstant pro X ⟶ P.functorialCupSource pro i :=
  match pro with
  | false => Etale.closedConstantSectionMap P.Coefficient i
  | true => ProEtale.cupCoefficientRestriction P i

/-- Supported cohomology in the published Hom model, for arbitrary integer degrees.
Source: lem-pur-supported-hom and lem-amb-closed-support-hom
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- The actual exact inverse image of fixed-scalar modules. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupInverseImage (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    P.functorialCupSheaves pro X ⥤ P.functorialCupSheaves pro Y :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v
  | true => ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v

/-- Additivity of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_additive (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) : (P.functorialCupInverseImage pro v).Additive := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance

/-- Left exactness of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_limits (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    PreservesFiniteLimits (P.functorialCupInverseImage pro v) := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance

/-- Right exactness of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_colimits (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    PreservesFiniteColimits (P.functorialCupInverseImage pro v) := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance


/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupGrothendieck (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published functorial flat resolutions, selected by the site.
Source: K-flat tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance

/-- The existing derived monoidal structure. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupDerivedMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : MonoidalCategory (P.FunctorialCupDerived pro X) := inferInstance

/-- The coefficient multiplication fixed by restriction and local scalar multiplication.
Source: def-pur-supported-cup and its etale analogue
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupMultiplication (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    P.functorialCupSource pro i ⊗ P.functorialCupSource pro j ⟶
      P.functorialCupSource pro (ProEtale.cupIntersection i j) :=
  match pro with
  | false => Etale.closedConstantTensorMap P.Coefficient i j
  | true => ProEtale.cupCoefficientMap P i j

/-- The signed product family together with the equations that uniquely normalize it.
All data are projected from the published signed-twist theorem, with the unit,
positive-power, evaluation, associativity and symmetry equations retained.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) where
  product : ∀ (X : Scheme.{u}), IsUnit (m : Γ(X, ⊤)) → ∀ r s : ℤ,
    Scheme.finiteEtaleTateSheaf A m X hA r ⊗ Scheme.finiteEtaleTateSheaf A m X hA s ≅
      Scheme.finiteEtaleTateSheaf A m X hA (r + s)
  left_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX 0 r = λ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (zero_add r).symm)
  right_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX r 0 = ρ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_zero r).symm)
  positive : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    product X hX (.ofNat (n + 1)) 1 = Iso.refl _
  associativity : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s t : ℤ),
    (product X hX r s).hom ▷ Scheme.finiteEtaleTateSheaf A m X hA t ≫
        (product X hX (r + s) t).hom =
      (α_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)
        (Scheme.finiteEtaleTateSheaf A m X hA t)).hom ≫
      Scheme.finiteEtaleTateSheaf A m X hA r ◁ (product X hX s t).hom ≫
        (product X hX r (s + t)).hom ≫
          eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_assoc r s t).symm)
  symmetry : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ),
    (β_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)).hom ≫
        (product X hX s r).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_comm s r)) =
      (product X hX r s).hom
  evaluation : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    (product X hX (.ofNat (n + 1)) (.negSucc n)).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA)
          (add_neg_cancel (Int.ofNat (n + 1)))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A m X hA (.ofNat (n + 1)))).app
        (Scheme.finiteEtaleTateSheaf A m X hA 0)

/-- Extract one coherent normalized family, retaining its characterizing equations.
Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) : FunctorialCupTwistProducts A m hA :=
  Classical.choice ((Scheme.etaleFiniteTwistPullback A m hm hA).elim fun _ hr ↦
    hr.elim fun _ hc ↦ hc.elim fun p hp ↦
      ⟨{ product := p
         left_unit := hp.2.2.2.2.2.2.2.2.1
         right_unit := hp.2.2.2.2.2.2.2.2.2.1
         positive := hp.2.2.2.2.2.2.2.2.2.2.1
         associativity := hp.2.2.2.2.2.2.2.2.2.2.2.1
         symmetry := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
         evaluation := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 }⟩)

/-- The canonical signed product, projected from its normalized family.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProductGeneral (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ) :=
  (functorialCupTwistProducts A m hm hA).product X hX r s

/-- Normalized etale twist multiplication from the signed-root prescription.
This selects the witness together with its generator, evaluation and tensor
normalizations, never an uncharacterized isomorphism. Source: Stacks 03PK and 07A4,
lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :=
  functorialCupTwistProductGeneral P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit a) r s

/-- The same normalized twist multiplication, transported through the canonical
strong monoidal site comparison on the pro-etale site. Source: Stacks 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProduct (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :
    P.functorialCupTwist pro X r ⊗ P.functorialCupTwist pro X s ≅
      P.functorialCupTwist pro X (r + s) :=
  match pro with
  | false => P.functorialCupEtaleTwistProduct X a r s
  | true => (asIso (Functor.OplaxMonoidal.δ
      (P.functorialCupComparisonFunctor X)
        (P.functorialCupTwist false X r) (P.functorialCupTwist false X s))).symm ≪≫
      (P.functorialCupComparisonFunctor X).mapIso
        (P.functorialCupEtaleTwistProduct X a r s)

/-- Flat supported coefficients make the canonical degree-zero tensor comparison
invertible. Source: def-pur-supported-cup and lem-pur-etale-closed-constant-tensor
(blueprint: lem-pur-supported-cup-functoriality).
Proof: on the etale site geometric stalks are A or zero and multiplication is the
identity on the common support. On the pro-etale site use the quotient/idempotent
calculation in def-pur-supported-cup. In both cases the flat degree-zero sheaves
are their own K-flat models, so the canonical localization comparison is invertible. -/
theorem functorialCupCoefficient_isIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j)) := by
  sorry

/-- The prescribed tensor-morphism supported product followed by multiplication
of the twist lines. For pro=true its first composite is the published supportedCup;
for pro=false it is its etale analogue, with exactly the same shift sign.
Source: def-pur-supported-cup, tensor-morphism formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCup (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s) :
    P.FunctorialCupH pro (ProEtale.cupIntersection i j) (a + b) (r + s) :=
  ProEtale.cupComposite (hM := P.functorialCupDerivedMonoidal pro X)
    (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j))
    (P.functorialCupCoefficient_isIso pro i j) a b α β ≫
      (ProEtale.cupSingleTensorMap (hD := P.functorialCupHasDerived pro X)
        (hDM := P.functorialCupDerivedMonoidal pro X)
          (P.functorialCupTwist pro X r) (P.functorialCupTwist pro X s) ≫
        (P.functorialCupSingle pro X).map (P.functorialCupTwistProduct pro X aX r s).hom)⟦a+b⟧'


/-- Canonical inverse image of the coefficient unit. Source: constant-sheaf adjunction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstantPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupConstant pro X) ≅
      P.functorialCupConstant pro Y :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v).app
      (ModuleCat.of P.Coefficient P.Coefficient)
  | true => P.frameConstantPullback v

/-- The etale part of normalized signed-twist inverse image.
Source: Stacks 03Q1, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage false v).obj (P.functorialCupTwist false X r) ≅
      P.functorialCupTwist false Y r :=
  Etale.p1DecompositionSheafPullback P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates v (P.diagonalExponent_isUnit aX) r

/-- The same root-normalized inverse image on either site. Pro-etale inverse image
uses the canonical comparison mate. Source: Stacks 03Q1, 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupTwist pro X r) ≅
      P.functorialCupTwist pro Y r :=
  match pro with
  | false => P.functorialCupEtaleTwistPullback v aX r
  | true => (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) v).app (P.functorialCupTwist false X r) ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapIso
        (P.functorialCupEtaleTwistPullback v aX r)

/-- Closed constant exchange is uniquely fixed by restriction of the unit.
Source: Stacks 03Q1 and 099V; supported functoriality, proof Steps 2 and 6
(blueprint: lem-pur-supported-cup-functoriality).
Proof: etale geometric stalks give A on the inverse-image closed subset and zero
elsewhere, so the section-normalized adjoint is invertible. For pro-etale objects
Y over X identify comparison inverse-image sections with etale sections on Y.
The same etale calculation and degree-zero comparison identify the closed source,
with identical local constants and restriction. This yields the asserted map on
both sites. Restriction from the constant unit is epic, so its displayed equation
makes the map unique. Nonreduced and empty closed supports require no modification. -/
theorem functorialCupExchange_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage pro v).obj (P.functorialCupSource pro i) ≅
        P.functorialCupSource pro j,
      (P.functorialCupInverseImage pro v).map (P.functorialCupRestriction pro i) ≫ b.hom =
        (P.functorialCupConstantPullback pro v).hom ≫ P.functorialCupRestriction pro j := by
  sorry

/-- The uniquely normalized ordinary coefficient exchange; no purity exchange is used.
Source: Stacks 03Q1, supported functoriality formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExchange (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :=
  (P.functorialCupExchange_existsUnique pro i j v g sq).choose

/-- Exact inverse image on derived Hom, precomposed by closed coefficient exchange
and followed by the normalized twist identification and canonical shift comparison.
This is the formula tau[a] v inverse(alpha) b inverse of proof Step 4.
Source: Stacks 0G78 and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro j a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupExchange pro i j v g sq).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

/-- Change of closed support over a fixed scheme, uniquely determined on local constants.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the map D to C over X restricts each locally constant section on C to D.
The sheaf map is A-linear and carries the restricted unit to the restricted unit.
The constant restriction onto the closed direct image is epic, proving uniqueness. -/
theorem functorialCupSupportMap_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (_h : g ≫ i = j) :
    ∃! b : P.functorialCupSource pro i ⟶ P.functorialCupSource pro j,
      P.functorialCupRestriction pro i ≫ b = P.functorialCupRestriction pro j := by
  sorry

/-- The actual restriction on closed constant sheaves, fixed by its epic unit map.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSupportMap (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j) :=
  (P.functorialCupSupportMap_existsUnique pro i j g h).choose

/-- Precomposition with the canonical closed support map. Source: supported
functoriality, symmetry and associativity clauses
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupChangeSupport (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j)
    (a r : ℤ) (α : P.FunctorialCupH pro j a r) : P.FunctorialCupH pro i a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupSupportMap pro i j g h) ≫ α

/-- Only the integral indices are transported; the coefficient and support maps are
spelled out separately. Source: supported functoriality, graded laws
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupReindex (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) {a b r s : ℤ} (ha : a = b) (hr : r = s)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro i b s :=
  ha ▸ hr ▸ α

/-- The canonical Ext-to-derived-Hom map, with its localization explicitly shared.
Source: Mathlib Ext.hom (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExtHom {B : Type c} [Category.{v} B] [Abelian B]
    [HasExt.{w} B] [hD : HasDerivedCategory.{w} B] {F G : B} (x : Abelian.Ext F G 1) :
    (DerivedCategory.singleFunctor B 0).obj F ⟶
      ((DerivedCategory.singleFunctor B 0).obj G)⟦(1 : ℤ)⟧ := x.hom

/-- Transport an Ext class along equality of its target before specializing coefficients.
Source: def-pur-frame-class, identical signed Kummer targets
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExtTarget {B : Type c} [Category.{v} B] [Abelian B] [HasExt.{w} B]
    {F G H : B} (h : G = H) (x : Abelian.Ext F G 1) : Abelian.Ext F H 1 :=
  h ▸ x

/-- The frame twist is the identical signed etale coefficient line.
Source: def-pur-frame-class, degree-one Kummer target
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold frameTwistEtale and functorialCupTwist at the etale site; both
are the same finiteEtaleTateSheaf with the same annihilation proof. -/
theorem functorialCupFrameTwistEtale_eq (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.frameTwistEtale X 1 = P.functorialCupTwist false X 1 := by
  sorry

/-- The frame twist is the identical signed pro-etale coefficient line.
Source: def-pur-frame-class, comparison of the Kummer target
(blueprint: lem-pur-supported-cup-functoriality).
Proof: both frameTwist and functorialCupTwist on the pro-etale site are the
same exact comparison inverse image of the etale signed finite coefficient line. -/
theorem functorialCupFrameTwist_eq (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.frameTwist X 1 = P.functorialCupTwist true X 1 := by
  sorry

/-- The published Kummer Ext class, selected before passing to derived Hom.
Source: the arbitrary-index Kummer prescription
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupKummerExt (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.functorialCupConstant pro X) (P.functorialCupTwist pro X 1) 1 :=
  match pro with
  | false => functorialCupExtTarget (P.functorialCupFrameTwistEtale_eq X)
      (P.frameKummerEtale X aX v)
  | true => functorialCupExtTarget (P.functorialCupFrameTwist_eq X) (P.frameKummer X aX v)

/-- The identity direct-image unitor of the actual supported coefficient source.
Source: the full-support normalization
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupFullSupportIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupSource pro (𝟙 X) ≅ P.functorialCupConstant pro X :=
  match pro with
  | false => (Etale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.constantEtale X)
  | true => (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X)

/-- The concrete published Kummer class in the full-support Hom model. The direct
image along the identity is identified by its canonical unitor.
Source: def-pur-frame-class, arbitrary-index Kummer prescription
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupKummer (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    P.FunctorialCupH pro (𝟙 X) 1 1 :=
  (P.functorialCupSingle pro X).map (P.functorialCupFullSupportIso pro X).hom ≫
    functorialCupExtHom (hD := P.functorialCupHasDerived pro X)
      (P.functorialCupKummerExt pro X aX v)


/-- Scalar linearity of fixed-ring module sheaves, with the existing action.
Source: purity conventions (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupLinear (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Linear P.Coefficient (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The `identity` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraIdentity (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (sq : ChosenCartesianSquare (𝟙 C) i i (𝟙 X))
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupPullback pro i i (𝟙 X) (𝟙 C) sq aX a r α = α

/-- The `composition` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraComposition (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C X D Y E Z : Scheme.{u}}
      (i : C ⟶ X) (j : D ⟶ Y) (k : E ⟶ Z)
      [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
      (v : Y ⟶ X) (w : Z ⟶ Y) (g : D ⟶ C) (h : E ⟶ D)
      (sq : ChosenCartesianSquare g j i v) (sq' : ChosenCartesianSquare h k j w)
      (sq'' : ChosenCartesianSquare (h ≫ g) k i (w ≫ v))
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupPullback pro i k (w ≫ v) (h ≫ g) sq'' aX a r α =
      P.functorialCupPullback pro j k w h sq' (v ≫ aX) a r
        (P.functorialCupPullback pro i j v g sq aX a r α)

/-- The `kummer_add` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraKummerAdd (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) (u w : Γ(X, ⊤)ˣ),
    P.functorialCupKummer pro X aX (u * w) =
      P.functorialCupKummer pro X aX u + P.functorialCupKummer pro X aX w

/-- The `kummer_pullback` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraKummerPullback (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {X Y : Scheme.{u}} (v : Y ⟶ X)
      (sq : ChosenCartesianSquare v (𝟙 Y) (𝟙 X) v)
      (aX : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ),
    P.functorialCupPullback pro (𝟙 X) (𝟙 Y) v v sq aX 1 1
        (P.functorialCupKummer pro X aX u) =
      P.functorialCupKummer pro Y (v ≫ aX) (Units.map v.appTop.hom.toMonoidHom u)

/-- The `add_left` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAddLeft (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α α' : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s (α + α') β =
      P.functorialCup pro aX i j a b r s α β + P.functorialCup pro aX i j a b r s α' β

/-- The `add_right` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAddRight (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β β' : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α (β + β') =
      P.functorialCup pro aX i j a b r s α β + P.functorialCup pro aX i j a b r s α β'

/-- The `smul_left` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSmulLeft (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (c : P.Coefficient)
      (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s (c • α) β = c • P.functorialCup pro aX i j a b r s α β

/-- The `smul_right` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSmulRight (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (c : P.Coefficient)
      (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α (c • β) = c • P.functorialCup pro aX i j a b r s α β

/-- The `associativity` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAssociativity (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D E X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
      (g : pullback i (ProEtale.cupIntersection j k) ⟶
        pullback (ProEtale.cupIntersection i j) k)
      (hg : g ≫ ProEtale.cupIntersection (ProEtale.cupIntersection i j) k =
        ProEtale.cupIntersection i (ProEtale.cupIntersection j k))
      (a b c r s t : ℤ) (α : P.FunctorialCupH pro i a r)
      (β : P.FunctorialCupH pro j b s) (γ : P.FunctorialCupH pro k c t),
    P.functorialCup pro aX (ProEtale.cupIntersection i j) k (a+b) c (r+s) t
        (P.functorialCup pro aX i j a b r s α β) γ =
      P.functorialCupReindex pro _ (add_assoc a b c).symm (add_assoc r s t).symm
        (P.functorialCupChangeSupport pro _ _ g hg (a+(b+c)) (r+(s+t))
          (P.functorialCup pro aX i (ProEtale.cupIntersection j k) a (b+c) r (s+t)
            α (P.functorialCup pro aX j k b c s t β γ)))

/-- The `symmetry` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSymmetry (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (g : pullback j i ⟶ pullback i j)
      (hg : g ≫ ProEtale.cupIntersection i j = ProEtale.cupIntersection j i)
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α β = ((-1 : ℤ) ^ (a*b).natAbs) •
      P.functorialCupReindex pro _ (add_comm b a) (add_comm s r)
        (P.functorialCupChangeSupport pro _ _ g hg (b+a) (s+r)
          (P.functorialCup pro aX j i b a s r β α))

/-- The `pullback` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraPullback (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X C' D' Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) (i' : C' ⟶ Y) (j' : D' ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j]
      [IsClosedImmersion i'] [IsClosedImmersion j']
      (v : Y ⟶ X) (g : C' ⟶ C) (h : D' ⟶ D)
      (sq : ChosenCartesianSquare g i' i v) (sq' : ChosenCartesianSquare h j' j v)
      (q : pullback i' j' ⟶ pullback i j)
      (sqp : ChosenCartesianSquare q (ProEtale.cupIntersection i' j')
        (ProEtale.cupIntersection i j) v)
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCupPullback pro _ _ v q sqp aX (a+b) (r+s)
        (P.functorialCup pro aX i j a b r s α β) =
      P.functorialCup pro (v ≫ aX) i' j' a b r s
        (P.functorialCupPullback pro i i' v g sq aX a r α)
        (P.functorialCupPullback pro j j' v h sq' aX b s β)

/-- All algebraic laws in the statement, on the actual supported Hom groups.
A morphism between the indicated closed supports over X is necessarily the canonical
support identification, since their immersions are monic. Thus the symmetry and
associativity fields include their support identifications, not an equality of
differently supported groups. Source: Stacks 0FPL and 0FPM, proof Steps 2--5 and 8
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupAlgebraLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  identity : P.FunctorialCupAlgebraIdentity pro
  composition : P.FunctorialCupAlgebraComposition pro
  kummer_add : P.FunctorialCupAlgebraKummerAdd pro
  kummer_pullback : P.FunctorialCupAlgebraKummerPullback pro
  add_left : P.FunctorialCupAlgebraAddLeft pro
  add_right : P.FunctorialCupAlgebraAddRight pro
  smul_left : P.FunctorialCupAlgebraSmulLeft pro
  smul_right : P.FunctorialCupAlgebraSmulRight pro
  associativity : P.FunctorialCupAlgebraAssociativity pro
  symmetry : P.FunctorialCupAlgebraSymmetry pro
  pullback : P.FunctorialCupAlgebraPullback pro


/-- Ordinary cohomology in the same derived-Hom model. Source: Hom_A(A,-)=sections
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupOrdinaryH (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupConstant pro X) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- Forget supports by the actual restriction of constants to the support.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupForget (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupOrdinaryH pro X a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupRestriction pro i) ≫ α

/-- Ordinary pullback, using exact inverse image and the same twist normalization.
Source: Stacks 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOrdinaryPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOrdinaryH pro Y a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupConstantPullback pro v).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupConstant pro X) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

/-- The published exact extension by zero for the complementary open.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenExtension (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupSheaves pro i.openComplement.toScheme ⥤ P.functorialCupSheaves pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι

/-- Extension by zero of the actual unit on the open complement.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  (P.functorialCupOpenExtension pro i).obj
    (P.functorialCupConstant pro i.openComplement.toScheme)

/-- The adjunction counit, with its canonical constant-sheaf restriction.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenInclusion (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenSource pro i ⟶ P.functorialCupConstant pro X :=
  match pro with
  | false => (P.functorialCupOpenExtension false i).map
      (P.functorialCupConstantPullback false i.openComplement.ι).inv ≫
      (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constantEtale X)
  | true => (P.functorialCupOpenExtension true i).map
      (P.functorialCupConstantPullback true i.openComplement.ι).inv ≫
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constant X)

/-- The source coefficient arrows form a complex for every closed support.
Source: Stacks 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: restriction of an extension-by-zero section to the complementary closed
subscheme is zero, on every object of either small site. Sheafification preserves
this identity. -/
theorem functorialCupSequence_zero (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenInclusion pro i ≫ P.functorialCupRestriction pro i = 0 := by
  sorry

/-- The actual open-closed coefficient sequence, before deriving.
Source: Stacks 095L, 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSequence (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  ShortComplex.mk (P.functorialCupOpenInclusion pro i) (P.functorialCupRestriction pro i)
    (P.functorialCupSequence_zero pro i)

/-- Exactness of this normalized coefficient sequence on either small site.
Source: Stacks 095L, 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: apply the recorded open-closed sequence on the etale site. On the pro-etale
site compare the exact sequence by exact inverse image, identifying the closed
source by restriction of local constants and the open source by the counit-normalized
extension-by-zero comparison. This argument does not require a quasi-compact complement. -/
theorem functorialCupSequence_shortExact (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (P.functorialCupSequence pro i).ShortExact := by
  sorry

/-- Cohomology of the open complement in its exact extension-by-zero adjunction
model Hom_X(j!A_U,F[a])=Hom_U(A_U,j*F[a]). This retains the usual cohomology
on U with the restriction of A(r). Source: Stacks 09XP
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupOpenH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupOpenSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- Ordinary restriction is precomposition with the open adjunction counit.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOpenH pro i a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupOpenInclusion pro i) ≫ α

/-- The localization boundary with the source sequence's actual connecting arrow.
Its normalization is the same Ext composition as the individual frame boundary.
Source: thm-pur-with-support-exactness and Stacks 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupBoundary (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupH pro i (a + 1) r :=
  ShiftedHom.comp (P.functorialCupSequence_shortExact pro i).singleδ α rfl

/-- Open coefficient exchange is uniquely normalized by its inclusion in the unit.
Source: Stacks 09XP, supported functoriality, Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: exact inverse image and extension by zero commute for the base-changed open.
Their canonical comparison respects counits by adjunction. Its tensor-unit
normalization gives the displayed equation; the monic open inclusion proves uniqueness. -/
theorem functorialCupOpenExchange_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage pro v).obj (P.functorialCupOpenSource pro i) ≅
        P.functorialCupOpenSource pro j,
      (P.functorialCupInverseImage pro v).map (P.functorialCupOpenInclusion pro i) ≫
          (P.functorialCupConstantPullback pro v).hom =
        b.hom ≫ P.functorialCupOpenInclusion pro j := by
  sorry

/-- Canonical open pullback, expressed by exact inverse image on the adjunction Hom model.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupOpenH pro j a r :=
  (P.functorialCupSingle pro Y).map
      (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose.inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupOpenSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

/-- The localization compatibility clauses, including the full-support normalization.
Source: Stacks 09XP and 0G78, proof Step 4
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupLocalizationLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  full_support : ∀ (X : Scheme.{u}) (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupForget pro (𝟙 X) a r)
  forget_support : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupForget pro j a r (P.functorialCupPullback pro i j v g sq aX a r α) =
      P.functorialCupOrdinaryPullback pro v aX a r (P.functorialCupForget pro i a r α)
  open_restriction : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOrdinaryH pro X a r),
    P.functorialCupOpenPullback pro i j v g sq aX a r
        (P.functorialCupOpenRestriction pro i a r α) =
      P.functorialCupOpenRestriction pro j a r
        (P.functorialCupOrdinaryPullback pro v aX a r α)
  boundary : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r),
    P.functorialCupPullback pro i j v g sq aX (a+1) r
        (P.functorialCupBoundary pro i a r α) =
      P.functorialCupBoundary pro j a r (P.functorialCupOpenPullback pro i j v g sq aX a r α)


/-- Map a degree-zero shifted Hom by an exact functor, using its canonical
single and shift comparisons before specializing the site categories.
Source: finite site comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExactHom {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B]
    [hD : HasDerivedCategory.{w} D] (F : B ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : B} (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj S) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj T))⟦a⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫
    F.mapDerivedCategory.map α ≫
    (F.mapDerivedCategory.commShiftIso a).hom.app
      ((DerivedCategory.singleFunctor B 0).obj T) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app T)⟦a⟧'

/-- Closed sources are canonically identified by the site comparison, normalized
on local constants. Source: Stacks 099V, 099W; proof Step 6
(blueprint: lem-pur-supported-cup-functoriality).
Proof: on a weakly etale Y over X the inverse-image section formula computes
etale sections on Y of the closed direct image. Etale base change identifies these
with constants on Y times_X C. Degree-zero comparison identifies them with the
same pro-etale constants. These identifications commute with restriction and
scalar multiplication and carry 1 to 1. They glue to the specified isomorphism.
The epic constant restriction makes it unique. -/
theorem functorialCupComparisonSource_existsUnique (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupSource false i) ≅ P.functorialCupSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupRestriction false i) ≫ b.hom = P.functorialCupRestriction true i := by
  sorry

/-- The comparison target of the signed twist is its defining pro-etale sheaf.
Source: finite coefficient twist comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold the two selected twists and the comparison functor. Both sides
are exact comparison inverse image of the same signed finite etale Tate sheaf. -/
theorem functorialCupComparisonTwist_eq (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (r : ℤ) :
    (P.functorialCupComparisonFunctor X).obj (P.functorialCupTwist false X r) =
      P.functorialCupTwist true X r := by
  sorry

/-- The comparison target of the coefficient unit is its defining pro-etale constant.
Source: finite coefficient comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold the constant sheaves and comparison functor; the pro-etale
coefficient unit was defined as comparison inverse image of the etale unit. -/
theorem functorialCupComparisonConstant_eq (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    (P.functorialCupComparisonFunctor X).obj (P.functorialCupConstant false X) =
      P.functorialCupConstant true X := by
  sorry

/-- Canonical comparison on the supported Hom groups. The finite twist on the
pro-etale site is the exact inverse image of the identical etale twist.
Source: Stacks 09B1, supported functoriality Step 7
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH false i a r) : P.FunctorialCupH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonSource_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- Ordinary site comparison in the identical degree-zero and shift conventions.
Source: Stacks 099W (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOrdinaryCompare (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH false X a r) : P.FunctorialCupOrdinaryH true X a r :=
  (P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonConstant_eq X).symm) ≫
  functorialCupExactHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- Open comparison preserves the actual extension-by-zero counit.
Source: Stacks 099V, proof Step 7; lem-cbc-proetale-extension-zero-comparison
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the canonical comparison restricts to the identity on the open. Under the
two extension-by-zero adjunctions the counits correspond to that same identity.
The open inclusion is monic, so its equation specifies the comparison uniquely. -/
theorem functorialCupComparisonOpen_existsUnique (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupOpenSource false i) ≅ P.functorialCupOpenSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupOpenInclusion false i) =
        b.hom ≫ P.functorialCupOpenInclusion true i := by
  sorry

/-- Site comparison on open cohomology in the extension-by-zero adjunction model.
Source: Stacks 099V, 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH false i a r) : P.FunctorialCupOpenH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonOpen_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- The `supported_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonSupportedBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupCompare i a r)

/-- The `ordinary_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOrdinaryBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupOrdinaryCompare X a r)

/-- The `open_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupOpenCompare i a r)

/-- The `pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupH false i a r),
    P.functorialCupCompare j a r (P.functorialCupPullback false i j v g sq aX a r α) =
      P.functorialCupPullback true i j v g sq aX a r (P.functorialCupCompare i a r α)

/-- The `ordinary_pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOrdinaryPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (v : Y ⟶ X)
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
      (α : P.FunctorialCupOrdinaryH false X a r),
    P.functorialCupOrdinaryCompare Y a r (P.functorialCupOrdinaryPullback false v aX a r α) =
      P.functorialCupOrdinaryPullback true v aX a r (P.functorialCupOrdinaryCompare X a r α)

/-- The `open_pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOpenH false i a r),
    P.functorialCupOpenCompare j a r (P.functorialCupOpenPullback false i j v g sq aX a r α) =
      P.functorialCupOpenPullback true i j v g sq aX a r (P.functorialCupOpenCompare i a r α)

/-- The `cup` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonCup (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α : P.FunctorialCupH false i a r) (β : P.FunctorialCupH false j b s),
    P.functorialCupCompare _ (a+b) (r+s) (P.functorialCup false aX i j a b r s α β) =
      P.functorialCup true aX i j a b r s
        (P.functorialCupCompare i a r α) (P.functorialCupCompare j b s β)

/-- The `kummer` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonKummer (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ),
    P.functorialCupCompare (𝟙 X) 1 1 (P.functorialCupKummer false X aX u) =
      P.functorialCupKummer true X aX u

/-- The `forget_support` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonForgetSupport (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupH false i a r),
    P.functorialCupOrdinaryCompare X a r (P.functorialCupForget false i a r α) =
      P.functorialCupForget true i a r (P.functorialCupCompare i a r α)

/-- The `open_restriction` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenRestriction (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupOrdinaryH false X a r),
    P.functorialCupOpenCompare i a r (P.functorialCupOpenRestriction false i a r α) =
      P.functorialCupOpenRestriction true i a r (P.functorialCupOrdinaryCompare X a r α)

/-- The `boundary` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonBoundary (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupOpenH false i a r),
    P.functorialCupCompare i (a+1) r (P.functorialCupBoundary false i a r α) =
      P.functorialCupBoundary true i a r (P.functorialCupOpenCompare i a r α)

/-- All operation-identification clauses for the canonical etale-to-pro-etale
comparison, including both arrows and the boundary of localization.
Source: Stacks 09B1, 099V and 099W, proof Steps 6--8
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupComparisonLaws (P : PurityFiniteSetting.{u}) : Prop where
  supported_bijective : P.FunctorialCupComparisonSupportedBijective
  ordinary_bijective : P.FunctorialCupComparisonOrdinaryBijective
  open_bijective : P.FunctorialCupComparisonOpenBijective
  pullback : P.FunctorialCupComparisonPullback
  ordinary_pullback : P.FunctorialCupComparisonOrdinaryPullback
  open_pullback : P.FunctorialCupComparisonOpenPullback
  cup : P.FunctorialCupComparisonCup
  kummer : P.FunctorialCupComparisonKummer
  forget_support : P.FunctorialCupComparisonForgetSupport
  open_restriction : P.FunctorialCupComparisonOpenRestriction
  boundary : P.FunctorialCupComparisonBoundary

/-- Pullback, localization, concrete Kummer identities and graded cup laws on both
small sites, identified by their canonical site comparison.
Source: Stacks Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

Proof:
1. Put m=ell^n. It annihilates A at every positive coefficient level. Apply
lem-asd-etale-finite-twist-pullback to its roots line, powers and duals. The local
primitive-root descriptions and lem-pur-twist-sheaf-locally-free identify the
projection-induced pro-etale twist and root coefficient map with this finite line.
Compare the identical root sections by lem-cbc-abelian-etale-proetale-cohomology-comparison
and lem-sf-comparison-pullback-exact. Every twist is a flat rank-one line.
2. Use lem-pur-etale-closed-constant-tensor: closed coefficients are flat, and the
normalized exchange and tensor multiplication are invertible and coherent. This
constructs the etale analogue of def-pur-supported-cup without exceptional base change.
3. Total tensor has its usual associator and Koszul symmetry. On homogeneous
cochains of degrees p,q the symmetry is (-1)^(pq). The two differential signs agree.
Descend these constraints through flat-term K-flat representatives using
lem-weil-pbc-site-derived-tensor-descent and lem-pc-kflat-closure. The canonical
ringed-topos tensor pullback comparison respects them termwise.
4. Use lem-amb-closed-support-hom and prop-weil-pbc-inverse-image-modules-exact
to pull back a representative as tau[a] v inverse(alpha) b inverse. Evaluation at 1
on injective representatives identifies this with the usual support-kernel pullback:
lem-weil-pbc-ext-exact-functor-cocycle and lem-weil-pbc-site-cohomology-pullback give
the normalization. Negative degrees vanish. Naturality of the actual source
short exact sequence gives restriction and boundary compatibility, with the
boundary convention of thm-pur-with-support-exactness. Unit-normalized exchanges
compose and are identities. For full support this is ordinary pullback.
5. Apply lem-pur-shifted-tensor-morphism-calculus to the flat support sources and
rank-one targets. Its sign is (-1)^(bp), exactly cupTensorShiftIso. Biadditivity
and scalar linearity give bilinearity. Its associativity and signed symmetry,
the source multiplications from Step 2 and the twist multiplications from Step 1
give associativity and (-1)^(ab) symmetry. Its pullback equation cancels the
normalized source exchanges and gives the cup pullback equality.
6. Evaluate comparison of a closed source on every weakly etale Y over X.
lem-cbc-comparison-pullback-sections and etale base change identify it with
etale constants on Y times_X C; degree-zero comparison identifies these with
pro-etale constants. Restriction and multiplication of the same local constants
identify the two coefficient multiplication maps and their flat derived maps.
No conservativity of pro-etale geometric stalks is asserted.
7. Full faithfulness in thm-weil-pbc-site-comparison and the supported Hom models
give the comparison bijections. lem-weil-pbc-comparison-pullback gives their
pullback square. lem-cbc-proetale-extension-zero-comparison preserves the open
counit by adjunction; together with Step 6 this identifies both arrows of the
source short exact sequence. The exact-functor single-delta formula
lem-weil-pbc-exact-functor-ses-triangle-image identifies the actual boundary,
including its sign. Step 5 then identifies the cups, and every pro-etale class
comes from an etale class, transporting all laws.
8. The Kummer sequence is short exact by lem-amb-kummer-any-base. Its connecting
map is additive by lem-weil-pbc-right-derived-universal-delta-functor. Pullback of
units commutes with powers and roots, giving naturality of its connecting map
by lem-weil-pbc-site-cohomology-pullback. The scalar extension sends a root to
that root tensor 1 and commutes with pullback. Def-pur-frame-class specifies
the concrete pro-etale class by comparison and this very root coefficient map,
so both Kummer identities and their site comparison follow. -/
theorem supportedCupFunctoriality (P : PurityFiniteSetting.{u}) :
    (∀ pro : Bool, P.FunctorialCupAlgebraLaws pro ∧ P.FunctorialCupLocalizationLaws pro) ∧
      P.FunctorialCupComparisonLaws := by
  sorry

end WeilConjectures.PurityFiniteSetting

