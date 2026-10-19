/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist

import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
import Sheaf.SmoothPurity.TensorMateEtalePrecomp
import Sheaf.Paper.PurityDiagonalOrientationCompatibility
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.Paper.ExceptionalCoefficientComparison
import Sheaf.Paper.FiniteSmoothGammaNormalization
import Sheaf.Paper.NoetherianEtaleSectionSpecialization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
import Sheaf.Paper.FiniteRingSectionDeformation
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Compactification.NagataCompactification

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Noetherian prime-power smooth duality

Source: Scholze, Six-Functor Formalisms, Theorem 7.19 and the following paragraph;
main-20261015, sk-prop-sp-orientation and sk-thm-dnc
(blueprint: lem-per-noetherian-prime-power-smooth-duality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.NoetherianSmoothDuality
open FiniteSmoothPurity

/-- The ordered Tate-line pullback, with its roots and scalar generators fixed by the
projective-line normalization. Source: Scholze, Theorem 7.19 and the following paragraph;
sk-prop-sp-orientation (blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def linePullback (ell n : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback (coefficient ell n) f).obj
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) Y d) ≅
      line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d :=
  vectorIntegrationBaseCoefficientPullback (coefficient ell n) (ell ^ n)
    (CharP.cast_eq_zero _ _)
    (projectiveLineTraceTransport (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      (coefficient ell n) (CharP.cast_eq_zero _ _)) f hY d

/-- Concatenate the ordered shifted Tate tensors; this is tensor associativity and the
unit constraint, including the empty product. Source: sk-prop-sp-orientation, composition
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def lineAppend (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (s : ℕ) : ∀ r : ℕ,
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).obj
        (line A N hA X r) ≅ line A N hA X (s + r) :=
  Nat.rec
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj (line A N hA X s)).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) ≪≫
        derivedTensorRightUnitor (ModuleCat.{u + 1} A) X (line A N hA X s))
    (fun r ih ↦
      (derivedTensorAssociator (ModuleCat.{u + 1} A) X (line A N hA X s)
        (line A N hA X r) ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).symm ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso ih).app _)

/-- Identify the purity source at the coefficient unit by inverse-image and tensor
unit constraints. Source: sk-prop-sp-orientation, unit normalization
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def unitSource (A : Type (u + 1)) [CommRing A] {P X : Scheme.{u}} (p : P ⟶ X)
    (L : DerivedCategoryModule A P) : (puritySource A p L).obj (𝟙_ _) ≅ L :=
  ((derivedTensor (ModuleCat.{u + 1} A) P).mapIso
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) p)).app L ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} A) P L

/-- The normalized orientation and its bounded-below tensor isomorphisms. All geometric
auxiliaries are conclusions; the orientation is constrained by the actual three-factor
DNC equation. Source: Scholze, Theorem 7.19; sk-prop-sp-orientation
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
structure Datum (ell n : ℕ) [Fact ell.Prime]
    {P X : Scheme.{u}} [IsNoetherian P] [IsNoetherian X]
    (p : P ⟶ X) [HasCompactification p] [QuasiCompact p] [IsSeparated p] (r : ℕ)
    (hP : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤))) where
  geometry : FiniteRingSectionDeformation.Geometry r (pullback.fst p p) (pullback.diagonal p)
  alpha : dualizingComplex (ModuleCat.{u + 1} (coefficient ell n)) p ≅
    line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r
  normalized : OrientationNormalized (coefficient ell n) (ell ^ n)
    (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _)
    p r geometry hP alpha
  tensor_isIso : ∀ K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell n))),
    IsIso (gamma (coefficient ell n) p
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r) alpha K.obj)
  unit_normalization : gamma (coefficient ell n) p
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r) alpha (𝟙_ _) =
    (unitSource (coefficient ell n) p
      (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r)).hom ≫ alpha.inv
  etale_comparison_exists : r = 0 →
    ∃ C : FiniteSmoothCompactSupportComparisons.{u} (coefficient.{u} ell n),
      FiniteSmoothComparisonNormalized (coefficient ell n) C
  dimension_zero : ∀ hd : r = 0, ∀ [Etale p],
    ∀ C : FiniteSmoothCompactSupportComparisons (coefficient ell n),
    FiniteSmoothComparisonNormalized (coefficient ell n) C →
    ∀ K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell n))),
    gamma (coefficient ell n) p
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r) alpha K.obj ≫
      (finiteSmoothAdjointCoordinates (coefficient ell n) C p).hom.app K.obj =
        zeroSourceMap (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) p r hd K.obj

/-- One family for all Noetherian smooth maps and all positive levels. Invertibility of
ell^n for n positive is equivalent to invertibility of ell. Both source and target witnesses
are included to avoid making a choice of their proofs. Source: sk-prop-sp-orientation
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def Family (ell : ℕ) [Fact ell.Prime] :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (P X : Scheme.{u}) [IsNoetherian P] [IsNoetherian X]
    (p : P ⟶ X) [HasCompactification p] [QuasiCompact p] [IsSeparated p]
    (r : ℕ) [SmoothOfRelativeDimension r p]
    (hP : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤))) (_hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤))),
    Datum ell n p r hP

/-- The source of the base-change square, using tensor pullback, the inverse-image
compositor, and the roots-normalized Tate pullback. Source: sk-prop-sp-orientation
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def baseChangeSource (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {P X X' : Scheme.{u}} (p : P ⟶ X) (b : X' ⟶ X)
    (hP : IsUnit (N : Γ(P, ⊤))) (r : ℕ)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A (pullback.fst p b)).obj
        ((puritySource A p (line A N hA P r)).obj K) ≅
      (puritySource A (pullback.snd p b) (line A N hA (pullback p b) r)).obj
        ((ordinaryFinitePullback A b).obj K) :=
  ordinaryFiniteTwistedPullbackComparison A p (pullback.snd p b) b
    (pullback.fst p b)
    (line A N hA P r)
    (line A N hA (pullback p b) r) K
    (smoothSquarePullbackIso A p b K)
    (vectorIntegrationBaseCoefficientPullback A N hA t (pullback.fst p b) hP r)

/-- The actual exceptional transitivity, conjugate to compact-support composition.
Source: sk-prop-sp-orientation, composition; Stacks 0F7J
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def exceptionalComp (A : Type (u + 1)) [CommRing A] [Finite A]
    {P X Y : Scheme.{u}} (p : P ⟶ X) (q : X ⟶ Y)
    [HasCompactification p] [HasCompactification q] [HasCompactification (p ≫ q)]
    [QuasiCompact p] [QuasiCompact (p ≫ q)] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) q ⋙
        rightDerivedUpperShriek (ModuleCat.{u + 1} A) p ≅
      rightDerivedUpperShriek (ModuleCat.{u + 1} A) (p ≫ q) :=
  conjugateIsoEquiv
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) p).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) q))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (p ≫ q))
    (unboundedEtaleLowerShriekCompIso A p q).symm

/-- Canonical source transitivity: inverse-image composition, ordered Tate tensor
concatenation, associativity, and tensor pullback. Source: sk-prop-sp-orientation
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def compositionSource (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {P X Y : Scheme.{u}} (p : P ⟶ X) (q : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (r s : ℕ)
    (K : DerivedCategoryModule A Y) :
    (puritySource A (p ≫ q) (line A N hA P (s + r))).obj K ≅
      (puritySource A p (line A N hA P r)).obj ((puritySource A q (line A N hA X s)).obj K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) P).mapIso
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p q).app K)).app _ ≪≫
  ((derivedTensor (ModuleCat.{u + 1} A) P).obj
    ((ordinaryFinitePullback A p).obj
      ((ordinaryFinitePullback A q).obj K))).mapIso
        (lineAppend A N hA P s r).symm ≪≫
  (derivedTensorAssociator (ModuleCat.{u + 1} A) P
    ((ordinaryFinitePullback A p).obj
      ((ordinaryFinitePullback A q).obj K))
    (line A N hA P s)
    (line A N hA P r)).symm ≪≫
  ((derivedTensor (ModuleCat.{u + 1} A) P).mapIso
    (((derivedTensor (ModuleCat.{u + 1} A) P).obj
      ((ordinaryFinitePullback A p).obj
        ((ordinaryFinitePullback A q).obj K))).mapIso
          (vectorIntegrationBaseCoefficientPullback A N hA t p hX s).symm ≪≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) p
        ((ordinaryFinitePullback A q).obj K)
        (line A N hA X s)).symm)).app _

/-- The base-change equation for the actual tensor maps, for every ordinary bounded-below
input and every Noetherian change of base. Source: sk-prop-sp-orientation
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def BaseChange (ell : ℕ) [Fact ell.Prime] (a : Family.{u} ell) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (P X X' : Scheme.{u})
    [IsNoetherian P] [IsNoetherian X] [IsNoetherian X']
    (p : P ⟶ X) [HasCompactification p] [QuasiCompact p] [IsSeparated p]
    (r : ℕ) [SmoothOfRelativeDimension r p] (b : X' ⟶ X)
    [IsNoetherian (pullback p b)]
    (hP : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤))) (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (hP' : IsUnit ((ell ^ n : ℕ) : Γ(pullback p b, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(X', ⊤)))
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell n)))),
    (ordinaryFinitePullback (coefficient ell n) (pullback.fst p b)).map
        (a n hn P X p r hP hX).alpha.inv ≫
      smoothDualizingBaseChangeMap (coefficient ell n) p b =
    (linePullback ell n (pullback.fst p b) hP r).hom ≫
      (a n hn (pullback p b) X' (pullback.snd p b) r hP' hX').alpha.inv ∧
    (ordinaryFinitePullback (coefficient ell n) (pullback.fst p b)).map
        (gamma (coefficient ell n) p
          (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r)
          (a n hn P X p r hP hX).alpha K.obj) ≫
      smoothExceptionalBaseChangeMap (coefficient ell n) p b K.obj =
    (baseChangeSource (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _)
      (projectiveLineTraceTransport (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
        (coefficient ell n) (CharP.cast_eq_zero _ _)) p b hP r K.obj).hom ≫
      gamma (coefficient ell n) (pullback.snd p b)
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) (pullback p b) r)
        (a n hn (pullback p b) X' (pullback.snd p b) r hP' hX').alpha
        ((ordinaryFinitePullback (coefficient ell n) b).obj K.obj)

/-- Smooth composition, including source open and separated etale restriction by taking
r=0 and using Datum.dimension_zero. Target restriction is included in BaseChange.
Source: sk-prop-sp-orientation and its chart proof
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def Composition (ell : ℕ) [Fact ell.Prime] (a : Family.{u} ell) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (P X Y : Scheme.{u})
    [IsNoetherian P] [IsNoetherian X] [IsNoetherian Y]
    (p : P ⟶ X) (q : X ⟶ Y)
    [HasCompactification p] [HasCompactification q] [HasCompactification (p ≫ q)]
    [QuasiCompact p] [QuasiCompact q] [QuasiCompact (p ≫ q)]
    [IsSeparated p] [IsSeparated q] [IsSeparated (p ≫ q)]
    (r s : ℕ) [SmoothOfRelativeDimension r p] [SmoothOfRelativeDimension s q]
    [SmoothOfRelativeDimension (s + r) (p ≫ q)]
    (hP : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤))) (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)))
    (K : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (coefficient ell n)))),
    gamma (coefficient ell n) (p ≫ q)
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P (s + r))
        (a n hn P Y (p ≫ q) (s + r) hP hY).alpha K.obj ≫
      (exceptionalComp (coefficient ell n) p q).inv.app K.obj =
    (compositionSource (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _)
      (projectiveLineTraceTransport (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
        (coefficient ell n) (CharP.cast_eq_zero _ _)) p q hX r s K.obj).hom ≫
      gamma (coefficient ell n) p
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) P r)
        (a n hn P X p r hP hX).alpha ((finiteSource ell n q s).obj K.obj) ≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (coefficient ell n)) p).map
        (gamma (coefficient ell n) q
          (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X s)
          (a n hn X Y q s hX hY).alpha K.obj)

/-- Coefficient reduction of the unit orientation, using the specified counit mate and
root-generator comparison. The root power is ell^(N-n), since (ell^N)/(ell^n) is that power.
Source: sk-prop-sp-orientation, coefficient normalization
(blueprint: lem-per-noetherian-prime-power-smooth-duality). -/
def Reduction (ell : ℕ) [Fact ell.Prime] (a : Family.{u} ell) : Prop :=
  ∀ (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (P X : Scheme.{u})
    [IsNoetherian P] [IsNoetherian X]
    (p : P ⟶ X) [HasCompactification p] [QuasiCompact p] [IsSeparated p]
    (r : ℕ) [SmoothOfRelativeDimension r p]
    (hPN : IsUnit ((ell ^ N : ℕ) : Γ(P, ⊤))) (hXN : IsUnit ((ell ^ N : ℕ) : Γ(X, ⊤)))
    (hPn : IsUnit ((ell ^ n : ℕ) : Γ(P, ⊤))) (hXn : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤))),
    ∃ e : CoefficientLineComparison (FiniteReduction.quotient ell hnN) (ell ^ N) (ell ^ n)
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) P,
    (ordinaryScalar (FiniteReduction.quotient ell hnN) P).map
        (a N (hn.trans hnN) P X p r hPN hXN).alpha.inv ≫
      ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hnN) p (𝟙_ _) ≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (coefficient ell n)) p).map
        (ExceptionalCoefficients.unitIso (FiniteReduction.quotient ell hnN) X).hom =
    (e.tensorPower r).hom ≫ (a n hn P X p r hPn hXn).alpha.inv

/-- Prime-power diagonal smooth duality over arbitrary Noetherian schemes, with all
specified normalizations and comparisons. Source: Scholze, Six-Functor Formalisms,
Theorem 7.19 and the following paragraph; sk-prop-sp-orientation and sk-thm-dnc
(blueprint: lem-per-noetherian-prime-power-smooth-duality).

Proof, following the DAG node step by step:

1. Put $A=\Lambda_n$ and $\omega_h=h_n^!A$. The self-product $W=P\times_XP$ is Noetherian, its
   first projection $p_1$ is separated finite type and smooth of dimension $r$, and its diagonal
   $\Delta$ is a regular closed immersion of codimension $r$ with normal bundle $T_{P/X}$. Indeed
   apply finite-type permanence, separated finite-type base change, smooth-dimension permanence
   and the diagonal regular-immersion lemma. A Noetherian scheme is quasi-compact by definition
   and quasi-separated by the locally-Noetherian lemma, so Nagata supplies compactifications for
   the separated finite-type maps used below. In particular the section-deformation lemma applies
   to $(p_1,\Delta)$; it supplies Noetherianity, smoothness and compactifiability of the
   deformation and normal-bundle maps. The same verifications apply after any Noetherian change of
   base.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-pod-separated-finite-type-base-change, lem-
   sbc-smooth-relative-dimension-permanence, lem-pur-diagonal-regular-immersion, lem-weil-pbc-
   locally-noetherian-quasi-separated, thm-nagata-compactification, lem-trf-finite-ring-section-
   deformation.

2. Fix the normalization for affine space over a Noetherian base $S$. For $q:\mathbf P^1_S\to S$,
   the ordinary finite projective-line adjunction has $G_qK=q^*K(1)[2]$ and counit $(1\otimes
   t_q)\mathrm{PF}^{-1}$, with $t_qc_1(\mathcal O(1))=1$. Its unit is the supported-diagonal
   formula of [det-sp-p1-adjunction]; the two diagonal integrals in
   [lem-amb-p1-diagonal-integrals] are its triangle identities. All coordinate-tower bases
   are Noetherian, as they are finite type over S; arbitrary-base integrals are unnecessary.
   Compose this adjunction with open extension for
   $\mathbf A^1_S\subset\mathbf P^1_S$, and then successively in the ordered coordinate tower.
   This is precisely the affine-space adjunction and trace of [lem-amb-affine-space-top-trace],
   with identity adjunction when $r=0$. Thus the chosen affine comparison
   $\Gamma_{r}:A(r)[2r]\to\omega_{p_r}$ uses the supported first Chern class of the diagonal and
   the prescribed integration normalization.
   Uses: lem-asd-ordinary-finite-p1-adjunction, det-sp-p1-adjunction,
   lem-amb-p1-diagonal-integrals, lem-weil-pbc-finite-type-over-noetherian,
   lem-amb-affine-space-top-trace, def-weil-pbc-composite-adjunction.

3. Apply [prop-asd-smooth-base-change] to the self-base-change square of $p$. Its unit-coefficient
   comparison $p_2^*\omega_p\xrightarrow{\sim}\omega_{p_1}$ restricts along $\Delta$ to
   $a_p:\omega_p\xrightarrow{\sim}\Delta^*\omega_{p_1}$, because $p_2\Delta=1_P$. The normalized
   finite-ring section deformation gives
   $\delta_p:\Delta^*\omega_{p_1}\xrightarrow{\sim}z^*\omega_\pi$, where $\pi:T_{P/X}\to P$ and
   $z$ is zero. The same $\delta_p$ is the normalized comparison $\delta_{p_1,\Delta}$ of [lem-
   pur-noetherian-etale-section-specialization]: that lemma applies to $(p_1,\Delta)$ with
   $A=\Lambda_n$ (its regularity, smoothness and compactifiability hypotheses are those verified
   in Step 1), it uses the same Rees family $D=\underline{\operatorname{Spec}}_W\mathcal
   O_W[t,\mathcal I/t]$ and the same exceptional base-change fibre identifications, and both
   lemmas characterize $\kappa$ as the unique isomorphism $F\to a^*C$ restricting to $1_C$ at
   $t=1$. Hence the deformation factor of Step 12 and the comparison $\kappa$ of Step 16 are the
   ones used here. In [thm-amb-vector-bundle-purity] take the coefficient extension $F=\mathbf
   Q_\ell$, uniformizer $\ell$, and stage $n$; its coefficient ring is $A$. Denote its unit
   comparison by $v_\pi:A(r)[2r]\xrightarrow{\sim}\omega_\pi$. Set
   $$\alpha_p=z^*(v_\pi^{-1})\circ\delta_p\circ a_p,\qquad\gamma_{p,n}=\alpha_p^{-1}.$$ The Tate
   comparison is exactly the ordinary roots-of-unity comparison in that theorem and [lem-asd-
   etale-finite-twist-pullback]. This proves the specified three-factor orientation is an
   isomorphism.
   Uses: prop-asd-smooth-base-change, lem-trf-finite-ring-section-deformation, thm-amb-vector-
   bundle-purity, lem-asd-etale-finite-twist-pullback, lem-pur-noetherian-etale-section-
   specialization.

4. For every $K\in D^+(X_{\mathrm{et}},A)$, define
   $$\gamma_{p,K}=\phi_{p,K}\circ(1\otimes\alpha_p^{-1}):p^*K(r)[2r]\longrightarrow p_n^!K,$$ with
   the tensor/shift unit identifications understood. Here $\phi_{p,K}$ is exactly the transpose of
   inverse compact-support projection followed by the unit-object counit, as specified in [thm-
   asd-smooth-tensor]. That theorem makes this actual map invertible for every ordinary derived
   input. Step 3 makes its other factor invertible. Therefore $\gamma_{p,K}$ is an isomorphism
   natural in $K$. This uses neither constructibility nor finite Tor amplitude of $K$.
   Uses: thm-asd-smooth-tensor, lem-asd-etale-finite-twist-pullback.

5. We compute the orientation on an affine smooth chart $h:U\to V$, with a separated etale
   coordinate map $e:U\to\mathbf A^r_V$. Such charts exist by [sbc-thm-etale-local-normal-form];
   their opens are Noetherian. On $U\times_VU$ the functions $e_j(u_2)-e_j(u_1)$ define an etale
   map to $\mathbf A^r_U$, by etale base change and the translation isomorphism. Its zero fibre is
   $U\times_{\mathbf A^r_V}U$, etale separated over $U$. The diagonal is a clopen section of that
   fibre; remove its complementary closed subscheme. This gives a neighbourhood of the diagonal
   whose inverse image of zero is exactly the diagonal. The section-deformation theorem identifies
   the normal frame with the classes of these coordinate differences and identifies its normalized
   $\delta$ with the identity on the standard section invariant.
   Uses: sbc-thm-etale-local-normal-form, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-
   weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-section-clopen-immersion, lem-trf-finite-
   ring-section-deformation.

6. The self-base-change comparison $a_h$ computed using $(u_1,e(u_2))$ agrees with the one
   computed using $(u_1,e(u_2)-e(u_1))$. Indeed these charts differ by translation by the section
   $e(u_1)$, and [lem-trf-ambient-affine-translation-trace] states that this translation preserves
   the actual ordered trace. Taking mates identifies the dualizing comparisons. The vector-bundle
   orientation in the normal frame of Step 5 is the ordered affine orientation: the finite-ring
   section theorem states this normalization, and vector-bundle purity specifies its counit. The
   affine orientation is compatible with base change along $h$: for $h':\mathbf A^r_U\to\mathbf
   A^r_V$, the map $\beta_{p_r,h}:h'^*\omega_{p_r,V}\xrightarrow{\sim}\omega_{p_r,U}$ of [prop-
   asd-smooth-base-change] is the transpose of the pulled-back counit through compact-support base
   change, and the equality $t_{p_{r,U}}\circ C_{r,h}=h^*t_{p_{r,V}}$ of [lem-amb-affine-space-
   top-trace] says exactly that this transpose carries $h'^*\Gamma_{r,V}$ to $\Gamma_{r,U}$. The
   chart $(u_1,e(u_2))$ is the base change of $e$ along $h$, so this identifies $a_h$, under $E_e$
   and the etale comparison for that chart, with the restriction along the section $(u,e(u))$ of
   $\Gamma_{r,U}$; the translation by $e(u_1)$ moves this section to zero. Pasting the self-
   product squares through $h=p_re$, using etale adjoint locality and mate pasting, now gives
   $$\alpha_h=e^*(\Gamma_r^{-1})\circ E_e,\quad E_e:\omega_h\xrightarrow{\sim}e^*\omega_{p_r}.$$
   Here $E_e$ is the counit-preserving etale comparison. The tensor-mate identity for etale
   precomposition identifies $\gamma_{h,K}$ with that same coordinate adjunction for every $K$.
   Uses: lem-trf-ambient-affine-translation-trace, lem-trf-finite-ring-section-deformation, thm-
   amb-vector-bundle-purity, lem-amb-etale-adjoint-locality, lem-weil-pbc-mate-pasting, lem-asd-
   tensor-mate-etale-precomp, prop-asd-smooth-base-change, lem-amb-affine-space-top-trace.

7. For $b:X'\to X$ with $X'$ Noetherian, let $b':P'\to P$ and
   $B:b'^*\omega_p\xrightarrow{\sim}\omega_{p'}$ be the canonical exceptional mate. The self-
   product square after base change is the pullback of the original square. Compact-support
   exchange is compatible with successive base changes and composition, and its exceptional mates
   obey pasting. These equations identify the pullback of $a_p$ with $a_{p'}$. The section-
   deformation theorem identifies the pullback of $\delta_p$ with $\delta_{p'}$, under these same
   fibre and normal-bundle comparisons. Thus the first two factors of $\alpha_p$ commute with this
   arbitrary Noetherian base change.
   Uses: prop-asd-smooth-base-change, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-
   mate-pasting, lem-trf-finite-ring-section-deformation.

8. For the vector factor, integration on each bundle trivialization is the affine trace. The
   equality $t_{p'_r}C_{r,b}=b^*t_{p_r}$ in the affine-space trace theorem therefore identifies
   the two integration maps on the pulled-back trivializing cover. Their compact-support source is
   concentrated in degree zero: locally it is isomorphic to $A[0]$ by that theorem. The definition
   of vector integration, full faithfulness of the degree-zero embedding and sheaf-Hom gluing give
   equality globally. Taking mates gives the corresponding equality for $v_\pi$ and its zero-
   section restriction. Together with Step 7 this proves $$\alpha_{p'}B=b'^*\alpha_p.$$ The
   tensor/base-change identity in [prop-asd-smooth-base-change], with
   $\alpha_{p'}^{-1}=B(b'^*\alpha_p)^{-1}$ substituted, gives
   $\beta_{p,b,K}b'^*\gamma_{p,K}=\gamma_{p',b^*K}$, with the canonical twist comparison.
   Uses: lem-amb-affine-space-top-trace, def-amb-vector-integration, lem-weil-pbc-derived-single-
   fully-faithful, lem-pur-sheaf-hom-cover-gluing, lem-weil-pbc-mate-pasting, prop-asd-smooth-
   base-change.

9. Open or separated etale restriction on the source preserves the specified orientation. First
   let $V\subset X$ be open and $U\subset P_V=P\times_XV$ open, with $h=p|_U$. Restriction of the
   base to $V$ is the Noetherian base change of Steps 7 and 8. For the open $U\subset P_V$ the
   three factors restrict separately. (a) $U\times_VU$ is open in $P_V\times_VP_V$; the maps
   $\beta$ of [prop-asd-smooth-base-change] for the two self-squares are transposes of pulled-back
   counits, so the etale comparisons of [lem-amb-etale-adjoint-locality] and mate pasting carry
   the restriction of $a_{p_V}$ to $a_h$. (b) The normalized comparison commutes with the
   Noetherian base change $U\to P_V$ of the section base and with the open neighbourhood
   $U\times_VU$ of the diagonal, whose square of centres is Cartesian, by [lem-trf-finite-ring-
   section-deformation]. (c) $T_{U/V}=T_{P_V/V}|_U$, and by [def-amb-vector-integration] both
   integrations are the unique maps restricting to the affine traces on trivializations, so
   $v_\pi$ restricts to $v_{\pi_U}$. Thus $\alpha_p|_U$ corresponds to $\alpha_h$ under the
   counit-preserving open comparison; in particular Steps 5 and 6 compute $\alpha_p$ itself on
   every coordinate chart. For a separated etale $j:P'\to P$, compute both orientations on a
   further smooth coordinate cover using Steps 5 and 6: both are the pullback of the same ordered
   affine orientation under the counit-preserving etale comparison. Successive etale charts
   compose, and their exceptional comparisons compose by mate pasting. The two unit-object maps
   are between equally shifted locally free rank-one sheaves by smooth tensor, so full
   faithfulness and sheaf-Hom gluing promote this coverwise equality to equality globally. The
   etale-precomposition tensor identity then gives the equality for every $K$. Base restrictions
   are already covered by Steps 7 and 8.
   Uses: lem-weil-pbc-etale-composition-cancellation, lem-amb-etale-adjoint-locality, lem-weil-
   pbc-mate-pasting, thm-asd-smooth-tensor, lem-weil-pbc-derived-single-fully-faithful, lem-pur-
   sheaf-hom-cover-gluing, lem-asd-tensor-mate-etale-precomp, prop-asd-smooth-base-change, lem-
   trf-finite-ring-section-deformation, def-amb-vector-integration.

10. Let $P\xrightarrow p X\xrightarrow q Y$ be smooth of dimensions $r,s$. Let
   $c:(qp)^!\xrightarrow{\sim}p^!q^!$ be the counit-preserving comparison. Put
   $u_{p,q}=c^{-1}\phi_{p,\omega_q}:p^*\omega_q\otimes\omega_p\to\omega_{qp}$. Transpose under
   $R(qp)_!\dashv(qp)^!$. The projection-composition identity of [lem-amb-shriek-tensor-
   composition], and the composite counit $\epsilon_q\circ Rq_!\epsilon_p$, identify the transpose
   of $$c^{-1}p^!(\phi_{q,K})\phi_{p,q^*K\otimes\omega_q}$$ with the transpose of
   $\phi_{qp,K}(1\otimes u_{p,q})$. Both are inverse projection for $p$, its unit-object counit,
   inverse projection for $q$, and its counit, in that order. The adjunction bijection gives
   equality. Thus composition for all $\gamma_{p,K}$ reduces to
   $$\alpha_{qp}^{-1}=u_{p,q}(p^*\alpha_q^{-1}\otimes\alpha_p^{-1}),$$ All twists are reassociated
   canonically.
   Uses: lem-amb-shriek-tensor-composition, def-weil-pbc-composite-adjunction, lem-amb-unbounded-
   compact-support-comparisons, lem-weil-pbc-mate-pasting, thm-asd-smooth-tensor.

11. Choose compatible affine charts $U\to\mathbf A^r_V$ for $p$ and $V\to\mathbf A^s_T$ for $q$.
   The composite chart $U\to\mathbf A^{r+s}_T$ is etale, by base change and composition of etale
   maps. Order the $r$ fibre coordinates before the $s$ base coordinates. Step 6 identifies the
   diagonal orientations with the counit-preserving chart adjunction comparisons. The $(r+s)$
   coordinate adjunction and the successive $r$ and $s$ adjunctions have the same Hom bijection:
   the same ordered succession of affine-line Hom bijections, with the same etale Hom bijections.
   Therefore their counits are equal. Coherent compact-support composition and mate pasting
   identify their right-adjoint comparisons; uniqueness of the counit-preserving comparison proves
   the unit equality in Step 10 on these charts. Both sides are maps between equal shifts of rank-
   one locally constant sheaves, so full faithfulness and sheaf gluing give the equality globally.
   Step 10 proves composition for every $K$. The shifts $2r,2s$ are even, so no sign is
   introduced.
   Uses: sbc-thm-etale-local-normal-form, lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-
   etale-composition-cancellation, lem-amb-affine-space-top-trace, def-weil-pbc-composite-
   adjunction, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-mate-pasting, det-sp-
   unique-right-adjoint, thm-asd-smooth-tensor, lem-weil-pbc-derived-single-fully-faithful, lem-
   pur-sheaf-hom-cover-gluing.

12. When $r=0$, smoothness is etaleness. Apply [lem-pur-finite-smooth-gamma-normalization] at the
   given stage $n$. Its three-factor orientation is exactly Step 3 and its tensor composite is
   Step 4. It says that the orientation becomes the identity under the etale sum-adjunction
   identification, and that the tensor composite is the unique right-adjoint comparison preserving
   the sum/evaluation counit. Thus the claimed dimension-zero normalization holds, including
   identity maps, open immersions, nontrivial etale covers and the empty scheme.
   Uses: def-sbc-smooth-morphisms, lem-pur-finite-smooth-gamma-normalization.

13. For coefficient reduction write $A=\Lambda_N$, $B=\Lambda_n$ and $S_T=(-)\otimes_A^LB$. Use
   the canonical compactification coefficient map $b:S_YRp_{!,A}\to Rp_{!,B}S_P$ in [lem-pur-
   exceptional-coefficient-comparison], at the bounded constructible finite-Tor inputs used here.
   Its quotient cocycle is checked with a common compactification: the proper comparison is the
   mate of the scalar/pullback associator, hence consecutive proper comparisons agree by mate
   pasting; the open comparison is the balancing identity $(m\otimes b)\otimes c=m\otimes bc$ on
   the open and zero off it. Pasting gives the cocycle for $b$. Hence the cited coefficient lemma
   defines $c_K:S_Pp_A^!K\to p_B^!S_XK$ by
   $$\epsilon_B\,Rp_{!,B}(c_K)=S_X\epsilon_A\,b_{p_A^!K}^{-1}.$$ We use only $K=A_X$ and the unit
   objects for the diagonal projection, vector bundle and deformation. These are bounded
   constructible finite-Tor; their dualizing objects are shifted locally free rank-one sheaves by
   smooth tensor. The coefficient lemma supplies the tensor and geometric-base-change identities
   for these actual $c$, without assuming $c$ invertible.
   Uses: lem-pur-exceptional-coefficient-comparison, lem-weil-pbc-mate-pasting, lem-weil-pbc-
   ringed-topoi-derived-tensor-pullback, thm-asd-smooth-tensor.

14. At the affine line, compare the Kummer sequences with exponents $\ell^N$ and $\ell^n$. The
   vertical map on their first $\mathbf G_m$ is $u\mapsto u^{\ell^{N-n}}$ and on their last
   $\mathbf G_m$ is the identity; their squares commute since
   $(u^{\ell^{N-n}})^{\ell^n}=u^{\ell^N}$. The kernel map is therefore the power map on roots of
   unity, and the connecting morphism sends the $N$-level first Chern class to the $n$-level
   class. The ordinary supported Kummer class is defined by this boundary and derived scalar
   extension, so the same assertion holds with diagonal support. The Tate lemma identifies
   $S_TA_T(1)$ with $B_T(1)$ by precisely this power map. Tensor powers give all twists used here.
   This is a comparison of the Kummer maps themselves; no tensoring-cohomology assertion with a
   nonflat quotient is used.
   Uses: lem-amb-kummer-any-base, lem-asd-ordinary-supported-kummer, lem-asd-etale-finite-twist-
   pullback.

15. For the projective line let $b_{q,R}:R(1)[2]\oplus R\xrightarrow{\sim}Rq_*R(1)[2]$ be its two-
   summand decomposition, $R=A,B$. Under the proper coefficient comparison, its first summand
   reduces to the shifted twisted unit (transpose the identity), and Step 14 identifies its second
   summand with $c_1(\mathcal O(1))$ over $B$. Thus $S(b_{q,A})$ becomes $b_{q,B}$. Taking inverse
   and the second projection shows that $t_{q,A}$ becomes $t_{q,B}$. The canonical proper
   coefficient map is the projection map after restriction of scalars, by [lem-pur-etale-scalar-
   mate-projection]; it is invertible on these inputs by the proper projection theorem. Open
   extension and the ordered affine-line tower preserve this counit identity, by mate pasting.
   Consequently the affine-space right-adjoint comparison at $A$ reduces to the corresponding $B$
   comparison. On vector-bundle trivializations this proves
   $$z^*(v_{\pi,B}^{-1})\,z^*c_{\pi,A}=S(z^*v_{\pi,A}^{-1}).$$ Both sides are maps between equally
   shifted rank-one $B$-sheaves. Full faithfulness and sheaf gluing give this equality globally.
   The needed projection/coefficient compatibility is the ringed exchange/tensor identity applied
   to the coefficient-change square.
   Uses: lem-asd-ordinary-finite-p1-adjunction, lem-pur-etale-scalar-mate-projection, lem-amb-
   proper-coproducts-projection, lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-weil-
   pbc-ringed-exchange-tensor-coherence, lem-pur-etale-open-derived-tensor, lem-amb-affine-space-
   top-trace, lem-weil-pbc-mate-pasting, thm-amb-vector-bundle-purity, lem-weil-pbc-derived-
   single-fully-faithful, lem-pur-sheaf-hom-cover-gluing.

16. Apply [lem-pur-diagonal-orientation-compatibility] to $(p_1,\Delta)$, with its normalized
   deformation family $F_A,F_B$ and section lines $C_A,C_B$. Take $e_F$ and $e_C$ to be section
   pullbacks of the counit-defined coefficient comparisons of Step 13. Their restrictions at $t=1$
   agree: this is the geometric-base-change identity for $c$ in that lemma, applied to the
   deformation fibre $i_1$. The orientation-compatibility lemma gives
   $$\delta_Be_C=e_0S(\delta_A).$$ It does not require any of these coefficient maps to be
   invertible. The same geometric-base-change identity on the diagonal self-square gives
   $a_{p,B}c_{p,A}=(\Delta^*c_{p_1,A})S(a_{p,A})$. Compose this with the displayed deformation
   equality and the vector equality of Step 15. All middle comparison maps cancel by substitution,
   yielding $$\alpha_{p,B}c_{p,A}=S(\alpha_{p,A}).$$ Multiplying by $S(\alpha_{p,A}^{-1})$ gives
   $c_{p,A}S(\gamma_{p,N})=\gamma_{p,n}$. In particular the coefficient comparison on this unit
   dualizing object is an isomorphism, as a consequence of this equality. This is the requested
   reduction of the specified orientation, with the power-map Tate identification of Step 14.
   Uses: lem-pur-diagonal-orientation-compatibility, lem-pur-exceptional-coefficient-comparison.
-/
theorem noetherianPrimePowerSmoothDuality (ell : ℕ) [Fact ell.Prime] :
    ∃ a : Family.{u} ell, BaseChange ell a ∧ Composition ell a ∧ Reduction ell a := by
  sorry

end AlgebraicGeometry.Etale.NoetherianSmoothDuality
