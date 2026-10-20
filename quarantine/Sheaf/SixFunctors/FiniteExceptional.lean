/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.SixFunctors.CoefDualFormulaScalarTranspose

import Sheaf.SixFunctors.FiniteCoefficientVerdier
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.BasicOperationsCoefficientReduction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.CategoryTheory.AbsoluteTraceExchange
import Sheaf.SixFunctors.CompactCoefficientComposition
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientReductionFlatModel
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.DualityPairing
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.FiniteCoefficientHomChange
import Sheaf.Paper.FiniteStageVerdierBiduality
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.SfPreservationClass

/-!
# Finite exceptional inverse image and quotient coefficients

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-coef-finite-exceptional and its proof (blueprint: lem-coef-finite-exceptional).
All indices below are predecessors of positive exponents: index n means A_(n+1).
The functors are restrictions of the published intrinsic pro-etale constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing positive-level finite-Tor constructible predicate.
Source: blueprint finite-Tor domain (blueprint: lem-coef-finite-exceptional). -/
abbrev domain (T : Scheme.{u}) (n : ℕ) :
    ObjectProperty (proEtaleDerivedCategory T
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T

/-- Actual quotient scalar extension, before restriction to finite Tor.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
abbrev reduction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (m + 1)) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  pbcDerivedExtend ((PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1)).map T)

/-- Finite-Tor constructibility survives the actual quotient tensor.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: use lem-sf-flat-model and lem-sf-reduction-flat-model to reduce a bounded flat
model; it stays flat over the quotient in the same interval. Constructible cohomology
follows from lem-pur-finite-tensor-constructible-cohomology. A finite module killed by
the quotient kernel is finite over the quotient; its locally constant descriptions
are quotient-linear since every quotient scalar lifts. -/
theorem reduction_preserves (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : (domain l E T m).FullSubcategory) :
    domain l E T n ((reduction l E T h).obj K.obj) := by
  sorry

/-- Restriction of the actual quotient tensor, with unchanged morphisms.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
def Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (domain l E T m).FullSubcategory ⥤ (domain l E T n).FullSubcategory :=
  (domain l E T n).lift ((domain l E T m).ι ⋙ reduction l E T h)
    (reduction_preserves l E T h)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

include D hl Xbase Ybase Xft Xqc Yft Yqc Xsep Ysep fbase fsep fft fqc in
/-- The two specified finite functors preserve their constructible finite-Tor domains.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional).
Proof: write compact support as Rp_* j_!. Apply lem-trf-open-ctf, then
cor-sf-direct-image-ctf-proetale, using lem-kun-dimension-finite-type on the proper
compactification. Every constructible input has etale origin and the same Tor interval
by lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude.
thm-sf-ambient-adjoint-class supplies the constructible adjunction and
thm-sf-preservation-class supplies finite-Tor preservation of its specified right
adjoint. Empty schemes and empty chart families use dimension bound zero. -/
theorem operations_preserve (n : ℕ) :
    (∀ K : (domain l E X n).FullSubcategory,
      domain l E Y n ((sfIntrinsicCompactSupport c
        (Padic.coefficientExtensionRing l E (n + 1))).obj K.obj)) ∧
    (∀ L : (domain l E Y n).FullSubcategory,
      domain l E X n ((ProEtale.sfFiniteExceptional
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj)) := by
  sorry

/-- Rf_! is the restriction of the specified compactification construction.
Source: blueprint F_r (blueprint: lem-coef-finite-exceptional). -/
def F (n : ℕ) :
    (domain l E X n).FullSubcategory ⥤ (domain l E Y n).FullSubcategory :=
  (domain l E Y n).lift ((domain l E X n).ι ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    (operations_preserve l E D hl f c n).1

/-- Rf^! is the restriction of Rnu_* followed by the etale adjoint and nu^*.
Source: blueprint G_r (blueprint: lem-coef-finite-exceptional). -/
def G (n : ℕ) :
    (domain l E Y n).FullSubcategory ⥤ (domain l E X n).FullSubcategory :=
  (domain l E X n).lift ((domain l E Y n).ι ⋙
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c)
    (operations_preserve l E D hl f c n).2

/-- The recorded Verdier dual into the actual structural exceptional image of the unit.
Source: blueprint omega and D (blueprint: lem-coef-finite-exceptional). -/
def dual (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] (n : ℕ) :
    (proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)))ᵒᵖ ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Functor.curry.obj (finiteIntrinsicDerivedInternalHom l E T n)).flip.obj
    (integralDualizingFiniteTerm l E D T n)

/-- The double-dual pullback formula as an actual covariant ambient functor.
Source: blueprint first display (blueprint: lem-coef-finite-exceptional). -/
def H (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (dual l E D Y n).rightOp ⋙ (finiteDerivedPullback l E n f).op ⋙ dual l E D X n

/-- The canonical compact-support scalar mate, in the intrinsic realization.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def supportMap {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        reduction l E Y h ⟶
      reduction l E X h ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.whiskerRight (PurCompactSupport.finiteImageIso l E m c).inv
      (reduction l E Y h) ≫
    PurCompactSupport.comparison (PurCompactSupport.finiteQuotientChange l E
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1)) c ≫
    Functor.whiskerLeft (reduction l E X h)
      (PurCompactSupport.finiteImageIso l E n c).hom

/-- Quotient composition as an equality of actual constant-ring maps.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction sends both composites to the same residue class.
The constant-sheaf functor preserves this equality, including equal indices. -/
theorem quotient_comp (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map T ≫
      (PurCompactSupport.finiteQuotientChange l E (n + 1) (t + 1)
        (Nat.succ_pos n) (Nat.succ_pos t) (Nat.add_le_add_right k 1)).map T =
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (t + 1)
      (Nat.succ_pos m) (Nat.succ_pos t) (Nat.add_le_add_right (k.trans h) 1)).map T := by
  sorry

/-- The identical quotient induces the identity map of coefficient sheaves.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction gives identity on each residue class, and constant
sheafification preserves identities. -/
theorem quotient_id (T : Scheme.{u}) (n : ℕ) :
    (PurCompactSupport.finiteQuotientChange l E (n + 1) (n + 1)
      (Nat.succ_pos n) (Nat.succ_pos n) (Nat.add_le_add_right (le_refl n) 1)).map T =
      𝟙 _ := by
  sorry

/-- Actual tensor associativity restricted through the full finite-Tor inclusion.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional). -/
def reassoc (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    Q l E T h ⋙ Q l E T k ≅ Q l E T (k.trans h) :=
  Functor.fullyFaithfulCancelRight (domain l E T t).ι
    (Functor.isoWhiskerLeft (domain l E T m).ι
      (PurCompactSupport.tensorComposition _ _ _ (quotient_comp l E T h k)))

/-- Actual multiplication unit for self reduction, restricted to finite Tor.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional). -/
def selfReduction (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (domain l E T n).ι
    (Functor.isoWhiskerLeft (domain l E T n).ι
      (eqToIso (congrArg pbcDerivedExtend (quotient_id l E T n)) ≪≫
        PurCompactSupport.tensorIdentity _))

/-- Brown representability for the specified ordinary etale compact-support candidate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
instance fixedSupport_isLeftAdjoint (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c

/-- The specified fixed-scalar exceptional realization is identified with the
right adjoint of the very same compactification by uniqueness of right adjoints.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedExceptionalIso (n : ℕ) :
    ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
  letI := c.hasCompactification
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft _
      ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _

/-- The canonical fixed-scalar Hom bijection, with an arbitrary retained etale origin.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedHom (n : ℕ)
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    ((ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      M.obj ⟶ L.obj) ≃
      (M.obj ⟶ (ProEtale.sfFiniteExceptionalFixed
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj) :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  (ProEtale.specifiedExceptionalHomEquiv _ c M W L).trans
    ((fixedExceptionalIso l E f c n).symm.app L.obj).homToEquiv

/-- The normalization on every etale-origin representative fixes the adjunction,
including its units and counits. There is no choice of adjunction in this predicate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def AdjunctionNormalized (n : ℕ) (a : F l E D hl f c n ⊣ G l E D hl f c n) : Prop :=
  ∀ (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (hM : domain l E X n
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        M.obj))
    (hL : domain l E Y n
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        L.obj))
    (v : (ProEtale.sfFixedCompactSupport
      (Padic.coefficientExtensionRing l E (n + 1)) c).obj M.obj ⟶ L.obj),
    (a.homEquiv ⟨_, hM⟩ ⟨_, hL⟩
      (ObjectProperty.homMk
        ((ProEtale.sfIntrinsicCompactSupportComparison _ c).hom.app M.obj ≫
          (sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).functor.map v))).hom =
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (fixedHom l E D f c n M W L v ≫
            (ProEtale.sfFiniteExceptionalFixed
              (Padic.coefficientExtensionRing l E (n + 1)) c).map
                ((sfIntrinsicDerivedEquivalence Y
                  (Padic.coefficientExtensionRing l E (n + 1))).unitIso.hom.app L.obj))

/-- The constructible adjunction is uniquely fixed by the recorded bounded Hom chain.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional).
Proof: lem-sf-proetale-constructible-origin supplies a bounded etale representative
for every constructible input. Transport specifiedExceptionalHomEquiv through the
canonical coefficient realizations. Its naturality supplies Adjunction.mkOfHomEquiv.
Full faithfulness and independence of the representative give the displayed
normalization for every witness. Each Hom bijection is therefore determined, so the
adjunction is unique. Preservation and Tor domains are operations_preserve. -/
theorem adjunction_existsUnique (n : ℕ) :
    ∃! a : F l E D hl f c n ⊣ G l E D hl f c n,
      AdjunctionNormalized l E D hl f c n a := by
  sorry

/-- The specified constructible adjunction, selected only by its unique Hom normalization.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def adjunction (n : ℕ) : F l E D hl f c n ⊣ G l E D hl f c n :=
  (adjunction_existsUnique l E D hl f c n).choose

/-- The finite constant-ring pull identifications respect compactification composition.
Source: blueprint proof step 3, projection construction
(blueprint: lem-coef-finite-exceptional).
Proof: the canonical inverse-image comparison sends every constant section to itself.
The inverse-image composition comparison has the same action. The constant-sheaf
universal property identifies the two ring maps, hence their isomorphisms. -/
theorem finitePull_comp (n : ℕ) :
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ c.g) =
      proEtaleRingCompositeCoefficients c.i c.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i) := by
  sorry

/-- The ordinary pullback presentation comparison, descended termwise. It is fixed
by the constant-section adjunction, before any exceptional formula is considered.
Source: blueprint proof step 3, ordinary pullback
(blueprint: lem-coef-finite-exceptional). -/
def formulaPullIso (n : ℕ) :
    PurCompactSupport.pull (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) f ≅
      finiteDerivedPullback l E n f := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive _ f
  letI : HasDerivedCategory (proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  exact Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (D := proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1))))
    (PurCompactSupport.finitePullbackIso.{u} l E n f)

/-- Evaluation and absolute-trace normalization of the finite dual-formula comparison.
All tensor presentations have their existing K-flat/evaluation normalization, and
sX is the descended Koszul symmetry. The trace is the existing structural-counit
transpose through compact-support composition, transported by the canonical site
comparisons. Thus this equation excludes rescaling the dual-formula isomorphism.
Source: blueprint proof steps 3--5; finite analogue of FormulaNormalized in
CoefDualFormulaScalarTranspose (blueprint: lem-coef-finite-exceptional). -/
def FormulaNormalized (n : ℕ)
    (k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n) : Prop :=
  ∀ (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (L : (domain l E Y n).FullSubcategory),
    ((PurCompactSupport.projectionMap
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (finitePull_comp l E f c n)).app ((G l E D hl f c n).obj L).obj).app
        ((dual l E D Y n).obj (op L.obj)) ≫
      (PurCompactSupport.image
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map
        (aX.tensor.map (Prod.mkHom (𝟙 _)
          ((formulaPullIso l E f n).hom.app ((dual l E D Y n).obj (op L.obj)))) ≫
          (sX.swap ((G l E D hl f c n).obj L).obj
            ((finiteDerivedPullback l E n f).obj
              ((dual l E D Y n).obj (op L.obj)))).hom ≫
          aX.tensor.map (Prod.mkHom (𝟙 _) (k.hom.app L)) ≫
          (aX.adjunction ((finiteDerivedPullback l E n f).obj
            ((dual l E D Y n).obj (op L.obj)))).counit.app
              (integralDualizingFiniteTerm l E D X n)) ≫
      (PurCompactSupport.finiteImageIso l E n c).hom.app
        (integralDualizingFiniteTerm l E D X n) ≫
      CoefDualFormulaScalarTranspose.finiteTrace D l E f c n =
    aY.tensor.map (Prod.mkHom
      ((PurCompactSupport.finiteImageIso l E n c).hom.app
        ((G l E D hl f c n).obj L).obj ≫
        ((adjunction l E D hl f c n).counit.app L).hom) (𝟙 _)) ≫
      (aY.tensor.map (Prod.mkHom (𝟙 L.obj) (𝟙 _))) ≫
      (aY.adjunction L.obj).counit.app (integralDualizingFiniteTerm l E D Y n)

/-- The finite dual formula has a unique evaluation/trace-normalized natural isomorphism.
Source: blueprint proof steps 2--5 (blueprint: lem-coef-finite-exceptional).
Proof: finite Verdier biduality and pullback Tor preservation put H in the domain.
Form the structural relative trace by transposing the absolute counit through support
composition. Projection, the ordinary counit and evaluation define the exchange
pairing. The absolute-trace-exchange lemma identifies its Hom action and proves it
invertible. Biduality, the ordinary adjunction, this exchange and biduality give the
four natural Hom bijections displayed in the blueprint. They make H a right adjoint
to F. Uniqueness of right adjoints compares it with the specified adjunction F ⊣ G.
Uncurrying the image of its counit gives exactly the displayed normalization, for
every normalized tensor presentation. Conversely, tensor-Hom injectivity, projection
invertibility on the finite-Tor domain and Verdier duality force each component from
this equation. Naturality then gives uniqueness of the natural isomorphism. -/
theorem dualFormula_existsUnique (n : ℕ) :
    ∃! k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n,
      FormulaNormalized l E D hl f c n k := by
  sorry

/-- The canonical finite dual formula, chosen only from its unique evaluation/trace
normalization. Source: blueprint proof step 5
(blueprint: lem-coef-finite-exceptional). -/
def dualFormulaIso (n : ℕ) :
    G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n :=
  (dualFormula_existsUnique l E D hl f c n).exists.choose

/-- The compact-support comparison restricted through the full inclusion.
Its orientation is Q_Y F_m to F_n Q_X, as in the displayed unit/counit identities.
Source: blueprint second paragraph (blueprint: lem-coef-finite-exceptional). -/
def qMap {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ⟶ Q l E X h ⋙ F l E D hl f c n :=
  ((domain l E Y n).fullyFaithfulι.whiskeringRight
    (domain l E X m).FullSubcategory).preimage
    (Functor.whiskerLeft (domain l E X m).ι (supportMap l E f c h))

/-- The actual compact-support comparison is invertible on the stated domain.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: lem-fix-compact-support-coefficient-change gives invertibility on the etale
origin of every bounded constructible finite-Tor input. The canonical intrinsic
realization preserves this comparison. The full inclusion reflects isomorphisms. -/
theorem qMap_isIso {m n : ℕ} (h : n ≤ m) : IsIso (qMap l E D hl f c h) := by
  sorry

/-- The canonical compact-support coefficient isomorphism.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def q {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ≅ Q l E X h ⋙ F l E D hl f c n :=
  @asIso _ _ _ _ (qMap l E D hl f c h) (qMap_isIso l E D hl f c h)

/-- The exceptional coefficient map is the counit transpose of inverse q. This
formula fixes the map itself before its invertibility, rather than choosing an
isomorphism. Source: blueprint proof paragraphs 2 and 3
(blueprint: lem-coef-finite-exceptional). -/
def b {m n : ℕ} (h : n ≤ m) :
    G l E D hl f c m ⋙ Q l E X h ⟶ Q l E Y h ⋙ G l E D hl f c n :=
  mateEquiv (adjunction l E D hl f c m) (adjunction l E D hl f c n)
    (q l E D hl f c h).inv

/-- Finite exceptional duality and the coherent, adjunction-normalized quotient maps.
Source: current blueprint sk-thm-sf-package, lem-coef-finite-exceptional and its proof
(blueprint: lem-coef-finite-exceptional).
Proof:
1. operations_preserve and the normalized bounded Hom chain give F_r adjoint G_r.
2. thm-fix-general-biduality and lem-sf-pullback-tor-amplitude put D_X f* D_Y in the
finite-Tor domain. Tensor closure follows from flat models and finite constructible
cohomology. Tensor-Hom transposition and H^0 of internal Hom give the Hom bijections.
3. Form the absolute trace transpose using compact-support composition and the
structure-map counit. Projection, the ordinary pullback counit and evaluation give
its exchange pairing. lem-sf-absolute-trace-exchange proves that this specified
exchange is invertible and identifies its Hom action.
4. The four Hom bijections (biduality, ordinary adjunction, exchange, biduality)
make D_X f* D_Y a right adjoint. Uniqueness of right adjoints gives the natural
first isomorphism with the already specified G, including its unit and counit.
5. Reduction preserves finite Tor by bounded flat models. Apply the coherent
Verdier coefficient comparisons to both duals and commute reduction past f*.
Contravariance uses the inverse of the inner comparison. Their cocycles and
naturality give the quotient cocycle for this comparison of the dual formulas.
6. Absolute dualizing coefficient change preserves the trace, by its counit
identity and compact-support composition. General finite Hom coefficient change
preserves evaluation. Projection and compact-support coefficient change preserve
the ordinary counit. Hence the transposed four Hom bijections give exactly inverse
q followed by reduction of the old counit. Thus their b is the mate defined above.
7. Mate pasting gives the displayed unit and counit equations. The dual comparison
makes b invertible. Its quotient cocycle descends from the two coherent dual
comparisons; equal indices give the scalar multiplication unit, with its required
endpoint identifications. All indices n denote the positive exponent n+1. -/
theorem finite_exceptional :
    (∀ n : ℕ, FormulaNormalized l E D hl f c n
      (dualFormulaIso l E D hl f c n)) ∧
    (∀ {m n : ℕ} (h : n ≤ m), IsIso (b l E D hl f c h)) ∧
    (∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (L : (domain l E Y m).FullSubcategory),
      (Q l E X k).map ((b l E D hl f c h).app L) ≫
          (b l E D hl f c k).app ((Q l E Y h).obj L) ≫
          (G l E D hl f c t).map ((reassoc l E Y h k).hom.app L) =
        (reassoc l E X h k).hom.app ((G l E D hl f c m).obj L) ≫
          (b l E D hl f c (k.trans h)).app L) ∧
    (∀ (n : ℕ) (L : (domain l E Y n).FullSubcategory),
      (b l E D hl f c (le_refl n)).app L ≫
          (G l E D hl f c n).map ((selfReduction l E Y n).hom.app L) =
        (selfReduction l E X n).hom.app ((G l E D hl f c n).obj L)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (K : (domain l E X m).FullSubcategory),
      (Q l E X h).map ((adjunction l E D hl f c m).unit.app K) ≫
          (b l E D hl f c h).app ((F l E D hl f c m).obj K) ≫
          (G l E D hl f c n).map ((q l E D hl f c h).hom.app K) =
        (adjunction l E D hl f c n).unit.app ((Q l E X h).obj K)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (L : (domain l E Y m).FullSubcategory),
      (q l E D hl f c h).hom.app ((G l E D hl f c m).obj L) ≫
          (F l E D hl f c n).map ((b l E D hl f c h).app L) ≫
          (adjunction l E D hl f c n).counit.app ((Q l E Y h).obj L) =
        (Q l E Y h).map ((adjunction l E D hl f c m).counit.app L)) := by
  sorry

end WeilConjectures.FiniteExceptional
