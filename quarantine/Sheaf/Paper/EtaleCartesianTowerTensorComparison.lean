module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.EtaleMiddleTensorAssembly
import Sheaf.Paper.EtaleTensorSourceTransport
import Sheaf.Paper.EtaleCompositeEComposition

/-! # Dualizing tensor comparison through an etale Cartesian tower

Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1, the
Cartesian-square/two-etale-factors refinement
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison).

All maps use the published canonical etale-origin coordinates for pro-etale Dctf.
The geometry record only packages the hypotheses. In particular its outer square
is not required to be Cartesian. The four equations retain every canonical pullback,
tensor, unit and exceptional-composition comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The hypotheses of the Cartesian tower, bundled without absolute separatedness.
The chosen Cartesian square may be any representative of the stated fibre product.
Source: main-20261015, composition coherence Step 1, etale localization
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
structure EtaleCartesianTower (P : WeilConjectures.PurityFiniteSetting.{u}) where
  B : Scheme.{u}
  T : Scheme.{u}
  A : Scheme.{u}
  Q : Scheme.{u}
  R : Scheme.{u}
  W : Scheme.{u}
  [overB : B.Over (Spec (.of P.field.k))]
  [finiteTypeB : LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
  [quasiCompactB : QuasiCompact (B ↘ Spec (.of P.field.k))]
  [overT : T.Over (Spec (.of P.field.k))]
  [finiteTypeT : LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
  [quasiCompactT : QuasiCompact (T ↘ Spec (.of P.field.k))]
  [overA : A.Over (Spec (.of P.field.k))]
  [finiteTypeA : LocallyOfFiniteType (A ↘ Spec (.of P.field.k))]
  [quasiCompactA : QuasiCompact (A ↘ Spec (.of P.field.k))]
  [overQ : Q.Over (Spec (.of P.field.k))]
  [finiteTypeQ : LocallyOfFiniteType (Q ↘ Spec (.of P.field.k))]
  [quasiCompactQ : QuasiCompact (Q ↘ Spec (.of P.field.k))]
  [overR : R.Over (Spec (.of P.field.k))]
  [finiteTypeR : LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
  [quasiCompactR : QuasiCompact (R ↘ Spec (.of P.field.k))]
  [overW : W.Over (Spec (.of P.field.k))]
  [finiteTypeW : LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
  [quasiCompactW : QuasiCompact (W ↘ Spec (.of P.field.k))]
  q : A ⟶ T
  [overq : q.IsOver (Spec (.of P.field.k))]
  [separatedq : IsSeparated q]
  [finiteTypeq : LocallyOfFiniteType q]
  [quasiCompactq : QuasiCompact q]
  p : T ⟶ B
  [overp : p.IsOver (Spec (.of P.field.k))]
  [separatedp : IsSeparated p]
  [finiteTypep : LocallyOfFiniteType p]
  [quasiCompactp : QuasiCompact p]
  G : Q ⟶ T
  [overG : G.IsOver (Spec (.of P.field.k))]
  [separatedG : IsSeparated G]
  [finiteTypeG : LocallyOfFiniteType G]
  [quasiCompactG : QuasiCompact G]
  qQ : R ⟶ Q
  [overqQ : qQ.IsOver (Spec (.of P.field.k))]
  [separatedqQ : IsSeparated qQ]
  [finiteTypeqQ : LocallyOfFiniteType qQ]
  [quasiCompactqQ : QuasiCompact qQ]
  J : R ⟶ A
  [overJ : J.IsOver (Spec (.of P.field.k))]
  [separatedJ : IsSeparated J]
  [finiteTypeJ : LocallyOfFiniteType J]
  [quasiCompactJ : QuasiCompact J]
  H : W ⟶ R
  [overH : H.IsOver (Spec (.of P.field.k))]
  [separatedH : IsSeparated H]
  [finiteTypeH : LocallyOfFiniteType H]
  [quasiCompactH : QuasiCompact H]
  dq : ℕ
  dp : ℕ
  [smoothq : SmoothOfRelativeDimension dq q]
  [smoothp : SmoothOfRelativeDimension dp p]
  [etaleG : Etale G]
  [etaleH : Etale H]
  square : IsPullback J qQ q G

attribute [instance] EtaleCartesianTower.overB EtaleCartesianTower.finiteTypeB
  EtaleCartesianTower.quasiCompactB
attribute [instance] EtaleCartesianTower.overT EtaleCartesianTower.finiteTypeT
  EtaleCartesianTower.quasiCompactT
attribute [instance] EtaleCartesianTower.overA EtaleCartesianTower.finiteTypeA
  EtaleCartesianTower.quasiCompactA
attribute [instance] EtaleCartesianTower.overQ EtaleCartesianTower.finiteTypeQ
  EtaleCartesianTower.quasiCompactQ
attribute [instance] EtaleCartesianTower.overR EtaleCartesianTower.finiteTypeR
  EtaleCartesianTower.quasiCompactR
attribute [instance] EtaleCartesianTower.overW EtaleCartesianTower.finiteTypeW
  EtaleCartesianTower.quasiCompactW
attribute [instance] EtaleCartesianTower.overq EtaleCartesianTower.separatedq
  EtaleCartesianTower.finiteTypeq EtaleCartesianTower.quasiCompactq
attribute [instance] EtaleCartesianTower.overp EtaleCartesianTower.separatedp
  EtaleCartesianTower.finiteTypep EtaleCartesianTower.quasiCompactp
attribute [instance] EtaleCartesianTower.overG EtaleCartesianTower.separatedG
  EtaleCartesianTower.finiteTypeG EtaleCartesianTower.quasiCompactG
attribute [instance] EtaleCartesianTower.overqQ EtaleCartesianTower.separatedqQ
  EtaleCartesianTower.finiteTypeqQ EtaleCartesianTower.quasiCompactqQ
attribute [instance] EtaleCartesianTower.overJ EtaleCartesianTower.separatedJ
  EtaleCartesianTower.finiteTypeJ EtaleCartesianTower.quasiCompactJ
attribute [instance] EtaleCartesianTower.overH EtaleCartesianTower.separatedH
  EtaleCartesianTower.finiteTypeH EtaleCartesianTower.quasiCompactH
attribute [instance] EtaleCartesianTower.smoothq EtaleCartesianTower.smoothp
  EtaleCartesianTower.etaleG EtaleCartesianTower.etaleH

namespace EtaleCartesianTower
open FiniteEtaleNormalization
variable {P : WeilConjectures.PurityFiniteSetting.{u}} (D : EtaleCartesianTower P)

/-- Etaleness of the actual Cartesian projection, by base-change stability.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
instance etaleJ : Etale D.J :=
  MorphismProperty.of_isPullback D.square.flip inferInstance

/-- The lower smooth composite a, with its actual factors.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev a := D.H ≫ D.qQ

/-- The upper smooth composite b, with its actual factors.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev b := D.G ≫ D.p

/-- The etale composite F; no Cartesian property of the outer square is asserted.
Source: main-20261015, composition coherence Step 1
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev F := D.H ≫ D.J

/-- The actual Cartesian beta is invertible, so the inverses below have their stated meaning.
Source: main-20261015, composition coherence Step 1, refinement proof Step 2
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison).
Proof: etale normalization clause (3) identifies beta with inverse target sigma followed
by inverse normalized E. Target sigma is invertible by the same clause; E and the eta
unit identification are isomorphisms. Thus the displayed beta itself is invertible. -/
theorem beta_isIso : IsIso (beta P D.q D.qQ D.G D.J D.square) := by
  have : Smooth D.q := SmoothOfRelativeDimension.smooth D.dq D.q
  have : Smooth D.qQ := MorphismProperty.of_isPullback D.square inferInstance
  have normalization := finite_etale_dualizing_normalization P D.G
  have := normalization.target_sigma_iso D.q D.qQ D.J D.square
  exact IsIso.of_isIso_fac_right
    (normalization.smooth_base_change D.q D.qQ D.J D.square)

/-- Inverse of the specified Cartesian beta, using its preceding invertibility assertion.
Source: main-20261015, composition coherence Step 1, refinement proof Step 2
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def betaInv :=
  @inv _ _ _ _ (beta P D.q D.qQ D.G D.J D.square) (beta_isIso D)

/-- The canonical commutative-square pullback comparison at omega_p.
Source: main-20261015, composition coherence Step 1, canonical identifications
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def squarePull :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.qQ D.G).inv.app
      (omega P D.p) ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.J D.q
      (D.qQ ≫ D.G) D.square.w.symm).hom.app (omega P D.p)

/-- The equality of the outer composites, using commutativity only.
Source: main-20261015, composition coherence Step 1, a=q_Q H and F=JH
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev outerComm : D.a ≫ D.G = D.F ≫ D.q :=
  (Category.assoc D.H D.qQ D.G).trans
    ((congrArg (fun f ↦ D.H ≫ f) D.square.w.symm).trans
      (Category.assoc D.H D.J D.q).symm)

/-- The canonical outer-square pullback comparison; the square need not be Cartesian.
Source: main-20261015, composition coherence Step 1, final displayed identity
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def outerPull :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.a D.G).inv.app
      (omega P D.p) ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.F D.q
      (D.a ≫ D.G) D.outerComm).hom.app (omega P D.p)

/-- Equality of composites used to type the second displayed identity.
Source: main-20261015, composition coherence Step 1, b=pG
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev middleComm : D.qQ ≫ D.b = D.J ≫ (D.q ≫ D.p) :=
  (Category.assoc D.qQ D.G D.p).symm.trans
    ((congrArg (fun f ↦ f ≫ D.p) D.square.w.symm).trans
      (Category.assoc D.J D.q D.p))

/-- Equality of composites used to type the third displayed identity.
Source: main-20261015, composition coherence Step 1, ba=pqF
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
abbrev totalComm : D.a ≫ D.b = D.F ≫ (D.q ≫ D.p) :=
  (Category.assoc D.a D.G D.p).symm.trans
    ((congrArg (fun f ↦ f ≫ D.p) D.outerComm).trans
      (Category.assoc D.F D.q D.p))

/-- First input factor of the final tensor map: E_H followed by H-pullback of beta inverse.
Source: main-20261015, composition coherence Step 1, final displayed identity
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def finalFirst :=
  (sourceEtale P D.H D.qQ).hom ≫ (pull P D.H).map D.betaInv

/-- Its target is identified with F-pullback using the canonical pullback compositor.
Source: main-20261015, composition coherence Step 1, final displayed identity
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def finalFirstCompared :=
  D.finalFirst ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.H D.J).inv.app
      (omega P D.q)

/-- Assemble the first equality before specializing the coefficient category, so that
all tensor units use the same instance. Every argument is specialized to the specified
map below. Source: main-20261015, composition coherence Step 1, first identity
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def firstEquationModel
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [Etale.UpperStarPreservesFlat C]
    {FC : C → C → Type w} {CC : C → Type (u + 1)}
    [∀ (M N : C), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
    [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]
    {R Q T A : Scheme.{u}} (qQ : R ⟶ Q) (G : Q ⟶ T) (J : R ⟶ A) (q : A ⟶ T)
    [cf : HasCompactification qQ] [ce : HasCompactification G]
    [cfe : HasCompactification (qQ ≫ G)] [cq : HasCompactification q]
    [(Etale.rightDerivedLowerShriek C q).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C qQ).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C G).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C (qQ ≫ G)).IsLeftAdjoint]
    [IsIso (Etale.projectionMap C qQ)]
    (c : Etale.rightDerivedUpperShriek C (qQ ≫ G) ≅
      Etale.rightDerivedUpperShriek C G ⋙ Etale.rightDerivedUpperShriek C qQ)
    (r : Etale.rightDerivedUpperShriek C G ≅ (Etale.upperStar C G).leftDerivedFunctor)
    (e : Etale.dualizingComplex C (qQ ≫ G) ⟶
      (Etale.upperStar C J).leftDerivedFunctor.obj (Etale.dualizingComplex C q))
    (b : Etale.dualizingComplex C qQ ⟶
      (Etale.upperStar C J).leftDerivedFunctor.obj (Etale.dualizingComplex C q)) : Prop :=
  (targetUnit C qQ G r).inv ≫ sigma C qQ G c ≫ e = b

/-- Assemble the two tensor identities over an abstract coefficient category.
Specialization below supplies the actual sigma, normalized E and Cartesian beta.
Source: main-20261015, composition coherence Step 1, second and third identities
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def tensorEquationModel
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [Etale.UpperStarPreservesFlat C]
    {FC : C → C → Type w} {CC : C → Type (u + 1)}
    [∀ (M N : C), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
    [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]
    {R Q T A B : Scheme.{u}} (f : R ⟶ Q) (g : Q ⟶ B)
    (J : R ⟶ A) (q : A ⟶ T) (p : T ⟶ B)
    [cf : HasCompactification f] [cg : HasCompactification g]
    [cfg : HasCompactification (f ≫ g)] [cq : HasCompactification q]
    [cp : HasCompactification p] [cqp : HasCompactification (q ≫ p)]
    [(Etale.rightDerivedLowerShriek C f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C g).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C (f ≫ g)).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C q).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C p).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C (q ≫ p)).IsLeftAdjoint]
    [IsIso (Etale.projectionMap C f)] [IsIso (Etale.projectionMap C q)]
    (c : Etale.rightDerivedUpperShriek C (f ≫ g) ≅
      Etale.rightDerivedUpperShriek C g ⋙ Etale.rightDerivedUpperShriek C f)
    (d : Etale.rightDerivedUpperShriek C (q ≫ p) ≅
      Etale.rightDerivedUpperShriek C p ⋙ Etale.rightDerivedUpperShriek C q)
    (e : Etale.dualizingComplex C (f ≫ g) ⟶
      (Etale.upperStar C J).leftDerivedFunctor.obj (Etale.dualizingComplex C (q ≫ p)))
    (x : Etale.dualizingComplex C f ⟶
      (Etale.upperStar C J).leftDerivedFunctor.obj (Etale.dualizingComplex C q))
    (y : (Etale.upperStar C f).leftDerivedFunctor.obj (Etale.dualizingComplex C g) ⟶
      (Etale.upperStar C J).leftDerivedFunctor.obj
        ((Etale.upperStar C q).leftDerivedFunctor.obj (Etale.dualizingComplex C p))) : Prop :=
  sigma C f g c ≫ e =
    ((Etale.derivedTensor C R).map x).app
        ((Etale.upperStar C f).leftDerivedFunctor.obj (Etale.dualizingComplex C g)) ≫
      ((Etale.derivedTensor C R).obj
        ((Etale.upperStar C J).leftDerivedFunctor.obj (Etale.dualizingComplex C q))).map y ≫
      (Etale.leftDerivedUpperStarTensorIso C J (Etale.dualizingComplex C q)
        ((Etale.upperStar C q).leftDerivedFunctor.obj (Etale.dualizingComplex C p))).inv ≫
      (Etale.upperStar C J).leftDerivedFunctor.map (sigma C q p d)

/-- The first identity, with the eta_G unit identification and square congruence explicit.
Source: main-20261015, composition coherence Step 1, first displayed identity
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def FirstEquation : Prop :=
  firstEquationModel (ModuleCat.{u + 1} P.Coefficient) D.qQ D.G D.J D.q
    (cf := compactification P D.qQ) (ce := compactification P D.G)
    (cfe := compactification P (D.qQ ≫ D.G)) (cq := compactification P D.q)
    (comp P D.qQ D.G) (rho P D.G)
    ((congr P (D.qQ ≫ D.G) (D.J ≫ D.q) D.square.w.symm).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) D.T) ≫
      (sourceEtale P D.J D.q).hom) D.betaInv

/-- The specified SecondEquation with canonical derived comparisons inserted.
Source: main-20261015, composition coherence Step 1, tensor comparison display
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def SecondEquation : Prop :=
  tensorEquationModel (ModuleCat.{u + 1} P.Coefficient) D.qQ D.b D.J D.q D.p
    (cf := compactification P D.qQ) (cg := compactification P D.b)
    (cfg := compactification P (D.qQ ≫ D.b)) (cq := compactification P D.q)
    (cp := compactification P D.p) (cqp := compactification P (D.q ≫ D.p))
    (comp P D.qQ D.b) (comp P D.q D.p)
    ((congr P (D.qQ ≫ D.b) (D.J ≫ (D.q ≫ D.p)) D.middleComm).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) D.B) ≫
      (sourceEtale P D.J (D.q ≫ D.p)).hom)
    D.betaInv
    ((pull P D.qQ).map (sourceEtale P D.G D.p).hom ≫ D.squarePull)

/-- The specified ThirdEquation with canonical derived comparisons inserted.
Source: main-20261015, composition coherence Step 1, tensor comparison display
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def ThirdEquation : Prop :=
  tensorEquationModel (ModuleCat.{u + 1} P.Coefficient) D.a D.b D.F D.q D.p
    (cf := compactification P D.a) (cg := compactification P D.b)
    (cfg := compactification P (D.a ≫ D.b)) (cq := compactification P D.q)
    (cp := compactification P D.p) (cqp := compactification P (D.q ≫ D.p))
    (comp P D.a D.b) (comp P D.q D.p)
    ((congr P (D.a ≫ D.b) (D.F ≫ (D.q ≫ D.p)) D.totalComm).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) D.B) ≫
      (sourceEtale P D.F (D.q ≫ D.p)).hom)
    D.finalFirstCompared
    ((pull P D.a).map (sourceEtale P D.G D.p).hom ≫ D.outerPull)

/-- The asserted formula for E_F itself, using the specified normalized E maps.
Source: main-20261015, composition coherence Step 1, final sentence
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison). -/
def CompositeEEquation : Prop :=
  (sourceEtale P D.F (D.q ≫ D.p)).hom =
    (congr P (D.F ≫ (D.q ≫ D.p)) (D.H ≫ (D.J ≫ (D.q ≫ D.p)))
      (Category.assoc D.H D.J (D.q ≫ D.p))).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) D.B) ≫
    (sourceEtale P D.H (D.J ≫ (D.q ≫ D.p))).hom ≫
    (pull P D.H).map (sourceEtale P D.J (D.q ≫ D.p)).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) D.H D.J).inv.app
      (omega P (D.q ≫ D.p))

private theorem congr_inverse
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f g : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (w : f = g) :
    (FiniteEtaleNormalization.congr P f g w).hom ≫
      (FiniteEtaleNormalization.congr P g f w.symm).hom = 𝟙 _ := by
  subst g
  simp only [FiniteEtaleNormalization.congr, Etale.unboundedEtaleLowerShriekCongr,
    conjugateIsoEquiv_apply_hom, Iso.refl_hom, conjugateEquiv_id, Category.id_comp]

/-- Dualizing tensor comparison through a Cartesian square and two etale factors.
Source: main-20261015, thm-pur-composition-coherence.proof.md, Step 1,
Cartesian-square/two-etale-factors refinement
(blueprint: lem-pur-etale-cartesian-tower-tensor-comparison).

Proof (the six steps of the DAG node):
1. Base-change stability makes J etale; composition makes F etale. Etale maps are
smooth of pure dimension zero, and smooth relative-dimension permanence supplies
q_Q, a, b and all the smooth composites. The square gives qJ=Gq_Q and pqF=ba.
2. Etale normalization clause (3) at (q,q_Q,G,J) gives beta as inverse sigma composed
with inverse E, with eta_G inserted. Invert to obtain FirstEquation.
3. Apply the smooth-triple sigma cocycle to (q_Q,G,p), remove omega_G with eta_G,
and substitute E_G,p sigma_G,p = eta_G tensor identity. Cancel the invertible
input map to express sigma_q_Q,b using sigma_Gq_Q,p and sigma_q_Q,G.
4. The etale-source cocycle at (J,q,p) identifies E_J,pq sigma_qJ,p with
J-pullback of sigma_q,p after tensoring E_J,q. Substitute steps 2 and 3 and use
tensor functoriality. This is SecondEquation with the canonical comparisons shown.
5. Associativity of compact-support composition, passed to adjunction conjugates
by mate pasting, and the composition law for rho_JH identify E_F,pq with
H-pullback of E_J,pq after E_H,pqJ. Naturality of rho_H gives CompositeEEquation.
6. Apply the etale-source identity to (H,q_Q,b), postcompose with H-pullback of
E_J,pq, and use step 5. Pull back step 4 along H. Tensor functoriality and the
canonical pullback compositor give ThirdEquation. Only the original square is
Cartesian; no condition of this kind is used for (F,G).
-/
theorem etale_cartesian_tower_tensor_comparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) (D : EtaleCartesianTower P) :
    D.FirstEquation ∧ D.SecondEquation ∧ D.ThirdEquation ∧ D.CompositeEEquation := by
  have : Smooth D.q := SmoothOfRelativeDimension.smooth D.dq D.q
  have : Smooth D.qQ := MorphismProperty.of_isPullback D.square inferInstance
  have hb := beta_isIso D
  have hn := (finite_etale_dualizing_normalization P D.G).smooth_base_change
    D.q D.qQ D.J D.square
  have first : D.FirstEquation := by
    dsimp only [FirstEquation, firstEquationModel, betaInv]
    apply (cancel_epi (beta P D.q D.qQ D.G D.J D.square)).1
    simp only [IsIso.hom_inv_id]
    rw [reassoc_of% hn]
    have hc := congr_inverse (P := P) (D.J ≫ D.q) (D.qQ ≫ D.G) D.square.w
    have hca := congr_app hc (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) D.T)
    dsimp only [NatTrans.comp_app, NatTrans.id_app] at hca
    erw [reassoc_of% hca]
    simpa only [Category.id_comp] using (sourceEtale P D.J D.q).inv_hom_id
  have : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension D.dq) :=
    smoothOfRelativeDimension_isStableUnderBaseChange D.dq
  have : SmoothOfRelativeDimension D.dq D.qQ :=
    MorphismProperty.of_isPullback D.square inferInstance
  have second : D.SecondEquation := by
    exact etale_middle_tensor_assembly P D.q D.p D.G D.qQ D.J D.dq D.dp
      D.square.w D.betaInv first
  have composite : D.CompositeEEquation := by
    exact etale_composite_e_composition P (D.q ≫ D.p) D.J D.H
  have third : D.ThirdEquation := by
    simpa only [ThirdEquation, tensorEquationModel, finalFirstCompared, finalFirst,
      a, b, F, outerPull, outerComm, totalComm, Category.assoc] using
      (etale_tensor_source_transport P D.q D.p D.G D.qQ D.J D.dq D.dp
        D.square.w D.betaInv D.H second composite)
  exact ⟨first, second, third, composite⟩

end EtaleCartesianTower
end AlgebraicGeometry.ProEtale
