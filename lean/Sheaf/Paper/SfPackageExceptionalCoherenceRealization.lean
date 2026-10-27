module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfCoefficientComparisonConclusions
public import Sheaf.Paper.SfWeilSheafComplex
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.Paper.CompactSupportProjectionFormula
public import Sheaf.Paper.ConstructibleMateCoherence
public import Sheaf.SixFunctors.CoefVerdierWeilEquivariance
import Sheaf.Paper.BoundaryEtaleAdjunctionRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.CompactificationCategory
public import Sheaf.SixFunctors.FiniteExceptionalDomain
public import Sheaf.SixFunctors.FiniteExceptional
import Sheaf.Paper.IntegralResidueTor
import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.SixFunctors.CoefQbarVerdier
public import Sheaf.Paper.SfPackageQbarAdjunctionMapDescent
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.FiniteCoefficientHomChange
public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Paper.IntegralHomReduction
public import Sheaf.SixFunctors.CoefIntegralFiniteExtension
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.DerivedPoincarePairing
public import Sheaf.CategoryTheory.PerfectPairingReductionAdjoints
public import Sheaf.Paper.IntegralExceptionalInverseImage

/-! # Exceptional adjunction and coherence of the constructible package

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, exceptional-adjunction and final coherence sentences
(blueprint: lem-sf-package-exceptional-coherence-realization).

The predicates below spell out the assertions being assembled, using the recorded
operations, their full subcategories, and their original comparison maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The separatedness hypothesis expressed through the canonical scheme-over-base
instance of a bundled space. Source: the standing geometric hypotheses
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
instance sfPackageSpaceSeparated (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated X.obj.hom)

/-- The dual formula on precisely the finite-Tor finite domain and the full higher
constructible domains. Dualizing objects are exceptional images of the coefficient
unit, since these are exactly the four Verdier functors of the operation datum.
The integral realization is the actual coefficient-system construction followed by
its total derived inverse limit, rather than an unbounded pro-etale right adjoint.
Source: blueprint exceptional-adjunction sentence
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
structure SfPackageExceptionalFormulas (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (c : Compactification f.hom.left)
    (cX : Compactification (sixFunctorStructure X).hom.left)
    (cY : Compactification (sixFunctorStructure Y).hom.left) : Prop where
  finiteDomain : ∀ K : sixFunctorFiniteCategory.{u} D C E n hn Y,
    S.finiteTorDomain Y K →
    S.finiteTorDomain X (((@SixFunctorPushStage.exceptional.{u, u + 2, u + 2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun T ↦ inferInstanceAs
        (Category.{u + 2} (sixFunctorFiniteCategory D C E n hn T)))
      S.finite X Y f c)).obj K)
  finiteFormula : Nonempty
    ((S.finiteTorDomain Y).ι ⋙ (@SixFunctorPushStage.exceptional.{u, u + 2, u + 2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun T ↦ inferInstanceAs
        (Category.{u + 2} (sixFunctorFiniteCategory D C E n hn T)))
      S.finite X Y f c) ≅
      (S.finiteTorDomain Y).ι ⋙ (S.finiteVerdier Y cY).rightOp ⋙
        ((@SixFunctorPushStage.pull.{u, u + 2, u + 2} D
          (sixFunctorFiniteCategory D C E n hn)
          (fun T ↦ inferInstanceAs
            (Category.{u + 2} (sixFunctorFiniteCategory D C E n hn T)))
          S.finite X Y f)).op ⋙ S.finiteVerdier X cX)
  integralFormula : Nonempty
    (S.higher.integral.exceptional f c ≅
      (S.integralVerdier Y cY).rightOp ⋙ (S.higher.integral.pull f).op ⋙
        S.integralVerdier X cX)
  integralRealization : Nonempty
    (S.higher.integral.exceptional f c ⋙ (sfIntegralConstructible C.l E X.obj.left).ι ≅
      (sfIntegralConstructible C.l E Y.obj.left).ι ⋙
        integralExceptionalInverseImage C.l E D C.different f.hom.left)
  rationalFormula : Nonempty
    (S.higher.rational.exceptional f c ≅
      (S.rationalVerdier Y cY).rightOp ⋙ (S.higher.rational.pull f).op ⋙
        S.rationalVerdier X cX)
  commonStageFormula : Nonempty
    (S.closure.commonStage.exceptional f c ≅
      (S.commonStageVerdier Y cY).rightOp ⋙ (S.closure.commonStage.pull f).op ⋙
        S.commonStageVerdier X cX)
  finiteClass : ProEtale.FiniteExceptionalDomain.Conclusion C.l E n hn f.hom.left c
  rationalizedAdjunction : RationalOperations.Conclusion D C.l C.different C.Qbar
    X.obj.left Y.obj.left f.hom.left c

open FiniteExceptional

/-- The finite quotients retain their evaluation/trace-normalized dual formula,
quotient cocycle and identity comparison, and the two actual adjunction equations.
The predecessor index m denotes exponent m+1, so exponent zero is never introduced.
Source: blueprint exceptional-adjunction sentence and finite coefficient comparison
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageFiniteExceptionalComparisons
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left] (c : Compactification f.hom.left) : Prop :=
  (∀ n : ℕ, FormulaNormalized C.l E D C.different f.hom.left c n
    (dualFormulaIso C.l E D C.different f.hom.left c n)) ∧
  (∀ {m n : ℕ} (h : n ≤ m), IsIso (b C.l E D C.different f.hom.left c h)) ∧
  (∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
    (L : (domain C.l E Y.obj.left m).FullSubcategory),
    (Q C.l E X.obj.left k).map ((b C.l E D C.different f.hom.left c h).app L) ≫
        (b C.l E D C.different f.hom.left c k).app ((Q C.l E Y.obj.left h).obj L) ≫
        (G C.l E D C.different f.hom.left c t).map ((reassoc C.l E Y.obj.left h k).hom.app L) =
      (reassoc C.l E X.obj.left h k).hom.app ((G C.l E D C.different f.hom.left c m).obj L) ≫
        (b C.l E D C.different f.hom.left c (k.trans h)).app L) ∧
  (∀ (n : ℕ) (L : (domain C.l E Y.obj.left n).FullSubcategory),
    (b C.l E D C.different f.hom.left c (le_refl n)).app L ≫
        (G C.l E D C.different f.hom.left c n).map ((selfReduction C.l E Y.obj.left n).hom.app L) =
      (selfReduction C.l E X.obj.left n).hom.app
        ((G C.l E D C.different f.hom.left c n).obj L)) ∧
  (∀ {m n : ℕ} (h : n ≤ m) (K : (domain C.l E X.obj.left m).FullSubcategory),
    (Q C.l E X.obj.left h).map ((adjunction C.l E D C.different f.hom.left c m).unit.app K) ≫
        (b C.l E D C.different f.hom.left c h).app ((F C.l E D C.different f.hom.left c m).obj K) ≫
        (G C.l E D C.different f.hom.left c n).map
          ((q C.l E D C.different f.hom.left c h).hom.app K) =
      (adjunction C.l E D C.different f.hom.left c n).unit.app ((Q C.l E X.obj.left h).obj K)) ∧
  (∀ {m n : ℕ} (h : n ≤ m) (L : (domain C.l E Y.obj.left m).FullSubcategory),
    (q C.l E D C.different f.hom.left c h).hom.app ((G C.l E D C.different f.hom.left c m).obj L) ≫
        (F C.l E D C.different f.hom.left c n).map ((b C.l E D C.different f.hom.left c h).app L) ≫
        (adjunction C.l E D C.different f.hom.left c n).counit.app
          ((Q C.l E Y.obj.left h).obj L) =
      (Q C.l E Y.obj.left h).map ((adjunction C.l E D C.different f.hom.left c m).counit.app L))

open IntegralFiniteExtension

/-- Scalar-extension evaluation, biduality, identity and composition normalization.
Source: blueprint final coherence sentence and its cited coefficient theorems
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageScalarHom
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L) : Prop :=
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l L X))
      (sE : IntegralVerdier.SignedSymmetry X _ a)
      (sL : IntegralVerdier.SignedSymmetry X _ b)
      (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
      (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n),
      Conclusion l E L ι X D hl wE wL a b sE sL mE mL ∧
      IdentityConclusion l E X D hl wE a ∧ IdentityConclusion l L X D hl wL b ∧
      (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
        (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
        (c : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l F X)),
        CompositionConclusion l E L ι X D hl wE wL a b F j wF c)

open CategoryTheory.MonoidalCategory


/-- Compatibility of the actual geometric pairing, expressed through the three
coefficient squares which define its comparison. These are the cup, evaluation
and normalized-trace squares, rather than a premise that the pairing reduces.
The formal adjoint squares are recorded separately. The source remains site-perfect;
no such hypothesis is used in the general internal-Hom clauses.
Source: thm-pod-finite-reduction.proof.md, composing the three squares
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageGeometricPairingReduction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] : Prop :=
  ∀ (a b : ℕ) (hab : b ≤ a)
    (S : SixFunctorDatum D C E (a + 1) (Nat.succ_le_succ (Nat.zero_le a)))
    (T : SixFunctorDatum D C E (b + 1) (Nat.succ_le_succ (Nat.zero_le b)))
    (O : SfOrientationDatum S) (P : SfOrientationDatum T)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] (d : ℕ)
    [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (hc : GeometricallyConnected X.obj.hom) (hd : X.obj.left.IsPureDimension d)
    (hg : SfPairingGlobalGeometry X)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)
    (L : (T.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)
    (_hL : HEq L.obj.obj ((coefficientFiniteQuotientDerived C.l E X.obj.left hab).obj K.obj.obj))
    (_hK : IsFiniteCoefficientSitePerfect.{u, u} C.l E X.obj.left a K.obj.obj)
    (hKdual : IsFiniteCoefficientSitePerfect.{u, u} C.l E X.obj.left a
      ((S.finiteCoefficientDual X).obj (op K)).obj.obj)
    (hLdual : IsFiniteCoefficientSitePerfect.{u, u} C.l E X.obj.left b
      ((T.finiteCoefficientDual X).obj (op L)).obj.obj),
  let β := S.finitePoincarePairing O X d hc hd hg c K hKdual
  let β' := T.finitePoincarePairing P X d hc hd hg c L hLdual
  let cup := S.finitePairingCup X c (S.sfPairingFiniteTorInput X K)
    (S.sfPairingFiniteTorInput X (S.sfPairingFiniteDualTwist X d K))
  let cup' := T.finitePairingCup X c (T.sfPairingFiniteTorInput X L)
    (T.sfPairingFiniteTorInput X (T.sfPairingFiniteDualTwist X d L))
  let trace := S.finiteNormalizedSmoothTrace O X d c
  let trace' := T.finiteNormalizedSmoothTrace P X d c
  let A := (CategoryTheory.Arrow.mk cup).left
  let B := (CategoryTheory.Arrow.mk cup).right
  let Z := (CategoryTheory.Arrow.mk trace).left
  let A' := (CategoryTheory.Arrow.mk cup').left
  let B' := (CategoryTheory.Arrow.mk cup').right
  let Z' := (CategoryTheory.Arrow.mk trace').left
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (a + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (b + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := pointModuleDerivedExtension (pointFiniteCoefficientQuotient C.l E hab)
  ∀ (q : PointModuleScalarTensorData (pointFiniteCoefficientQuotient C.l E hab) F),
  letI : F.Monoidal := q.strong
  ∀ (v : F.obj B ⟶ B') (w : F.obj Z ⟶ Z')
    (source : F.obj A ⟶ A')
    (middle : B ⟶ Z) (middle' : B' ⟶ Z')
    (_hmiddle : β = cup ≫ middle ≫ trace)
    (_hmiddle' : β' = cup' ≫ middle' ≫ trace')
    (_hcup : source ≫ cup' = F.map cup ≫ v)
    (_hevaluation : v ≫ middle' = F.map middle ≫ w)
    (_htrace : w ≫ trace' = F.map trace ≫ Functor.OplaxMonoidal.η F),
    source ≫ β' = F.map β ≫ Functor.OplaxMonoidal.η F

/-- The geometric-point tensorators and all finite quotient squares are normalized
on K-flat representatives, so the pairing squares above use derived reduction even
for a nonflat quotient and for equal levels.
Source: thm-pod-finite-reduction.proof.md, point perfectness paragraph
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackagePointComparisons
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) : Prop :=
  ∃ T : PointFibreDerivedTensorSystem D C.l C.different C.Qbar,
    Nonempty (PointFibreDerivedTensorCanonical D C.l C.different C.Qbar T)

open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients

/-- The actual compactification, smooth base-change and composition equations
of an orientation family. In particular its base-change equation includes the
geometric-Frobenius squares; the comparison remains the counit mate beta.
Source: fix-prop-coherence, smooth-orientation and field-equivariance clauses
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageOrientationEquations {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type (u + 2)} [∀ X, Category.{u + 2} (B X)]
    {S : SixFunctorPushStage D B} {tensor : ∀ X, B X ⥤ B X ⥤ B X}
    {T : ∀ X, ℕ → B X} (A : SfOrientationTwists S tensor T)
    (P : SfOrientationExchange S tensor T) (o : SfGeometricOrientation A P) : Prop :=
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c c' : Compactification f.hom.left),
    o.component f d c ≪≫ (S.exceptionalComparison f c c').app (T Y 0) =
      o.component f d c') ∧
  (∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (d : ℕ)
    [SmoothOfRelativeDimension d Q.f.hom.left]
    [SmoothOfRelativeDimension d Q.f'.hom.left],
    (o.component Q.f' d Q.compactification').hom =
      (A.pull Q.g' d).inv ≫
        (S.pull Q.g').map (o.component Q.f d Q.compactification).hom ≫ sfOrientationBeta A P Q d) ∧
  (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left]
    [IsSeparated (f ≫ g).hom.left] (d e : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] [SmoothOfRelativeDimension e g.hom.left]
    [SmoothOfRelativeDimension (d + e) (f ≫ g).hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left),
    (o.component (f ≫ g) (d + e) cfg).hom =
      (A.product X d e).inv ≫
        ((tensor X).obj (T X d)).map (A.pull f e).inv ≫
        ((tensor X).map (o.component f d cf).hom).app ((S.pull f).obj (T Y e)) ≫
        sfOrientationTheta A P f d cf e ≫ (S.exceptional f cf).map (o.component g e cg).hom ≫
        (sixFunctorExceptionalComposition S f g cf cg cfg).inv.app (T Z 0))

/-- Higher orientations retain those same geometric equations at every finite
field representative and after common-stage inclusion, and their scalar transition
is the root-normalized one already recorded in the orientation family.
Source: prop-pur-weil-equivariance-compatibilities and fix-prop-coherence
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageSmoothOrientation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] : Prop :=
  ∀ (a : ℕ) (S : SixFunctorDatum D C E (a + 1)
    (Nat.succ_le_succ (Nat.zero_le a))) (O : SfOrientationDatum S),
    SfPackageOrientationEquations _ _ O.higher.higher.integral ∧
    SfPackageOrientationEquations _ _ O.higher.higher.rational ∧
    SfPackageOrientationEquations _ _ O.higher.common ∧
    (∀ L : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageOrientationEquations _ _ (O.higher.coefficients L).integral ∧
      SfPackageOrientationEquations _ _ (O.higher.coefficients L).rational) ∧
    ∀ {L M : Padic.FiniteCoefficientFields C.l C.Qbar} (h : L ≤ M),
      SfStageOrientationCompatible S.closure h
        (O.higher.coefficients L) (O.higher.coefficients M)

/-- Coherence is expressed by the dependency's concrete exchange/pasting equations,
projection diamonds, compactification comparisons and pentagons, on their own domains.
The field clauses lift those very carrier maps to fixed Weil pairs and include
Verdier evaluation, biduality and exceptional adjunction maps. No arbitrary-base-change
claim for duality is present.
Source: blueprint final sentence and fix-prop-coherence
(blueprint: lem-sf-package-exceptional-coherence-realization). -/
def SfPackageComparisonCoherence (S : SixFunctorOperationDatum D C E n hn) : Prop :=
  (∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (a b : ℕ) (h : b ≤ a),
    FiniteHomComparisonConclusion D C.l C.different E X.obj.left a b h) ∧
  (∀ X : SixFunctorSpace D, IntegralHomReductionConclusion C.l E X.obj.left D C.different) ∧
  (∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom],
    CoefQbarVerdierConclusion D C.l C.different C.Qbar X.obj.left) ∧
  (∀ (L : Type u) [Field L] [Algebra (Padic C.l) L]
    [FiniteDimensional (Padic C.l) L] (i : E →ₐ[Padic C.l] L)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (wE : DualizingDatum C.l X.obj.left D C.different E)
    (wL : DualizingDatum C.l X.obj.left D C.different L),
    SfPackageScalarHom C.l E L i X.obj.left D C.different wE wL) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left), ProjectionCoefficientConclusion D C E f c) ∧
  (∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y),
    letI := dlAdicGeometricResidueInvertible D C X.obj.left
    letI := dlAdicGeometricResidueInvertible D C Y.obj.left
    BasicOperationsReductionConclusion C.l E C.Qbar X.obj.left Y.obj.left f.hom.left) ∧
  directImageScalarTowerLaws.{u} ∧ coefficientOperationIdentityLaws.{u} ∧
  PurityFiniteReductionConclusion.{u} ∧ PerfectPairingAdjointsConclusion.{u} ∧
  SfPackageGeometricPairingReduction D C E ∧ SfPackagePointComparisons D C ∧
  SfPackageSmoothOrientation D C E ∧
  CommonStageAdjunctionDescentConclusion.{u} ∧
  exchangeDatumFiniteIdentification D C E n hn S ∧
  exchangeFiniteStageLaws C.l E n hn ∧
  exchangeFiniteCompactIdentification C.l E n hn ∧
  CompletedOrdinaryExchangeLaws (pbcIntegralDatum C.l E) ∧
  CompletedSupportExchangeLaws (pbcIntegralDatum C.l E) ∧
  exchangeCompletedSupportNaturality (pbcIntegralDatum C.l E) ∧
  exchangeRationalSupportLaws C.l E ∧
  exchangeCommonStageSupportLaws.{u, u} C.l C.Qbar ∧
  exchangeScalarCompatibility.{u} C.l ∧
  exchangeCompletedMateLaws C.l E ∧
  exchangeCompletedSquareNaturality C.l E ∧
  coefficientOperationMateEquations.{u} ∧
  compactSupportScalarExtensionLaws.{u} ∧
  CompactSupportFiniteProjection.Laws S.toSixFunctorFiniteOperations ∧
  CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
    S.higher.integralExchange S.integralFiniteTorDomain ∧
  CompactSupportProjectionLaws S.higher.rational S.higher.rationalTensor
    S.higher.rationalExchange (fun _ ↦ ⊤) ∧
  CompactSupportProjectionLaws S.closure.commonStage S.closure.commonStageTensor
    S.closure.commonStageExchange (fun _ ↦ ⊤) ∧
  (∀ m : ℕ, CompactSupportFiniteProjection.Laws
    (S.integralNormalization.finiteLevels m)) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    CompactSupportProjectionLaws (S.closure.coefficientStages E₀).integral
      (S.closure.coefficientStages E₀).integralTensor
      (S.closure.coefficientStages E₀).integralExchange
      (fun X K ↦ finiteTorConstructibleIntegral C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left K.obj) ∧
    CompactSupportProjectionLaws (S.closure.coefficientStages E₀).rational
      (S.closure.coefficientStages E₀).rationalTensor
      (S.closure.coefficientStages E₀).rationalExchange (fun _ ↦ ⊤) ∧
    ∀ m : ℕ, CompactSupportFiniteProjection.Laws
      ((S.coefficientIntegralNormalization E₀).finiteLevels m)) ∧
  (∃ L : PodConstructibleMate.RationalLifts D C E S.higher.rational,
    PodConstructibleMate.RationalCoherence D C E S.higher L) ∧
  (∃ L : PodConstructibleMate.CommonLifts D C S.closure.commonStage,
    PodConstructibleMate.CommonCoherence D C S.closure L) ∧
  ∀ (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom],
    CoefVerdierWeil.Conclusion D C.l C.different C.Qbar X₀

/-- The finite, completed, rationalized and descended exceptional adjunctions and
all proved comparison equations, on their individual constructible domains.

Source: current blueprint prop-functor-package.proof.md, exceptional-adjunction
and final coherence sentences
(blueprint: lem-sf-package-exceptional-coherence-realization).

Proof:
1. The boundary restriction lemma makes the geometric schemes qcqs and Noetherian.
   Nagata supplies a compactification. Finite-type dimension bounds every chosen
   compactifying scheme; the empty scheme has bound zero.
2. Apply lem-sf-package-finite-exceptional-domain to this compactification and bound.
   Its Hom equivalence, units, counits and quotient cocycle are the class-relative ones.
3. Apply lem-coef-finite-exceptional: the evaluation/absolute-trace-normalized formula
   is D_X f* D_Y and the quotient maps satisfy their identity and tower equations,
   as well as both unit/counit equations.
4. By lem-coef-integral-residue-tor, the first reduction controls a single Tor interval
   for every reduction of an integral constructible object. Apply
   prop-coef-integral-exceptional-adjoint to the specified coherent system realization.
   Its total limit is D_X f*_comp D_Y, preserves constructibility, and its finite
   evaluations identify the unit and counit. Its output bound is
   [a-2d_X,b+2d_Y], also when a scheme is empty.
5. lem-coef-rational-operations rationalizes the same integral adjunction. Evaluation,
   units and counits are preserved under all finite field extensions.
6. thm-coef-qbar-verdier supplies the common-stage formula. Apply
   lem-sf-package-qbar-adjunction-map-descent with the normalized scalar comparisons;
   its representative formulas descend the unit, counit, evaluation and triangles.
7. lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction
   and lem-coef-integral-finite-extension preserve the defining evaluation maps.
8. Apply fix-prop-coherence, restricting each equation to the intersection of the
   domains of its two composites. Exchange and projection use their original mate
   constructions. Retain the separate smooth-orientation and site-perfect pairing
   compatibilities; no purity or site-perfectness is imposed on the general Hom.
9. At field stages the canonical maps lift to the fixed-pair Weil categories for
   finite-field models. Their carrier comparisons are the original maps; adjoint
   mates preserve the specified units and counits, and evaluation gives duality
   equivariance. No unbounded ambient right adjoint is used.
-/
theorem sfPackageExceptionalCoherenceRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) :
    (∀ {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
      (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
      [QuasiCompact f.hom.left],
      Nonempty (Compactification f.hom.left) ∧
      ∀ (c : Compactification f.hom.left),
        QuasiCompact c.i ∧
        LocallyOfFiniteType (c.g ≫ Y.obj.hom) ∧ QuasiCompact (c.g ≫ Y.obj.hom) ∧
        (∃ d : ℕ, topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞) ∧
          (IsEmpty c.Z → d = 0)) ∧
        (∀ (cX : Compactification (sixFunctorStructure X).hom.left)
          (cY : Compactification (sixFunctorStructure Y).hom.left),
          SfPackageExceptionalFormulas S f c cX cY) ∧
        SfPackageFiniteExceptionalComparisons D C E f c) ∧
    SfPackageComparisonCoherence S := by
  sorry

end WeilConjectures
