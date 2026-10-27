module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Sheaf.Paper.ExceptionalInverseImageExistence
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
public import Sheaf.SecSmoothPurity.ReductionCompatibilities
public import Sheaf.Paper.SmoothPurityCompositionFactors
public import Sheaf.Paper.SmoothPurityBaseChangeFactors
public import Sheaf.Paper.FiniteReductionOfPurity
public import Sheaf.Paper.ProjectionPurityAgreement
public import Sheaf.Paper.VectorTraceScalarDescent
public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.SmoothTrace
import Sheaf.SecSmoothPurity.ReductionDirectImage
import Sheaf.SecSmoothPurity.ReductionExceptional
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose
import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility

/-! # The normalized finite-coefficient purity counit system

Source: latest blueprint, sec-smooth-purity/sk-thm-purity-transport, Steps 1, 3 and 4
(blueprint: lem-pur-transport-finite-counit-system).

The ordinary finite-module presentation is identified with condensed modules by the
section-action derived equivalence. All operations below are the recorded pro-etale
operations in these coordinates. A system includes actual adjunctions, their specified
counits, and the canonical coefficient, geometric and integration identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FinitePurityCounit
open WeilConjectures.PurityFiniteSetting
open Etale.FiniteSmoothPurity

/-- One actual adjunction F dashv J, compared to the specified exceptional adjunction.
Both counits are fixed morphisms, and the natural purity isomorphism has the prescribed
three-factor components. The full subcategories use the recorded intrinsic IsCtf predicate.
Source: latest blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-transport-finite-counit-system). -/
structure AdjunctionAt (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : Etale.DerivedCategoryModule A X)
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L) where
  compact_closed : ∀ M, IsCtf A X M → IsCtf A Y ((proCompact A f).obj M)
  source_closed : ∀ K, IsCtf A Y K → IsCtf A X ((proSource A f L).obj K)
  exceptional_closed : ∀ K, IsCtf A Y K → IsCtf A X ((exceptional A f).obj K)
  exceptionalAdjunction :
    ObjectProperty.lift (IsCtf A Y) (ObjectProperty.ι (IsCtf A X) ⋙ proCompact A f)
        (fun M ↦ compact_closed M.obj M.property) ⊣
      ObjectProperty.lift (IsCtf A X) (ObjectProperty.ι (IsCtf A Y) ⋙ exceptional A f)
        (fun K ↦ exceptional_closed K.obj K.property)
  exceptional_counit : ∀ K : ObjectProperty.FullSubcategory (IsCtf A Y),
    (exceptionalAdjunction.counit.app K).hom = proCounit A f K.obj
  adjunction :
    ObjectProperty.lift (IsCtf A Y) (ObjectProperty.ι (IsCtf A X) ⋙ proCompact A f)
        (fun M ↦ compact_closed M.obj M.property) ⊣
      ObjectProperty.lift (IsCtf A X) (ObjectProperty.ι (IsCtf A Y) ⋙ proSource A f L)
        (fun K ↦ source_closed K.obj K.property)
  purity :
    ObjectProperty.lift (IsCtf A X) (ObjectProperty.ι (IsCtf A Y) ⋙ proSource A f L)
        (fun K ↦ source_closed K.obj K.property) ≅
      ObjectProperty.lift (IsCtf A X) (ObjectProperty.ι (IsCtf A Y) ⋙ exceptional A f)
        (fun K ↦ exceptional_closed K.obj K.property)
  purity_components : ∀ K : ObjectProperty.FullSubcategory (IsCtf A Y),
    (purity.hom.app K).hom = proGamma A f L alpha K.obj
  counit : ∀ K : ObjectProperty.FullSubcategory (IsCtf A Y),
    (adjunction.counit.app K).hom = proTrace A f L alpha K.obj
  unit : ∀ M : ObjectProperty.FullSubcategory (IsCtf A X),
    adjunction.unit.app M = exceptionalAdjunction.unit.app M ≫
      purity.inv.app
        ((ObjectProperty.lift (IsCtf A Y) (ObjectProperty.ι (IsCtf A X) ⋙ proCompact A f)
          (fun M ↦ compact_closed M.obj M.property)).obj M)
  site_trace : ∀ (K₀ : Etale.DerivedCategoryModule A Y),
    Etale.DerivedCategory.boundedConstructibleFiniteTor A Y K₀ →
    ∀ (K : proCategory A Y), IsCtf A Y K → ∀ e : (comparison A Y).obj K₀ ≅ K,
      (proCompact A f).map
          ((sourceAtOriginIso A f L K₀).hom ≫ (proSource A f L).map e.hom) ≫
          proTrace A f L alpha K =
        compactSiteMap A f ((puritySource A f L).obj K₀) ≫
          (comparison A Y).map (trace A f L alpha K₀) ≫ e.hom

/-- The actual scalar associator, normalized by multiplication on balanced tensors.
Source: latest blueprint sk-thm-purity-transport, Step 1 coefficient transitivity
(blueprint: lem-pur-transport-finite-counit-system). -/
def scalarAssociator {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (phi : A →+* B) (psi : B →+* C) (T : Scheme.{u}) :
    proScalar phi T ⋙ proScalar psi T ≅ proScalar (psi.comp phi) T :=
  @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
    A B C inferInstance inferInstance inferInstance phi psi (psi.comp phi) rfl

/-- Integration on the ordered affine coordinate tower, on the Tate-line source.
The inverse descent and normalized pullback take the line to the same coordinate
right-adjoint input used by the projective-trace/open-extension construction. The
final factor is the inverse compact-support comparison followed by the counit of the
ordered affine-trace adjunction built from projective-line integration; this is the
same composite that lem-pur-vector-trace-scalar-descent names `affineTrace`.
Source: latest blueprint sk-thm-purity-transport, Step 4
(blueprint: lem-pur-transport-finite-counit-system). -/
@[irreducible]
def affineIntegration (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (line A N hA (affineTraceTower S d) d) ⟶ Etale.ordinaryFiniteUnit A S :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).map
        (((Etale.affineLinearCoefficientDescent A N hA
            (Etale.projectiveLineTraceTransport N hN A hA) S hS d) ≪≫
          Etale.vectorIntegrationBaseCoefficientPullback A N hA
            (Etale.projectiveLineTraceTransport N hN A hA)
            (affineTraceProjection S d) hS d).inv) ≫
    (Etale.affineLinearCompactComparison N hN A hA S hS d).inv ≫
    Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
      (Etale.projectiveLineTraceDatum N hN A hA) S hS d

/-- Inverse coefficient-first projection followed by one tensor integration.
It uses the same ordered projection as the tensor-transpose definition of gamma.
Source: latest blueprint sk-thm-purity-transport, Step 4
(blueprint: lem-pur-transport-finite-counit-system). -/
@[irreducible]
def affineIntegrationCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        ((puritySource A (affineTraceProjection S d)
          (line A N hA (affineTraceTower S d) d)).obj K) ⟶ K := by
  letI := Etale.isIso_projectionMap_of_finite A (affineTraceProjection S d)
  exact
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (affineTraceTower S d)).hom.app
            ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K)).app
              (line A N hA (affineTraceTower S d) d)) ≫
      ((inv (Etale.projectionMap (ModuleCat.{u + 1} A)
        (affineTraceProjection S d))).app
          (line A N hA (affineTraceTower S d) d)).app K ≫
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection S d)).obj
            (line A N hA (affineTraceTower S d) d))).app K ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
        (affineIntegration A N hN hA S hS d) ≫
      (Etale.derivedTensorSingleUnitIso K).hom

/-- All clauses of the normalized finite system. The constituent equations are
written with the dependency declarations, including the actual canonical b, c and a.
The geometric and finite-reduction fields are the original constituent identities;
they therefore constrain these same diagonal/DNC-normalized purity maps.
Source: latest blueprint sk-thm-purity-transport, Steps 1, 3 and 4
(blueprint: lem-pur-transport-finite-counit-system). -/
structure System : Prop where
  adjunctions : ∀
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0),
    ∃ (hX : IsNoetherian X) (hY : IsNoetherian Y) (hqc : QuasiCompact f)
      (hc : HasCompactification f),
      letI := hX
      letI := hY
      letI := hqc
      letI := hc
      ∃ (geometry : Etale.FiniteRingSectionDeformation.Geometry d
            (pullback.fst f f) (pullback.diagonal f))
          (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
            line A (ell ^ n) hA X d),
          OrientationNormalized A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
            hA f d geometry
            ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
              (X ↘ Spec (.of D.k))) alpha ∧
          Nonempty (AdjunctionAt A f _ alpha) ∧
          FiniteGeneralRingLevelIndependence A ell n hA d f geometry
            (fun m hm ↦ ({ finiteGeneralRingPrimeSetting D ell hne n hn with
              level := m, level_pos := hm } : PurityFiniteSetting).diagonalExponent_isUnit
                (X ↘ Spec (.of D.k))) alpha
  coefficient : ∀
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [QuasiCompact f] [HasCompactification f]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (n : ℕ) (hn : 1 ≤ n)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A (ell ^ n) hA X d)
    (beta : Etale.dualizingComplex (ModuleCat.{u + 1} B) f ≅ line B (ell ^ n) hB X d)
    (_ha : OrientationNormalized A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      hA f d geometry ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alpha)
    (_hb : OrientationNormalized B (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      hB f d geometry ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) beta),
    ∃ e : CoefficientLineComparison phi (ell ^ n) (ell ^ n) hA hB X,
      ∀ (K : proCategory A Y), IsCtf A Y K →
        IsCtf B Y ((proScalar phi Y).obj K) ∧ IsIso (proLambda f d e K) ∧
        IsIso (proCoefficientMap phi f K) ∧
        IsIso (proCompactCoefficientMap phi f ((proSource A f (line A (ell ^ n) hA X d)).obj K)) ∧
        ((proScalar phi X).map (proGamma A f _ alpha K) ≫ proCoefficientMap phi f K =
          proLambda f d e K ≫ proGamma B f _ beta ((proScalar phi Y).obj K)) ∧
        ((proCompact B f).map (proLambda f d e K) ≫
            proTrace B f _ beta ((proScalar phi Y).obj K) =
          proCompactCoefficientInverse phi f ((proSource A f (line A (ell ^ n) hA X d)).obj K) ≫
            (proScalar phi Y).map (proTrace A f _ alpha K)) ∧
        ∀ (a : AdjunctionAt A f _ alpha) (b : AdjunctionAt B f _ beta)
          (M : ObjectProperty.FullSubcategory (IsCtf A X))
          (hM : IsCtf B X ((proScalar phi X).obj M.obj)),
          (proScalar phi X).map (a.adjunction.unit.app M).hom ≫
              proLambda f d e ((proCompact A f).obj M.obj) ≫
              (proSource B f (line B (ell ^ n) hB X d)).map (proCompactCoefficientMap phi f M.obj) =
            (b.adjunction.unit.app ⟨_, hM⟩).hom
  transitive : ∀
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [QuasiCompact f] [HasCompactification f]
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (phi : A →+* B) (psi : B →+* C)
    (n : ℕ) (_hn : 1 ≤ n) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0) (hC : ((ell ^ n : ℕ) : C) = 0)
    (eAB : CoefficientLineComparison phi (ell ^ n) (ell ^ n) hA hB X)
    (eBC : CoefficientLineComparison psi (ell ^ n) (ell ^ n) hB hC X)
    (eAC : CoefficientLineComparison (psi.comp phi) (ell ^ n) (ell ^ n) hA hC X)
    (K : proCategory A Y), IsCtf A Y K →
      ((proScalar psi X).map (proLambda f d eAB K) ≫
          proLambda f d eBC ((proScalar phi Y).obj K) ≫
          (proSource C f (line C (ell ^ n) hC X d)).map ((scalarAssociator phi psi Y).hom.app K) =
        (scalarAssociator phi psi X).hom.app ((proSource A f (line A (ell ^ n) hA X d)).obj K) ≫
          proLambda f d eAC K) ∧
      ((proScalar psi Y).map (proCompactCoefficientMap phi f
          ((proSource A f (line A (ell ^ n) hA X d)).obj K)) ≫
          proCompactCoefficientMap psi f
            ((proScalar phi X).obj ((proSource A f (line A (ell ^ n) hA X d)).obj K)) ≫
          (proCompact C f).map ((scalarAssociator phi psi X).hom.app
            ((proSource A f (line A (ell ^ n) hA X d)).obj K)) =
        (scalarAssociator phi psi Y).hom.app
            ((proCompact A f).obj ((proSource A f (line A (ell ^ n) hA X d)).obj K)) ≫
          proCompactCoefficientMap (psi.comp phi) f
            ((proSource A f (line A (ell ^ n) hA X d)).obj K))
  composition : ∀
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsSeparated f] [IsSeparated g]
    [QuasiCompact g] (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (df : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (dg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (dh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (af : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)
    (ag : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
    (ah : Etale.dualizingComplex (ModuleCat.{u + 1} A) (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X (d + e))
    (_hf : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA f d df
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) af)
    (_hg : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA g e dg
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) ag)
    (_hh : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA (f ≫ g) (d + e) dh
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ah),
    SpCompositionFactors.FiniteEquations A f g (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) d e af ag ah
  baseChange : ∀
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (X Y Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    [IsNoetherian (pullback f.left v.left)]
    (n : ℕ) (_hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f.left v.left, ⊤)))
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : Etale.dualizingComplex (ModuleCat.{u + 1} A)
        (pullback.snd f.left v.left) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f.left v.left)
      d g' hX' alpha'),
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.inv ≫
          Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) =
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
          (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
            (pow_pos (Fact.out : ell.Prime).pos n) hA)
          (pullback.fst f.left v.left) hX d).hom ≫ alpha'.inv) ∧
    ∀ K : Etale.DerivedCategoryModule A Y.left,
      Etale.FiniteSmoothPurity.IsCtf A Y.left
        ((Etale.FiniteSmoothPurity.comparison A Y.left).obj K) →
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f.left
                (Etale.isIso_projectionMap_of_finite A f.left) K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
              (pullback.fst f.left v.left)
              ((Etale.ordinaryFinitePullback A f.left).obj K)
              (Etale.dualizingComplex (ModuleCat.{u + 1} A) f.left)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).map
              (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq K)).app _ ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).obj
              ((Etale.ordinaryFinitePullback A (pullback.snd f.left v.left)).obj
                ((Etale.ordinaryFinitePullback A v.left).obj K))).map
                  (Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) ≫
            Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A)
              (pullback.snd f.left v.left)
              (Etale.isIso_projectionMap_of_finite A (pullback.snd f.left v.left))
              ((Etale.ordinaryFinitePullback A v.left).obj K)) ∧
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.FiniteSmoothPurity.gamma A f.left _ alpha K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFiniteTwistedPullbackComparison A f.left
              (pullback.snd f.left v.left) v.left (pullback.fst f.left v.left)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d) K
              ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq).symm.app K)
              (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
                (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
                  (pow_pos (Fact.out : ell.Prime).pos n) hA)
                (pullback.fst f.left v.left) hX d)).hom ≫
            Etale.FiniteSmoothPurity.gamma A (pullback.snd f.left v.left) _ alpha'
              ((Etale.ordinaryFinitePullback A v.left).obj K))
  reductionPurity : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    (P.finiteReduction m hm hmn X).map (P.smoothPurityMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK)
  reductionTrace : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    (P.finiteReduction m hm hmn Y).map (P.coefficientValuedSmoothTrace f d K hK) =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj K) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK)
  reductionUnitTrace : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f],
    (P.finiteReduction m hm hmn Y).map (P.smoothTrace f d) ≫
        P.finiteReductionUnitComparison m hm hmn Y =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj (P.coefficientUnit Y)) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReductionSourceComparison m hm hmn f d (P.coefficientUnit Y)).hom ≫
            ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
              (P.finiteReductionUnitComparison m hm hmn Y)) ≫
        (P.finiteReductionSetting m hm).smoothTrace f d
  reductionComposition : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K),
    (P.finiteReduction m hm hmn X).map
        ((P.compositionSourceIdentification f g d e K).hom ≫
          (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
          P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
            (P.compositionExceptional_ctf g e K hK) ≫
          (P.compositionExceptionalIso f g K hK).inv) ≫
        P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK =
      (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
        ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
          ((P.finiteReduction m hm hmn Z).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
          ((P.finiteReductionSetting m hm).smoothPurityMap g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          (((P.finiteReductionSetting m hm).compositionExceptional g).obj
            ((P.finiteReduction m hm hmn Z).obj K))
          ((P.finiteReductionSetting m hm).compositionExceptional_ctf g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
          ((P.finiteReduction m hm hmn Z).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).inv
  reductionBaseChange : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (sq : IsPullback u f' f v) (d : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).compositionShiftedPullback f' d).map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionShiftedPullback f d).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionBaseChangeSource
        u f' f v sq d ((P.finiteReduction m hm hmn Y).obj K)).hom) ∧
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionSmoothExchange u f' f v sq d K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K) (P.finiteReductionBaseChangeInput v K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionExceptional f).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
      ((P.finiteReductionSetting m hm).finiteReductionSmoothExchange u f' f v sq d
        ((P.finiteReduction m hm hmn Y).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Y K hK)).hom)
  reductionOrientation : ∀
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))],
    (P.finiteReduction m hm hmn Y).map (P.finiteReductionOrientation Y) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn Y ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).map
          (P.finiteReductionOrientationInputComparison m hm hmn Y).hom =
    P.finiteReductionUnitComparison m hm hmn Y ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation Y
  affine : ∀
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    (S : Scheme.{u}) [S.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of D.k))]
    [QuasiCompact (S ↘ Spec (.of D.k))] [IsSeparated (S ↘ Spec (.of D.k))]
    [IsNoetherian S] (n : ℕ) (hn : 1 ≤ n)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0)
    (d : ℕ) [IsNoetherian (affineTraceTower S d)]
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (affineTraceProjection S d) (affineTraceProjection S d))
      (pullback.diagonal (affineTraceProjection S d)))
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A)
      (affineTraceProjection S d) ≅ line A (ell ^ n) hA (affineTraceTower S d) d)
    (_ha : OrientationNormalized A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      hA (affineTraceProjection S d) d geometry
      ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
        (affineTraceProjection S d ≫ (S ↘ Spec (.of D.k)))) alpha)
    (K : Etale.DerivedCategoryModule A S),
    Etale.DerivedCategory.boundedConstructibleFiniteTor A S K →
      trace A (affineTraceProjection S d) _ alpha K =
        affineIntegrationCounit A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n) hA S
          ((finiteGeneralRingPrimeSetting D ell hne n hn).diagonalExponent_isUnit
            (S ↘ Spec (.of D.k))) d K

/-- Finite purity is a normalized system of explicit adjunctions and actual counits.
Source: latest blueprint sk-thm-purity-transport, Steps 1, 3 and 4
(blueprint: lem-pur-transport-finite-counit-system).

Proof:
1. Use sk-prop-sf-rf-shriek-preservation and the exact section-action equivalence
   lem-sf-module-object-ordinary-coefficient-equivalence to work on these same finite-Tor
   categories with the same compactification composite and exceptional counit.
   det-sp-finite-general-ring supplies the normalized orientation and natural gamma,
   independently of the exponent. Transport the exceptional Hom bijection by gamma
   inverse (lem-weil-pbc-adjunction-of-natural-bijection). This gives AdjunctionAt,
   including its unit, counit and site-origin equations.
2. det-sp-scalar-extension-functor preserves the finite-Tor domain without flatness.
   Combine det-sp-reduction-compatibilities(3) with the defining counit equation
   of det-sp-reduction-exceptional. Naturality of the b of det-sp-reduction-direct-image
   moves F(gamma) through b inverse, giving exactly the coefficient trace equation.
3. Express a as gamma inverse followed by c and scalar gamma. Successive gamma
   factors cancel; det-sp-reduction-compatibilities(2) and the scalar associator
   give the source cocycle. The b cocycle is det-sp-reduction-direct-image.
   Substitution in the exceptional unit equation proves the displayed unit equation;
   together with the counit equation these are transitive adjunctions.
4. det-sp-composition-factors and det-sp-purity-bc-factors apply to these same
   diagonal/DNC-normalized orientations and tensor mates. They give the constituent
   and gamma identities. thm-pur-finite-reduction-of-purity gives every recorded
   reduction square, including trace, unit trace, composition, exchange and orientation.
5. Transpose the tensor definition of gamma. Naturality of inverse projection in
   the inverse orientation shows t_K is inverse projection followed by one tensor t_1.
6. For Z/ell^n, lem-pur-projection-purity-agreement identifies the line map with
   the exceptional transpose of projective-line integration restricted by zero extension.
   Apply the inverse adjunction bijection to get the actual counit formula.
7. For an arbitrary finite ring A, scalar-extend only the coefficient unit from Z/ell^n.
   The Step 2 counit equation and lem-pur-vector-trace-scalar-descent identify its trace
   with that same integration over A. lem-sp-et-proet-coefficient-compatibility and
   lem-pur-finite-ring-site-tensor-transpose identify the specified site/scalar maps.
   Finite type over the field makes all bases Noetherian. Cancel the invertible
   coefficient comparisons and use Step 5 for every K, without a regularity assumption.
8. Factor affine d-space into the ordered line projections. The composition equation
   and def-weil-pbc-composite-adjunction identify its counit with the iterated line
   counits. Induct from the identity adjunction at d=0. The even shifts introduce
   no odd interchange sign. This is exactly affineIntegrationCounit at every d.
-/
theorem finiteCounitSystem : System.{u} := by
  sorry

end AlgebraicGeometry.ProEtale.FinitePurityCounit
