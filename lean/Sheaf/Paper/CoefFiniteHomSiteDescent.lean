module

public import Sheaf.Paper.FiniteCoefficientSiteHomArrow
public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.FiniteCoefficientSiteScalarArrow
public import Sheaf.Paper.FiniteCoefficientSiteChainTensor
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.NormalizedOriginScalarComparisons
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.SixFunctors.CoefMonoidalSquareHomTransport

/-! # Finite Hom scalar/site square and constructible descent

Source: blueprint `thm-coef-finite-hom`, final paragraph and final site-comparison
sentence, expanded in the seven proof steps of lem-coef-finite-hom-site-descent
(blueprint: lem-coef-finite-hom-site-descent).

The indices n,m,r mean the positive exponents n+1,m+1,r+1. The canonical
scalar/site isomorphism is the inverse of the existing adjunction mate, and the
Hom comparisons are the existing evaluation transposes. No scalar-Hom
invertibility is asserted. Object and morphism universes of the small site remain distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Strong monoidality for a specified tensor comparison, including unit and associativity.
The unit is determined by this tensorator and the two unit axioms, so it is not extra
unconstrained comparison data. Source: blueprint final paragraph; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomStrong
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :=
  letI := SA.monoidal
  letI := SB.monoidal
  {s : F.CoreMonoidal // ∀ P Q : A, s.μIso P Q = (μ.app (P, Q)).symm}

/-- The monoidal square equations for the fixed tensorators and their coherent units.
Source: blueprint final site-comparison sentence; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomMonoidalSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G) : Prop :=
  ∃ sF : CoefFiniteHomStrong SA SB F μF,
    ∃ sG : CoefFiniteHomStrong SC SD G μG,
      ∃ sU : CoefFiniteHomStrong SA SC U μU,
        ∃ sV : CoefFiniteHomStrong SB SD V μV,
          (∀ K M : A,
            h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
                μG.hom.app (U.obj K, U.obj M) =
              V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
                SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) ∧
          h.hom.app SA.monoidal.tensorUnit ≫
              G.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SC.monoidal U sU.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SC.monoidal _ _ SD.monoidal G sG.val).inv =
            V.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SB.monoidal F sF.val).inv ≫
              (@Functor.CoreMonoidal.εIso _ _ SB.monoidal _ _ SD.monoidal V sV.val).inv

/-- Naturality, evaluation/transpose and internal composition at finite-Tor pairs.
This is the restriction of the existing coefficient evaluation equations to the stated
constructible domain. Source: blueprint final paragraph, equations transported by the square
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomLawsOn
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P : ObjectProperty A) : Prop :=
  (∀ K M K' M' : A, P K → P M → P K' → P M' →
    ∀ (f : K' ⟶ K) (g : M ⟶ M'),
      F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ K' M' =
        coefficientBaseChangeHom SA SB F μ K M ≫
          HB.map (Prod.mkHom (F.map f).op (F.map g))) ∧
  (∀ K M : A, P K → P M → ∀ (T : A) (f : SA.tensor.obj (T, K) ⟶ M),
    F.map (SA.transpose T K M f) ≫ coefficientBaseChangeHom SA SB F μ K M =
      SB.transpose (F.obj T) (F.obj K) (F.obj M) (μ.inv.app (T, K) ≫ F.map f)) ∧
  (∀ K L M : A, P K → P L → P M →
    F.map (SA.composition K L M) ≫ coefficientBaseChangeHom SA SB F μ K M =
      μ.hom.app (HA.obj (op L, M), HA.obj (op K, L)) ≫
        SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ L M)
          (coefficientBaseChangeHom SA SB F μ K L)) ≫
        SB.composition (F.obj K) (F.obj L) (F.obj M))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The specified coefficient/site isomorphism h, inverse to the scalar-restriction mate.
Source: blueprint final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomSiteIso {n m : ℕ} (h : m ≤ n) :
    finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m ≅
      finiteHomNu l E X n ⋙ coefficientFiniteQuotientDerived l E X h :=
  (asIso (finiteHomSiteBeta l E X h)).symm

/-- Bounded constructibility in the existing positive-level etale category.
Source: blueprint constructible descent clause
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomEtaleConstructible (n : ℕ) : ObjectProperty (finiteHomEtale l E X n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- Descent, reflection for every bounded constructible witness, and interval preservation.
Source: blueprint site-comparison sentence; proof step 1
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomDescent (n : ℕ) : Prop :=
  PreservesFiniteLimits (finiteHomNuOrdinary l E X n) ∧
  PreservesFiniteColimits (finiteHomNuOrdinary l E X n) ∧
  (∀ P : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    ∃ P' : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' ∧
      Nonempty ((finiteHomNu l E X n).obj P' ≅ P)) ∧
  (∀ (P : normalizedDVRDerived l E X n) (P' : finiteHomEtale l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X P →
    coefFiniteHomEtaleConstructible l E X n P' →
    Nonempty ((finiteHomNu l E X n).obj P' ≅ P) → ∀ a b : ℤ, a ≤ b →
      (Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' ↔
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) P a b)) ∧
  (∀ P' : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X P' →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
      ((finiteHomNu l E X n).obj P') ∧
    ∀ a b : ℤ, a ≤ b → Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X a b P' →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteHomNu l E X n).obj P') a b)

/-- The actual canonical square, with the inverse h in the contravariant Hom input.
Source: blueprint final site-comparison sentence; proof step 6
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSquare {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    IsIso (finiteHomSiteHom l E X n K M) ∧
    IsIso (finiteHomSiteHom l E X m
      ((finiteHomEtaleReduction l E X h).obj K)
      ((finiteHomEtaleReduction l E X h).obj M)) ∧
    (coefFiniteHomSiteIso l E X h).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      (coefficientFiniteQuotientDerived l E X h).map (finiteHomSiteHom l E X n K M) ≫
      proEtaleFiniteHomCanonical l E X h
        ((finiteHomNu l E X n).obj K) ((finiteHomNu l E X n).obj M) =
    (finiteHomNu l E X m).map (etaleFiniteHomCanonical l E X h K M) ≫
      finiteHomSiteHom l E X m
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X m).map
        (Prod.mkHom ((coefFiniteHomSiteIso l E X h).inv.app K).op
          ((coefFiniteHomSiteIso l E X h).hom.app M))

/-- Coherence for the actual scalar/site isomorphisms under successive quotients.
Source: blueprint final paragraph; proof step 4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomQuotientCoherence {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m) (T : finiteHomEtale l E X n),
    (finiteHomNu l E X r).map ((finiteHomEtaleAssoc l E X h k).hom.app T) ≫
      (coefFiniteHomSiteIso l E X (k.trans h)).hom.app T =
    (coefFiniteHomSiteIso l E X k).hom.app ((finiteHomEtaleReduction l E X h).obj T) ≫
      (coefficientFiniteQuotientDerived l E X k).map
        ((coefFiniteHomSiteIso l E X h).hom.app T) ≫
      (finiteHomIntrinsicAssoc l E X h k).hom.app ((finiteHomNu l E X n).obj T)

/-- The fixed intrinsic scalar tensorator, projected from the published quotient calculus.
Source: blueprint scalar tensor convention; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProTensor {n m : ℕ} (h : m ≤ n) :=
  (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h

/-- Symmetry of a specified tensor comparison, using the supplied canonical symmetries.
Source: blueprint monoidal clause; Stacks 07A4
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSymmetry
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (βA : @SymmetricCategory A _ SA.monoidal)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q : A,
    F.map (βA.toBraidedCategory.braiding P Q).hom ≫ μ.hom.app (Q, P) =
      μ.hom.app (P, Q) ≫ (βB.toBraidedCategory.braiding (F.obj P) (F.obj Q)).hom

/-- The canonical identity-quotient scalar associator, adjoint to identity restriction.
Source: blueprint identity quotient convention
(blueprint: lem-coef-finite-hom-site-descent). -/
def coefFiniteHomProUnit (n : ℕ) :
    coefficientFiniteQuotientDerived l E X (Nat.le_refl n) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n)) (normalizedDVRResUnit l E X n)

/-- Transport of successive quotient and identity equations from the etale transposes
to the intrinsic transposes, on finite-Tor constructible pairs.
Source: blueprint final paragraph; proof step 7
(blueprint: lem-coef-finite-hom-site-descent). -/
def CoefFiniteHomSuccessive {n m : ℕ} (h : m ≤ n) : Prop :=
  ((∀ (r : ℕ) (k : r ≤ m) (K M : finiteHomEtale l E X n),
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomEtaleAssoc l E X h k).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≫
      etaleFiniteHomCanonical l E X (k.trans h) K M =
    (finiteHomEtaleReduction l E X k).map
        (etaleFiniteHomCanonical l E X h K M) ≫
      etaleFiniteHomCanonical l E X k
        ((finiteHomEtaleReduction l E X h).obj K)
        ((finiteHomEtaleReduction l E X h).obj M) ≫
      (finiteHomEtaleInternalHom l E X r).map
        (Prod.mkHom ((finiteHomEtaleAssoc l E X h k).inv.app K).op
          ((finiteHomEtaleAssoc l E X h k).hom.app M))) ∧
  (∀ K M : finiteHomEtale l E X n,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
    etaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (finiteHomEtaleInternalHom l E X n).map
        (Prod.mkHom
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).inv.app K).op
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
            (finiteHomQuotient l E (Nat.le_refl n))
            (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
              (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app M)) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
        (finiteHomQuotient l E (Nat.le_refl n))
        (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
          (S := Padic.coefficientExtensionIdeal l E (n + 1))))).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)))) →
  (∀ (r : ℕ) (k : r ≤ m) (K M : normalizedDVRDerived l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    (finiteHomIntrinsicAssoc l E X h k).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)) ≫
      proEtaleFiniteHomCanonical l E X (k.trans h) K M =
    (coefficientFiniteQuotientDerived l E X k).map
        (proEtaleFiniteHomCanonical l E X h K M) ≫
      proEtaleFiniteHomCanonical l E X k
        ((coefficientFiniteQuotientDerived l E X h).obj K)
        ((coefficientFiniteQuotientDerived l E X h).obj M) ≫
      (coefficientFiniteInternalHom l E X r).map
        (Prod.mkHom ((finiteHomIntrinsicAssoc l E X h k).inv.app K).op
          ((finiteHomIntrinsicAssoc l E X h k).hom.app M))) ∧
  (∀ K M : normalizedDVRDerived l E X n,
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    proEtaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom ((coefFiniteHomProUnit l E X n).inv.app K).op
          ((coefFiniteHomProUnit l E X n).hom.app M)) =
      (coefFiniteHomProUnit l E X n).hom.app
        ((coefficientFiniteInternalHom l E X n).obj (op K, M)))

/-- Constructible descent component of the finite Hom site descent theorem.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 1.
(blueprint: lem-coef-finite-hom-site-descent-core-descent). -/
theorem coefFiniteHomSiteDescent_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ n : ℕ, CoefFiniteHomDescent l E X n := by
  sorry

/-- Monoidal, symmetry, quotient, square, and transport component.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof steps 2--7.
(blueprint: lem-coef-finite-hom-site-descent-core-coherence). -/
theorem coefFiniteHomSiteDescent_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
        (finiteHomEtaleClosed l E X n).monoidal,
      ∃ βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
          (finiteIntrinsicClosed l E X n).monoidal,
        (∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
          HEq ((βet n).toBraidedCategory.braiding P Q)
            (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q)) ∧
        (∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) ∧
        (∀ n : ℕ, CoefFiniteHomSymmetry
          (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
          (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
        ∀ (n m : ℕ) (h : m ≤ n),
          CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (βet n) (βet m) (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
            (coefFiniteHomProTensor l E X h) ∧
          CoefFiniteHomQuotientCoherence l E X h ∧ CoefFiniteHomSquare l E X h ∧
          (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  sorry

/-- Finite-Tor constructible descent and the canonical scalar/site Hom square.
Source: blueprint thm-coef-finite-hom, final paragraph and final sentence
(blueprint: lem-coef-finite-hom-site-descent).

Proof (the node's seven steps):
1. Exact comparison identifies constant rings (lem-sf-comparison-pullback-exact).
Constructible origin supplies an etale witness. Comparison Tor-amplitude reflection
applies because that witness is bounded below; preservation and reflection identify
all ordered Tor intervals for every witness (lem-sf-proetale-constructible-origin,
lem-sf-comparison-tor-amplitude).
2. The terminal-diagram case of lem-pur-algebra-diagram-pullback-extension-coherence
constructs the scalar/site isomorphism. On flat-term K-flat resolutions its map is
inverse image of x tensor b mapped to the tensor of the inverse image of x and b.
K-flat resolutions, ringed pullback preservation and derived-pullback computation
identify this with the inverse of the fixed restriction mate.
3. The ringed-derived closed symmetric monoidal theorem supplies the four ambient
structures. Canonical tensor pullback and its shift/unit normalization identify their
comparisons with the cochain maps of lem-pur-cochain-pullback-tensor-coherence.
These respect associators, unitors and signed symmetry even for nonflat quotients.
4. The cochain scalar-association equation proves monoidality of h; the unit sends
one to one. Both successive routes send (x tensor b) tensor c to the inverse image
of x tensor the image of b times c. Localization preserves these equations.
5. Finite Hom domain calculus puts reductions in the finite-Tor constructible domain.
The finite-duality site comparison makes the specified evaluation-defined beta maps
invertible, both before and after reduction. This uses no invertibility of v.
6. Apply lem-coef-monoidal-square-hom-transport to the four functors and the monoidal h.
Its transpose equation is exactly the displayed square; Hom uses h inverse in its
contravariant input and h in its covariant input.
7. Assuming the corresponding etale equations, that same categorical transport carries
naturality, evaluation, arbitrary transposes, internal composition, identities and successive
quotients to the intrinsic equations. The etale identity uses normalizedOriginScalarUnit,
the adjunction mate of identity restriction. Every intrinsic
finite-Tor constructible pair has etale witnesses by step 1; naturality conjugates the
equations by the witness isomorphisms, independently of their choice. -/
theorem coefFiniteHomSiteDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (∀ n : ℕ, CoefFiniteHomDescent l E X n) ∧
    ∃ βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
        (finiteHomEtaleClosed l E X n).monoidal,
      ∃ βpro : ∀ n : ℕ, @SymmetricCategory (normalizedDVRDerived l E X n) _
          (finiteIntrinsicClosed l E X n).monoidal,
        (∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
          HEq ((βet n).toBraidedCategory.braiding P Q)
            (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q)) ∧
        (∀ n : ℕ, Nonempty (RingedDerivedTensorCoherence
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n) (βpro n))) ∧
        (∀ n : ℕ, CoefFiniteHomSymmetry
          (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
          (βet n) (βpro n) (finiteHomNu l E X n) (finiteHomNuTensor l E X n)) ∧
        ∀ (n m : ℕ) (h : m ≤ n),
          CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (βet n) (βet m) (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
          CoefFiniteHomSymmetry
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (βpro n) (βpro m) (coefficientFiniteQuotientDerived l E X h)
            (coefFiniteHomProTensor l E X h) ∧
          CoefFiniteHomQuotientCoherence l E X h ∧ CoefFiniteHomSquare l E X h ∧
          (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  exact ⟨coefFiniteHomSiteDescent_descent D l _hl E X,
    coefFiniteHomSiteDescent_coherence D l _hl E X⟩

end WeilConjectures
