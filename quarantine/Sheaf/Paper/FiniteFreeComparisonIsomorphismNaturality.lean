module

public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Paper.DualityPairing
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites
import Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.CategoryTheory.AdjointEquivalenceConjugation
import Sheaf.SixFunctors.CoefMonoidalSquareHomTransport
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Scheme-isomorphism naturality of specified finite-free coefficient maps

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality).

Only the definitions of FiniteFreeCoefficientExtension are used. Its theorem is a consumer
of this statement, not a premise. The ordinary-etale assertions below have unbounded inputs.
The pro-etale assertions use the recorded transported exceptional functor and finite-Tor
constructible inputs; no ambient pro-etale exceptional adjunction is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeIsomorphismNaturality
open FiniteFreeCoefficients
open FiniteFreeCoefficients.Sites

/-- Exact derived inverse image on either actual small site.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def pull (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) : D pro A X ⥤ D pro A Y := by
  cases pro
  · exact Sites.pull A g
  · exact proPull A g

/-- The canonical scalar/pullback balancing isomorphism, not an extra chosen square.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def scalarPull (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) :
    scalar pro φ X ⋙ pull pro B g ≅ pull pro A g ⋙ scalar pro φ Y := by
  cases pro
  · exact Sites.scalarPull φ g
  · exact proScalarPull φ g

/-- The direct-image endpoint identification is the inverse-image counit mate.
It is defined for the actual commutative square, not just the chosen pullback object.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def directPull (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {V X V' X' : Scheme.{u}} {f : V ⟶ X} {f' : V' ⟶ X'}
    {gV : V' ⟶ V} {gX : X' ⟶ X} (sq : CommSq gV f' f gX) :
    push pro A f ⋙ pull pro A gX ⟶ pull pro A gV ⋙ push pro A f' := by
  cases pro
  · exact Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq
  · exact ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq

/-- Evaluation-normalized geometric internal-Hom identification.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def homPull (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K M : D pro A X) :
    (pull pro A g).obj (((hom pro A X).obj (op K)).obj M) ⟶
      ((hom pro A Y).obj (op ((pull pro A g).obj K))).obj ((pull pro A g).obj M) := by
  cases pro
  · exact pullHom A g K M
  · exact proPullHom A g K M

/-- The ordinary closed-adjoint transport is the transpose of the transported counit.
The inverse uses the canonical direct-image square on its isomorphism domain.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def etaleClosedPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i']
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} (sq : CommSq gZ i' i gX) (M : Cat A X) :
    (Sites.pull A gZ).obj ((closedUpper A i).obj M) ⟶
      (closedUpper A i').obj ((Sites.pull A gX).obj M) :=
  (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i'))).homEquiv _ _
    (inverseOnDomain ((directPull false A sq).app ((closedUpper A i).obj M)) ≫
      (Sites.pull A gX).map
        ((Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M))

/-- Closed transport on pro-etale realizations includes the canonical site counit mate.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def closedPull (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i']
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} (sq : CommSq gZ i' i gX) (M : D pro A X) :
    (pull pro A gZ).obj ((exceptional pro A i).obj M) ⟶
      (exceptional pro A i').obj ((pull pro A gX).obj M) := by
  cases pro
  · exact etaleClosedPull A sq M
  · exact (sitePull A gZ).hom.app ((closedUpper A i).obj ((rnu A X).obj M)) ≫
      (nu A Z').map (etaleClosedPull A sq ((rnu A X).obj M)) ≫
      (nu A Z').map ((closedUpper A i').map (rnuPull A gX M))

/-- The same specified coefficient comparison on the two exceptional realizations.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def closedScalar (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : D pro A X) :
    (scalar pro φ Z).obj ((exceptional pro A i).obj M) ⟶
      (exceptional pro B i).obj ((scalar pro φ X).obj M) := by
  cases pro
  · exact FiniteFreeCoefficients.closedMap φ i M
  · exact proClosedMap φ i M

/-- Exceptional transport along an actual isomorphism square uses the unique counit mate.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def etaleOmegaPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'}
    [QuasiCompact a'] {gX : X' ⟶ X} {gS : S' ⟶ S}
    (sq : IsPullback gX a' a gS) (c : Compactification a) (c' : Compactification a') :
    (Sites.pull A gX).obj (FiniteFreeCoefficients.omega A c) ⟶
      FiniteFreeCoefficients.omega A c' :=
  letI := c.hasCompactification
  letI := c'.hasCompactification
  Etale.dualizingComplexBaseChangeMap A sq

/-- Dualizing transport on pro-etale realizations is the site transport of the same mate.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def omegaPull (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'}
    [QuasiCompact a'] {gX : X' ⟶ X} {gS : S' ⟶ S}
    (sq : IsPullback gX a' a gS) (c : Compactification a) (c' : Compactification a') :
    (pull pro A gX).obj (omega pro A c) ⟶ omega pro A c' := by
  cases pro
  · exact etaleOmegaPull A sq c c'
  · exact (proPull A gX).map (inverseOnDomain (omegaBridge A c)) ≫
      (sitePull A gX).hom.app (FiniteFreeCoefficients.omega A c) ≫
      (nu A X').map (etaleOmegaPull A sq c c') ≫ omegaBridge A c'

/-- Canonical dualizing coefficient comparison on either realization.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def omegaScalar (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a) :
    (scalar pro φ X).obj (omega pro A c) ⟶ omega pro B c := by
  cases pro
  · exact FiniteFreeCoefficients.omegaMap φ c
  · exact proOmegaMap φ c

/-- The ordinary category has no restriction; the pro-etale domain is finite-Tor constructible.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def Domain (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    ObjectProperty (D pro A X) :=
  match pro with
  | false => ⊤
  | true => Sites.Ctf true A X

/-- The geometric Verdier identification is Hom transport followed by dualizing transport.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def dualPull (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'}
    [QuasiCompact a'] {gX : X' ⟶ X} {gS : S' ⟶ S}
    (sq : IsPullback gX a' a gS) (c : Compactification a) (c' : Compactification a')
    (K : D pro A X) :
    (pull pro A gX).obj ((dual pro A c).obj (op K)) ⟶
      (dual pro A c').obj (op ((pull pro A gX).obj K)) :=
  homPull pro A gX K (omega pro A c) ≫
    ((hom pro A X').obj (op ((pull pro A gX).obj K))).map (omegaPull pro A sq c c')

/-- Composition identification from the actual termwise site pullbacks.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def pullComp (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {Z Y X : Scheme.{u}} (h : Z ⟶ Y) (g : Y ⟶ X) :
    pull pro A (h ≫ g) ≅ pull pro A g ⋙ pull pro A h := by
  cases pro
  · exact Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h g
  · exact ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h g

/-- Identity identification induced by identity site reindexing.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def pullId (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    pull pro A (𝟙 X) ≅ 𝟭 (D pro A X) := by
  cases pro
  · exact Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) X
  · exact ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) X

/-- The inverse-image square is induced by actual composition of the site functors.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def pullSquare (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {V X V' X' : Scheme.{u}} {f : V ⟶ X} {f' : V' ⟶ X'}
    {gV : V' ⟶ V} {gX : X' ⟶ X} (sq : CommSq gV f' f gX) :
    pull pro A f ⋙ pull pro A gV ≅ pull pro A gX ⋙ pull pro A f' :=
  (pullComp pro A gV f).symm ≪≫ eqToIso (congrArg (pull pro A) sq.w) ≪≫
    pullComp pro A f' gX

/-- Ordinary inverse-image/direct-image adjunction on each of the actual sites.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def imageAdj (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {V X : Scheme.{u}} (f : V ⟶ X) : pull pro A f ⊣ push pro A f := by
  cases pro
  · exact Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  · exact ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f

/-- Compact-support transport is the proper-image/open-extension comparison.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def supportPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} [QuasiCompact a']
    {gX : X' ⟶ X} {gS : S' ⟶ S} (sq : IsPullback gX a' a gS)
    (c : Compactification a) (c' : Compactification a') :
    FiniteFreeCoefficients.support A c ⋙ Sites.pull A gS ⟶
      Sites.pull A gX ⋙ FiniteFreeCoefficients.support A c' :=
  letI := c.hasCompactification
  letI := c'.hasCompactification
  Etale.rightDerivedLowerShriekBaseChangeMap A sq

/-- The full exceptional identification is the counit mate of compact-support transport.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def upperPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} [QuasiCompact a']
    {gX : X' ⟶ X} {gS : S' ⟶ S} (sq : IsPullback gX a' a gS)
    (c : Compactification a) (c' : Compactification a') :
    FiniteFreeCoefficients.upper A c ⋙ Sites.pull A gX ⟶
      Sites.pull A gS ⋙ FiniteFreeCoefficients.upper A c' :=
  letI := c.hasCompactification
  letI := c'.hasCompactification
  Etale.rightDerivedUpperShriekBaseChangeMap A sq

/-- The five actual coefficient-map squares, with evaluation and double-dual transport.
Every endpoint map is the previously defined counit or evaluation transpose.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
structure SquareLaws (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {V X Z S V' X' Z' S' : Scheme.{u}}
    {f : V ⟶ X} {f' : V' ⟶ X'} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i']
    {a : X ⟶ S} {a' : X' ⟶ S'} [QuasiCompact a']
    (gV : V' ≅ V) (gX : X' ≅ X) (gZ : Z' ≅ Z) (gS : S' ≅ S)
    (sf : CommSq gV.hom f' f gX.hom) (si : CommSq gZ.hom i' i gX.hom)
    (sa : IsPullback gX.hom a' a gS.hom)
    (c : Compactification a) (c' : Compactification a')
    (μ : TensorComparison pro φ X) (μ' : TensorComparison pro φ X') : Prop where
  direct_iso : ∀ K : D pro A V, IsIso ((directPull pro A sf).app K)
  direct_iso_target : ∀ K : D pro B V, IsIso ((directPull pro B sf).app K)
  closed_iso : ∀ M : D pro A X, Domain pro A X M → IsIso (closedPull pro A si M)
  closed_iso_target : ∀ M : D pro B X, Domain pro B X M → IsIso (closedPull pro B si M)
  omega_iso : IsIso (omegaPull pro A sa c c')
  omega_iso_target : IsIso (omegaPull pro B sa c c')
  support_iso : ∀ K : Cat A X, IsIso ((supportPull A sa c c').app K)
  upper_iso : ∀ N : Cat A S, IsIso ((upperPull A sa c c').app N)
  image_counit : ∀ K : D pro A V,
    (pull pro A f').map ((directPull pro A sf).app K) ≫
        (imageAdj pro A f').counit.app ((pull pro A gV.hom).obj K) =
      (pullSquare pro A sf).inv.app ((push pro A f).obj K) ≫
        (pull pro A gV.hom).map ((imageAdj pro A f).counit.app K)
  upper_counit : ∀ N : Cat A S,
    (FiniteFreeCoefficients.support A c').map ((upperPull A sa c c').app N) ≫
        (FiniteFreeCoefficients.adj A c').counit.app ((Sites.pull A gS.hom).obj N) =
      inverseOnDomain ((supportPull A sa c c').app
        ((FiniteFreeCoefficients.upper A c).obj N)) ≫
        (Sites.pull A gS.hom).map ((FiniteFreeCoefficients.adj A c).counit.app N)
  direct : ∀ K : D pro A V, Domain pro A V K →
    (scalar pro φ X').map ((directPull pro A sf).app K) ≫
        direct pro φ f' ((pull pro A gV.hom).obj K) ≫
        (push pro B f').map ((scalarPull pro φ gV.hom).inv.app K) =
      (scalarPull pro φ gX.hom).inv.app ((push pro A f).obj K) ≫
        (pull pro B gX.hom).map (direct pro φ f K) ≫
        (directPull pro B sf).app ((scalar pro φ V).obj K)
  closed : ∀ M : D pro A X, Domain pro A X M →
    (scalar pro φ Z').map (closedPull pro A si M) ≫
        closedScalar pro φ i' ((pull pro A gX.hom).obj M) ≫
        (exceptional pro B i').map ((scalarPull pro φ gX.hom).inv.app M) =
      (scalarPull pro φ gZ.hom).inv.app ((exceptional pro A i).obj M) ≫
        (pull pro B gZ.hom).map (closedScalar pro φ i M) ≫
        closedPull pro B si ((scalar pro φ X).obj M)
  closed_counit : ∀ M : Cat A X,
    (R(Etale.lowerStar (ModuleCat.{u + 1} A) i')).map (etaleClosedPull A si M) ≫
        (Adjunction.ofIsLeftAdjoint
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) i'))).counit.app
            ((Sites.pull A gX.hom).obj M) =
      inverseOnDomain ((directPull false A si).app ((closedUpper A i).obj M)) ≫
        (Sites.pull A gX.hom).map
          ((Adjunction.ofIsLeftAdjoint
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) i))).counit.app M)
  omega : (scalar pro φ X').map (omegaPull pro A sa c c') ≫ omegaScalar pro φ c' =
    (scalarPull pro φ gX.hom).inv.app (Sites.omega pro A c) ≫
      (pull pro B gX.hom).map (omegaScalar pro φ c) ≫ omegaPull pro B sa c c'
  hom : ∀ K M : D pro A X, Domain pro A X K → Domain pro A X M →
    (scalar pro φ X').map (homPull pro A gX.hom K M) ≫
        homMap pro φ X' μ' ((pull pro A gX.hom).obj K) ((pull pro A gX.hom).obj M) ≫
        homAction (Sites.hom pro B X') ((scalarPull pro φ gX.hom).hom.app K)
          ((scalarPull pro φ gX.hom).inv.app M) =
      (scalarPull pro φ gX.hom).inv.app (((Sites.hom pro A X).obj (op K)).obj M) ≫
        (pull pro B gX.hom).map (homMap pro φ X μ K M) ≫
        homPull pro B gX.hom ((scalar pro φ X).obj K) ((scalar pro φ X).obj M)
  verdier : ∀ K : D pro A X, Domain pro A X K →
    (scalar pro φ X').map (dualPull pro A sa c c' K) ≫
        dualMap pro φ c' μ' (omegaScalar pro φ c') ((pull pro A gX.hom).obj K) ≫
        ((Sites.hom pro B X').map ((scalarPull pro φ gX.hom).hom.app K).op).app
          (Sites.omega pro B c') =
      (scalarPull pro φ gX.hom).inv.app ((dual pro A c).obj (op K)) ≫
        (pull pro B gX.hom).map (dualMap pro φ c μ (omegaScalar pro φ c) K) ≫
        dualPull pro B sa c c' ((scalar pro φ X).obj K)

/-- Tensor and evaluation transport, including transposition, on the actual two sites.
This pins down the double-dual transpose without any biduality-isomorphism hypothesis.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
def tensorPull (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K M : D pro A X) :
    (pull pro A g).obj (((tensor pro A X).obj K).obj M) ≅
      ((tensor pro A Y).obj ((pull pro A g).obj K)).obj ((pull pro A g).obj M) := by
  cases pro
  · exact Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K M
  · exact ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K M

/-- Evaluation, every tensor-Hom transpose, double dual, and identity/composition coherence.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
structure HomTransportLaws (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) : Prop where
  equivalence : ∀ {Y : Scheme.{u}} (e : Y ≅ X),
    ∃ E : D pro A X ≌ D pro A Y,
      E.functor = pull pro A e.hom ∧ E.inverse = pull pro A e.inv
  domain : ∀ {Y : Scheme.{u}} (e : Y ≅ X) (K : D pro A X),
    Domain pro A Y ((pull pro A e.hom).obj K) ↔ Domain pro A X K
  hom_iso : ∀ {Y : Scheme.{u}} (e : Y ≅ X) (K M : D pro A X),
    IsIso (homPull pro A e.hom K M)
  evaluation : ∀ {Y : Scheme.{u}} (e : Y ≅ X) (K M : D pro A X),
    (tensorPull pro A e.hom K (((Sites.hom pro A X).obj (op K)).obj M)).hom ≫
        ((tensor pro A Y).obj ((pull pro A e.hom).obj K)).map (homPull pro A e.hom K M) ≫
        (Sites.adj pro A Y ((pull pro A e.hom).obj K)).counit.app ((pull pro A e.hom).obj M) =
      (pull pro A e.hom).map ((Sites.adj pro A X K).counit.app M)
  transpose : ∀ {Y : Scheme.{u}} (e : Y ≅ X) (K L M : D pro A X)
      (b : ((tensor pro A X).obj K).obj L ⟶ M),
    (Sites.adj pro A Y ((pull pro A e.hom).obj K)).homEquiv _ _
        ((tensorPull pro A e.hom K L).inv ≫ (pull pro A e.hom).map b) =
      (pull pro A e.hom).map ((Sites.adj pro A X K).homEquiv _ _ b) ≫ homPull pro A e.hom K M
  bidual : ∀ {Y : Scheme.{u}} (e : Y ≅ X)
      (b : tensor pro A X ≅ (tensor pro A X).flip)
      (b' : tensor pro A Y ≅ (tensor pro A Y).flip),
    NormalizedSymmetry pro A X b → NormalizedSymmetry pro A Y b' →
    ∀ (W K : D pro A X),
      (pull pro A e.hom).map (Sites.bidual pro A X b W K) ≫
          homPull pro A e.hom (((Sites.hom pro A X).obj (op K)).obj W) W ≫
          homAction (Sites.hom pro A Y) (inverseOnDomain (homPull pro A e.hom K W))
            (𝟙 ((pull pro A e.hom).obj W)) =
        Sites.bidual pro A Y b' ((pull pro A e.hom).obj W) ((pull pro A e.hom).obj K)
  identity : ∀ (K M : D pro A X),
    homPull pro A (𝟙 X) K M ≫
        homAction (Sites.hom pro A X) ((pullId pro A X).inv.app K)
          ((pullId pro A X).hom.app M) =
      (pullId pro A X).hom.app (((Sites.hom pro A X).obj (op K)).obj M)
  composition : ∀ {Z Y : Scheme.{u}} (h : Z ≅ Y) (g : Y ≅ X) (K M : D pro A X),
    homPull pro A (h.hom ≫ g.hom) K M ≫
        homAction (Sites.hom pro A Z) ((pullComp pro A h.hom g.hom).inv.app K)
          ((pullComp pro A h.hom g.hom).hom.app M) =
      (pullComp pro A h.hom g.hom).hom.app (((Sites.hom pro A X).obj (op K)).obj M) ≫
        (pull pro A h.hom).map (homPull pro A g.hom K M) ≫
        homPull pro A h.hom ((pull pro A g.hom).obj K) ((pull pro A g.hom).obj M)


/-- Scalar balancing commutes with identity and composite geometric reindexing.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
structure ScalarTransportLaws (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (X : Scheme.{u}) : Prop where
  identity : ∀ K : D pro A X,
    (scalarPull pro φ (𝟙 X)).hom.app K ≫
        (scalar pro φ X).map ((pullId pro A X).hom.app K) =
      (pullId pro B X).hom.app ((scalar pro φ X).obj K)
  composition : ∀ {Z Y : Scheme.{u}} (h : Z ≅ Y) (g : Y ≅ X) (K : D pro A X),
    (pullComp pro B h.hom g.hom).hom.app ((scalar pro φ X).obj K) ≫
        (pull pro B h.hom).map ((scalarPull pro φ g.hom).hom.app K) ≫
        (scalarPull pro φ h.hom).hom.app ((pull pro A g.hom).obj K) =
      (scalarPull pro φ (h.hom ≫ g.hom)).hom.app K ≫
        (scalar pro φ Z).map ((pullComp pro A h.hom g.hom).hom.app K)

/-- All image and dualizing identifications obey identity and composition, including
changing the base scheme. The displayed maps are the specified counit mates.
Source: blueprint finite-free-extension proof, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality). -/
structure ImageTransportLaws (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X Z S : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ S) [QuasiCompact a] (c : Compactification a) : Prop where
  direct_identity : ∀ (sq : CommSq (𝟙 V) f f (𝟙 X)) (K : D pro A V),
    (directPull pro A sq).app K ≫ (push pro A f).map ((pullId pro A V).hom.app K) =
      (pullId pro A X).hom.app ((push pro A f).obj K)
  closed_identity : ∀ (sq : CommSq (𝟙 Z) i i (𝟙 X)) (M : D pro A X),
    Domain pro A X M →
    closedPull pro A sq M ≫ (exceptional pro A i).map ((pullId pro A X).hom.app M) =
      (pullId pro A Z).hom.app ((exceptional pro A i).obj M)
  omega_identity : ∀ sq : CommSq (𝟙 X) a a (𝟙 S),
    omegaPull pro A (IsPullback.of_horiz_isIso sq) c c =
      (pullId pro A X).hom.app (Sites.omega pro A c)
  direct_composition : ∀ {V' X' V'' X'' : Scheme.{u}}
      (f' : V' ⟶ X') (f'' : V'' ⟶ X'')
      (gV : V' ≅ V) (gX : X' ≅ X) (hV : V'' ≅ V') (hX : X'' ≅ X')
      (sg : CommSq gV.hom f' f gX.hom) (sh : CommSq hV.hom f'' f' hX.hom)
      (K : D pro A V),
    (pullComp pro A hX.hom gX.hom).hom.app ((push pro A f).obj K) ≫
        (pull pro A hX.hom).map ((directPull pro A sg).app K) ≫
        (directPull pro A sh).app ((pull pro A gV.hom).obj K) =
      (directPull pro A (sh.horiz_comp sg)).app K ≫
        (push pro A f'').map ((pullComp pro A hV.hom gV.hom).hom.app K)
  closed_composition : ∀ {Z' X' Z'' X'' : Scheme.{u}}
      (i' : Z' ⟶ X') (i'' : Z'' ⟶ X'') [IsClosedImmersion i'] [IsClosedImmersion i'']
      (gZ : Z' ≅ Z) (gX : X' ≅ X) (hZ : Z'' ≅ Z') (hX : X'' ≅ X')
      (sg : CommSq gZ.hom i' i gX.hom) (sh : CommSq hZ.hom i'' i' hX.hom)
      (M : D pro A X), Domain pro A X M →
    (pullComp pro A hZ.hom gZ.hom).hom.app ((exceptional pro A i).obj M) ≫
        (pull pro A hZ.hom).map (closedPull pro A sg M) ≫
        closedPull pro A sh ((pull pro A gX.hom).obj M) =
      closedPull pro A (sh.horiz_comp sg) M ≫
        (exceptional pro A i'').map ((pullComp pro A hX.hom gX.hom).hom.app M)
  omega_composition : ∀ {X' S' X'' S'' : Scheme.{u}}
      (a' : X' ⟶ S') (a'' : X'' ⟶ S'') [QuasiCompact a'] [QuasiCompact a'']
      (gX : X' ≅ X) (gS : S' ≅ S) (hX : X'' ≅ X') (hS : S'' ≅ S')
      (sg : CommSq gX.hom a' a gS.hom) (sh : CommSq hX.hom a'' a' hS.hom)
      (c' : Compactification a') (c'' : Compactification a''),
    (pullComp pro A hX.hom gX.hom).hom.app (Sites.omega pro A c) ≫
        (pull pro A hX.hom).map
          (omegaPull pro A (IsPullback.of_horiz_isIso sg) c c') ≫
        omegaPull pro A (IsPullback.of_horiz_isIso sh) c' c'' =
      omegaPull pro A (IsPullback.of_horiz_isIso (sh.horiz_comp sg)) c c''

/-- The five specified comparisons commute with scheme isomorphisms, on ordinary etale
inputs and on finite-Tor constructible pro-etale realizations. The compactification c'
is transported by gX and gS, and all coefficient maps retain their actual algebra action.
The square witnesses are equalities of scheme morphisms, so gS need not be the identity.
In particular semilinear geometric Frobenius is included.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, final paragraph
(blueprint: lem-sf-finite-free-comparison-isomorphism-naturality).

Proof:
1. Reindex both small sites by composition with the scheme isomorphism. Reindexing
   by its inverse is inverse, preserves coverings and constant ring actions. Apply
   lem-weil-pbc-site-equivalence-is-morphism-of-sites and
   lem-weil-pbc-ringed-presentation-transport to get the exact module equivalences,
   their termwise derived equivalences and preservation of K-injectives.
2. The tensor comparison sends reindexed x tensor y to E(x) tensor E(y).
   Its signed total preserves K-flatness by lem-sfb-exact-monoidal-equivalence-total-kflat.
   Lem-pur-derived-change-of-rings gives the scalar square, normalized on the same
   balanced tensors. Tensor reassociation, the unit and the Koszul symmetry commute.
3. The commuting f-square identifies inverse images. Conjugate their adjunctions
   to identify ordinary direct images with their actual counits. The transported
   open-extension formula is the same module where the object factors through the
   open, zero otherwise. Combine it with proper direct image for compact support.
   Conjugate the closed and compact-support adjunctions; det-sp-unique-right-adjoint
   fixes the right-adjoint comparisons by their counit equations.
4. For the direct, closed and structure comparisons, transpose after transport.
   The defining equation is L_S(m) followed by epsilon_S equals the scalar-extended
   epsilon_R preceded by inverse coefficient comparison. The tensor and counit
   identifications of steps 2 and 3 give the primed equation. Injectivity of the
   Hom bijection proves equality of each specified map, without assuming that a
   mate of an arbitrary isomorphism is an isomorphism. The compact-support scalar
   comparison is precisely proper projection followed by open extension by zero.
5. Lem-coef-monoidal-square-hom-transport identifies the evaluation transposes.
   Lem-sfb-ringed-derived-monoidal-comparisons supplies the canonical monoidal square.
   Thus both v maps have the same transpose, the transported evaluation. Compose
   with Hom of the already identified u map to obtain the beta square.
6. Evaluation is the closed counit. Its symmetry-transpose is the double-dual arrow
   of lem-weil-duality-pairing. The same tensor, symmetry and Hom identifications
   therefore preserve both arrows and all their coefficient squares.
7. On pro-etale objects reindexing also commutes with the etale inclusion and the
   colimit formula for nu*. Conjugation gives compatibility with Rnu*. Hence the
   specified composites nu* G Rnu* and their counits have the same transports.
   Isomorphism pullback reindexes finite locally constant stratifications and
   preserves every tensor-vanishing test, so the equalities restrict to the given
   finite-Tor constructible realizations. No unbounded pro-etale adjoint is used.
8. Twice reindexing is reindexing by the composite. Pure tensors and evaluation
   identify its tensor, scalar and Hom comparisons. Uniqueness of counit-compatible
   right-adjoint identification gives the same statement for all mates. Identity
   reindexing is the identity. Applying this to id times Spec(gamma), where gamma
   is a field automorphism fixing the finite base, gives the semilinear instance
   of def-weil-global-geometric-frobenius, with inverse gamma inverse.
-/
theorem finite_free_comparison_isomorphism_naturality
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B]
    (_hA : ∃ n : ℕ, 0 < n ∧ (l ^ n : A) = 0)
    (_hB : ∃ n : ℕ, 0 < n ∧ (l ^ n : B) = 0)
    (V X Z : Scheme.{u})
    [V.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))] [Z.Over (Spec (.of F.k))]
    [IsSeparated (V ↘ Spec (.of F.k))] [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    [IsSeparated (X ↘ Spec (.of F.k))] [LocallyOfFiniteType (X ↘ Spec (.of F.k))]
    [QuasiCompact (X ↘ Spec (.of F.k))]
    [IsSeparated (Z ↘ Spec (.of F.k))] [LocallyOfFiniteType (Z ↘ Spec (.of F.k))]
    [QuasiCompact (Z ↘ Spec (.of F.k))]
    (f : V ⟶ X) [f.IsOver (Spec (.of F.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of F.k))]
    (c : Compactification (X ↘ Spec (.of F.k))) :
    ∀ pro : Bool,
      HomTransportLaws pro A X ∧ HomTransportLaws pro B X ∧
      HomTransportLaws pro A V ∧ HomTransportLaws pro B V ∧
      HomTransportLaws pro A Z ∧ HomTransportLaws pro B Z ∧
      HomTransportLaws pro A (Spec (.of F.k)) ∧
      HomTransportLaws pro B (Spec (.of F.k)) ∧
      ScalarTransportLaws pro (algebraMap A B) X ∧
      ScalarTransportLaws pro (algebraMap A B) V ∧
      ScalarTransportLaws pro (algebraMap A B) Z ∧
      ScalarTransportLaws pro (algebraMap A B) (Spec (.of F.k)) ∧
      ImageTransportLaws pro A f i (X ↘ Spec (.of F.k)) c ∧
      ImageTransportLaws pro B f i (X ↘ Spec (.of F.k)) c ∧
      ∃ μ : ∀ W : Scheme.{u}, TensorComparison pro (algebraMap A B) W,
        (∀ W : Scheme.{u}, NormalizedTensor pro (algebraMap A B) W (μ W)) ∧
        ∀ (V' X' Z' S' : Scheme.{u}) (f' : V' ⟶ X') (i' : Z' ⟶ X')
          [IsClosedImmersion i'] (a' : X' ⟶ S') [QuasiCompact a']
          (gV : V' ≅ V) (gX : X' ≅ X) (gZ : Z' ≅ Z) (gS : S' ≅ Spec (.of F.k))
          (sf : CommSq gV.hom f' f gX.hom) (si : CommSq gZ.hom i' i gX.hom)
          (sa : CommSq gX.hom a' (X ↘ Spec (.of F.k)) gS.hom),
          SquareLaws pro (algebraMap A B) gV gX gZ gS sf si
            (IsPullback.of_horiz_isIso sa) c
            (c.ofIsPullback (IsPullback.of_horiz_isIso sa)) (μ X) (μ X') := by
  sorry

end WeilConjectures.FiniteFreeIsomorphismNaturality
