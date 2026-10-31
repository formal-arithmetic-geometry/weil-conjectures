/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionCoherence
import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
import WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ScalarSixNormalizedImmersion
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.SecSmoothPurity.Transport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Compact-support, exceptional and coefficient comparisons on native condensed categories

Source: blueprint latest, sk-thm-sbc-coefficients/fix-lem-exchanges, clauses 1, 2, 4;
sk-prop-scalar-six; sk-prop-sp-composition; sk-prop-sp-purity-bc
(blueprint: lem-pur-condensed-operation-comparisons).

The full subcategories are the published bounded constructible finite-Tor categories of
ordinary derived internal modules over the coefficient ring pulled from the condensed point.
The selected composition and exchange maps are fixed by the dependency's refinement and
proper/open normalization equations. Selecting them does not choose arbitrary isomorphisms.
Right adjoints are quantified together with their adjunctions; their conjugates and exceptional
exchange maps below are actual adjunction constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace OperationComparisons

/-- Exactly the four coefficient stages in the statement, invariant under coefficient
isomorphism. The finite quotient uses the recorded uniformizer and the discrete topology.
Source: opening coefficient convention (blueprint: lem-pur-condensed-operation-comparisons). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
    Nonempty (Mon.mk Λ.X ≅ Mon.mk
      (cartesianFinitePointRing (ULift.{u} (Padic.coefficientExtensionRing ell E.1 n))))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.1))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

variable {k : Type u} [Field k] {Λ : ScalarSixRing.{u}}

/-- Preservation and the canonical normalized comparison families supplied by composition.
This first projection is proof data, not a choice of a new functor.
Source: composition theorem, preservation (blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev preserves (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  H.preserves (X := X) (Y := Y) f c

/-- The model compositor fixed by proper/open normalization and common refinements.
Its normalization determines every component, hence this is a canonical-data choice.
Source: composition theorem, alpha (blueprint: lem-pur-condensed-operation-comparisons). -/
@[irreducible] def modelComposition (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ.X e :=
  H.comp (X := X) (Y := Y) (Z := Z) f g c d e

/-- Pullback preservation, the proof field in the same coherent comparison family.
Source: composition theorem, arbitrary base maps
(blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev pullPreserves (H : CompactSupportComposition.CoherentData Λ.X k)
    (X Y : SepFinType k) (v : X.obj.left ⟶ Y.obj.left) :=
  H.pullback_preserves X Y v

/-- The exchange fixed by the canonical proper exchange, inverse open mate and model
comparison. All three normalizations belong to the same dependency witness as alpha.
Source: composition theorem, B (blueprint: lem-pur-condensed-operation-comparisons). -/
@[irreducible] def modelExchange (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          moduleObjectDerivedPullback Λ.X v) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ.X u ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) :=
  H.exchange (X := X) (Y := Y) (X' := X') (Y' := Y') (f := f) (f' := f') sq c d

/-- The fully faithful inclusion of the existing Dctf category in its ambient derived category.
Source: full-subcategory convention (blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev inclusion (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Γ.X X) :=
  ObjectProperty.ι _

/-- The canonical inclusion of Dctf in its localizing closure, with unchanged objects and maps.
Source: composition theorem, restriction to C
(blueprint: lem-pur-condensed-operation-comparisons). -/
def toLocalizing (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      (localizingClosureProEtale Γ.X X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- The chosen compactification functor, restricted to the actual Dctf full subcategories.
Source: sk-thm-existence (blueprint: lem-pur-condensed-operation-comparisons). -/
def lower (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y : SepFinType k} (f : X ⟶ Y) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left :=
  ObjectProperty.lift _
    (inclusion Λ X.obj.left ⋙
      rightDerivedLowerShriekOfCompactification Λ.X (compactificationOverField f.hom))
    (fun K ↦ (preserves H f (compactificationOverField f.hom)).2 K.obj K.property)

/-- Derived pullback restricted by the dependency's preservation assertion. The underlying
scheme map is arbitrary and is not required to be a morphism over k.
Source: composition theorem, U and V (blueprint: lem-pur-condensed-operation-comparisons). -/
def pull (H : CompactSupportComposition.CoherentData Λ.X k)
    (X Y : SepFinType k) (v : X.obj.left ⟶ Y.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ObjectProperty.lift _ (inclusion Λ Y.obj.left ⋙ moduleObjectDerivedPullback Λ.X v)
    (fun K ↦ (pullPreserves H X Y v).2 K.obj K.property)

/-- Alpha is the restriction of exactly the normalized dependency compositor.
Source: first displayed comparison (blueprint: lem-pur-condensed-operation-comparisons). -/
def composition (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lower H f ⋙ lower H g ≅ lower H (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Z.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelComposition H f g (compactificationOverField f.hom)
        (compactificationOverField g.hom) (compactificationOverField (f ≫ g).hom)))

/-- B is the restriction of exactly the normalized dependency exchange. Cartesian squares
are given by IsPullback, so this includes all their realizations, not only a chosen pullback.
Source: compact-support exchange (blueprint: lem-pur-condensed-operation-comparisons). -/
def exchange (H : CompactSupportComposition.CoherentData Λ.X k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v) :
    lower H f ⋙ pull H Y' Y v ≅ pull H X' X u ⋙ lower H f' :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Y'.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelExchange H (X := X) (Y := Y) (X' := X') (Y' := Y')
        (f := f) (f' := f') sq (compactificationOverField f.hom)
        (compactificationOverField f'.hom)))

/-- The inherited identity pullback comparison, retaining its canonical unit normalization.
Source: identity square (blueprint: lem-pur-condensed-operation-comparisons). -/
def pullId (H : CompactSupportComposition.CoherentData Λ.X k) (X : SepFinType k) :
    pull H X X (𝟙 X.obj.left) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ X.obj.left) (leftDerivedUpperStarId Λ.X X.obj.left))

/-- The canonical inherited pullback compositor used in successive base change.
Source: vertical pasting (blueprint: lem-pur-condensed-operation-comparisons). -/
def pullComp (H : CompactSupportComposition.CoherentData Λ.X k) (X Y Z : SepFinType k)
    (f : X.obj.left ⟶ Y.obj.left) (g : Y.obj.left ⟶ Z.obj.left) :
    pull H X Z (f ≫ g) ≅ pull H Y Z g ⋙ pull H X Y f :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ Z.obj.left) (leftDerivedUpperStarComp Λ.X f g))

/-- The scalar/pullback comparison on total left derived pullbacks: transport the published
normalized theta through exact-pullback localization. This is j, in the statement's direction.
Source: det-prop-scalar-six-pullback (blueprint: lem-pur-condensed-operation-comparisons). -/
def scalarPull {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ') {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Γ.X f ⋙ scalarSixChange a X ≅
      scalarSixChange a Y ⋙ moduleObjectDerivedPullback Γ'.X f :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Γ.X f) _ ≪≫
    scalarDirectImagePullbackData.theta a f ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Γ'.X f).symm

/-- The conjugate of alpha under the specified composite adjunction and the gf adjunction.
The right adjoint to F_f then F_g is E_g then E_f in Lean's functor order.
Source: first counit identity (blueprint: lem-pur-condensed-operation-comparisons). -/
def conjugate {X Y Z : SepFinType k} (H : CompactSupportComposition.CoherentData Λ.X k)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Eg : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left}
    {Egf : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    (af : lower H f ⊣ Ef) (ag : lower H g ⊣ Eg) (agf : lower H (f ≫ g) ⊣ Egf) :
    Egf ≅ Eg ⋙ Ef :=
  conjugateIsoEquiv agf (af.comp ag) (composition H f g)

/-- The transpose of inverse B followed by the pulled-back counit. This construction is
made for every square; invertibility is a separate geometric assertion below.
Source: second counit identity (blueprint: lem-pur-condensed-operation-comparisons). -/
def exceptional {X Y X' Y' : SepFinType k}
    (H : CompactSupportComposition.CoherentData Λ.X k) {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Ef' : ConstantModelConstructibleFiniteTor Λ.X Y'.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X'.obj.left}
    (af : lower H f ⊣ Ef) (af' : lower H f' ⊣ Ef') :
    Ef ⋙ pull H X' X u ⟶ pull H Y' Y v ⋙ Ef' :=
  (mateEquiv af af' (TwoSquare.mk _ _ _ _ (exchange H sq).inv)).natTrans

/-- The simultaneous data on the four native coefficient stages. H retains *all* canonicity,
independence, unit, associativity and composition/exchange equations of the dependency.
Each right adjoint is supplied with its adjunction on Dctf itself. Scalar preservation is
stated for the actual ordinary derived extension, without completed or discrete replacements.
Source: standing operations and coefficient change
(blueprint: lem-pur-condensed-operation-comparisons). -/
structure Data (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] where
  coherent : ∀ (Γ : ScalarSixRing.{u}), IsCoefficient ell Γ →
    CompactSupportComposition.CoherentData Γ.X D.k
  right : ∀ (Γ : ScalarSixRing.{u}) (_hΓ : IsCoefficient ell Γ)
    {X Y : SepFinType D.k} (_f : X ⟶ Y),
    ConstantModelConstructibleFiniteTor Γ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Γ.X X.obj.left
  adj : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y : SepFinType D.k} (f : X ⟶ Y), lower (coherent Γ hΓ) f ⊣ right Γ hΓ f
  scalar_preserves : ∀ {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (_ha : ListedCoefficientMap ell a) (_hΓ : IsCoefficient ell Γ)
    (_hΓ' : IsCoefficient ell Γ') (X : SepFinType D.k)
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    constantModelBoundedConstructible Γ'.X X.obj.left
        ((scalarSixChange a X.obj.left).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.obj.left).obj K.obj)

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]

/-- The actual scalar image, with only its preservation proof supplied by the operations datum.
Source: T on the constructible categories
(blueprint: lem-pur-condensed-operation-comparisons). -/
def scalar (S : Data D ell) {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ)
    (hΓ' : IsCoefficient ell Γ') (X : SepFinType D.k) :
    ConstantModelConstructibleFiniteTor Γ.X X.obj.left ⥤
      ConstantModelConstructibleFiniteTor Γ'.X X.obj.left :=
  ObjectProperty.lift _ (inclusion Γ X.obj.left ⋙ scalarSixChange a X.obj.left)
    (S.scalar_preserves a ha hΓ hΓ' X)

/-- The specified compact-support coefficient arrow, restricted by full faithfulness.
Its ambient image is exactly scalarCompactSupportMap for the chosen compactification.
Source: b of det-prop-scalar-six-compact-support
(blueprint: lem-pur-condensed-operation-comparisons). -/
def scalarLower (S : Data D ell) {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    {X Y : SepFinType D.k} (f : X ⟶ Y) :
    lower (S.coherent Γ hΓ) f ⋙ scalar S a ha hΓ hΓ' Y ⟶
      scalar S a ha hΓ hΓ' X ⋙ lower (S.coherent Γ' hΓ') f :=
  ((Functor.whiskeringRight _ _ _).obj (inclusion Γ' Y.obj.left)).preimage
    (Functor.whiskerLeft (inclusion Γ X.obj.left)
      (scalarCompactSupportMap a (compactificationOverField f.hom).i
        (compactificationOverField f.hom).g))

/-- The specified scalar/pullback comparison on the full constructible categories.
Source: j_u and j_v (blueprint: lem-pur-condensed-operation-comparisons). -/
def scalarPullIso (S : Data D ell) {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    (X Y : SepFinType D.k) (v : X.obj.left ⟶ Y.obj.left) :
    pull (S.coherent Γ hΓ) X Y v ⋙ scalar S a ha hΓ hΓ' X ≅
      scalar S a ha hΓ hΓ' Y ⋙ pull (S.coherent Γ' hΓ') X Y v :=
  Functor.fullyFaithfulCancelRight (inclusion Γ' X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Γ Y.obj.left) (scalarPull a v))

/-- The requested equations for the specified comparisons, simultaneously for all
coefficients, morphisms and squares. Naturality and compactification independence of alpha
and B are already part of S.coherent; the equations below add the counits, identity and
successive-base-change laws, smooth exceptional invertibility and the scalar rectangle.
The scalar composition and pasted-rectangle equations express compatibility with alpha
and with successive base changes using these same maps.
Source: all clauses (blueprint: lem-pur-condensed-operation-comparisons). -/
structure Laws (S : Data D ell) : Prop where
  composition_counit : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : ConstantModelConstructibleFiniteTor Γ.X Z.obj.left),
    (composition (S.coherent Γ hΓ) f g).hom.app ((S.right Γ hΓ (f ≫ g)).obj K) ≫
        (S.adj Γ hΓ (f ≫ g)).counit.app K =
      (lower (S.coherent Γ hΓ) f ⋙ lower (S.coherent Γ hΓ) g).map
          ((conjugate (S.coherent Γ hΓ) f g
            (S.adj Γ hΓ f) (S.adj Γ hΓ g) (S.adj Γ hΓ (f ≫ g))).hom.app K) ≫
        (lower (S.coherent Γ hΓ) g).map
          ((S.adj Γ hΓ f).counit.app ((S.right Γ hΓ g).obj K)) ≫
        (S.adj Γ hΓ g).counit.app K
  exchange_identity : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y : SepFinType D.k} (f : X ⟶ Y)
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (exchange (S.coherent Γ hΓ) (f := f) (f' := f)
        (IsPullback.id_horiz f.hom.left)).hom.app K ≫
        (lower (S.coherent Γ hΓ) f).map ((pullId (S.coherent Γ hΓ) X).hom.app K) =
      (pullId (S.coherent Γ hΓ) Y).hom.app ((lower (S.coherent Γ hΓ) f).obj K)
  exchange_pasting : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y X' Y' X'' Y'' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    {u' : X''.obj.left ⟶ X'.obj.left} {v' : Y''.obj.left ⟶ Y'.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    (sq' : IsPullback u' f''.hom.left f'.hom.left v')
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (exchange (S.coherent Γ hΓ) (f := f) (f' := f'') (sq'.paste_horiz sq)).hom.app K ≫
        (lower (S.coherent Γ hΓ) f'').map
          ((pullComp (S.coherent Γ hΓ) X'' X' X u' u).hom.app K) =
      (pullComp (S.coherent Γ hΓ) Y'' Y' Y v' v).hom.app
          ((lower (S.coherent Γ hΓ) f).obj K) ≫
        (pull (S.coherent Γ hΓ) Y'' Y' v').map
          ((exchange (S.coherent Γ hΓ) sq).hom.app K) ≫
        (exchange (S.coherent Γ hΓ) sq').hom.app
          ((pull (S.coherent Γ hΓ) X' X u).obj K)
  smooth_exceptional : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y X' Y' : SepFinType D.k} {f : X ⟶ Y} {f' : X' ⟶ Y'} [Smooth f.hom.left]
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v),
    IsIso (exceptional (S.coherent Γ hΓ) sq (S.adj Γ hΓ f) (S.adj Γ hΓ f'))
  exceptional_counit : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsCoefficient ell Γ)
    {X Y X' Y' : SepFinType D.k} {f : X ⟶ Y} {f' : X' ⟶ Y'} [Smooth f.hom.left]
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    (K : ConstantModelConstructibleFiniteTor Γ.X Y.obj.left),
    (exchange (S.coherent Γ hΓ) sq).hom.app ((S.right Γ hΓ f).obj K) ≫
        (lower (S.coherent Γ hΓ) f').map
          ((exceptional (S.coherent Γ hΓ) sq
            (S.adj Γ hΓ f) (S.adj Γ hΓ f')).app K) ≫
        (S.adj Γ hΓ f').counit.app ((pull (S.coherent Γ hΓ) Y' Y v).obj K) =
      (pull (S.coherent Γ hΓ) Y' Y v).map ((S.adj Γ hΓ f).counit.app K)
  scalar_isIso : ∀ {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    {X Y : SepFinType D.k} (f : X ⟶ Y), IsIso (scalarLower S a ha hΓ hΓ' f)
  scalar_exchange : ∀ {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    {X Y X' Y' : SepFinType D.k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (scalar S a ha hΓ hΓ' Y').map ((exchange (S.coherent Γ hΓ) sq).hom.app K) ≫
        (scalarLower S a ha hΓ hΓ' f').app ((pull (S.coherent Γ hΓ) X' X u).obj K) ≫
        (lower (S.coherent Γ' hΓ') f').map
          ((scalarPullIso S a ha hΓ hΓ' X' X u).hom.app K) =
      (scalarPullIso S a ha hΓ hΓ' Y' Y v).hom.app
          ((lower (S.coherent Γ hΓ) f).obj K) ≫
        (pull (S.coherent Γ' hΓ') Y' Y v).map ((scalarLower S a ha hΓ hΓ' f).app K) ≫
        (exchange (S.coherent Γ' hΓ') sq).hom.app ((scalar S a ha hΓ hΓ' X).obj K)
  scalar_composition : ∀ {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (scalar S a ha hΓ hΓ' Z).map ((composition (S.coherent Γ hΓ) f g).hom.app K) ≫
        (scalarLower S a ha hΓ hΓ' (f ≫ g)).app K =
      (scalarLower S a ha hΓ hΓ' g).app ((lower (S.coherent Γ hΓ) f).obj K) ≫
        (lower (S.coherent Γ' hΓ') g).map ((scalarLower S a ha hΓ hΓ' f).app K) ≫
        (composition (S.coherent Γ' hΓ') f g).hom.app ((scalar S a ha hΓ hΓ' X).obj K)
  scalar_exchange_pasting : ∀ {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ')
    (ha : ListedCoefficientMap ell a) (hΓ : IsCoefficient ell Γ) (hΓ' : IsCoefficient ell Γ')
    {X Y X' Y' X'' Y'' : SepFinType D.k}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {u : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    {u' : X''.obj.left ⟶ X'.obj.left} {v' : Y''.obj.left ⟶ Y'.obj.left}
    (sq : IsPullback u f'.hom.left f.hom.left v)
    (sq' : IsPullback u' f''.hom.left f'.hom.left v')
    (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (scalar S a ha hΓ hΓ' Y'').map
        ((pull (S.coherent Γ hΓ) Y'' Y' v').map
            ((exchange (S.coherent Γ hΓ) sq).hom.app K) ≫
          (exchange (S.coherent Γ hΓ) sq').hom.app
            ((pull (S.coherent Γ hΓ) X' X u).obj K)) ≫
        (scalarLower S a ha hΓ hΓ' f'').app
          ((pull (S.coherent Γ hΓ) X'' X' u').obj
            ((pull (S.coherent Γ hΓ) X' X u).obj K)) ≫
        (lower (S.coherent Γ' hΓ') f'').map
          ((scalarPullIso S a ha hΓ hΓ' X'' X' u').hom.app
              ((pull (S.coherent Γ hΓ) X' X u).obj K) ≫
            (pull (S.coherent Γ' hΓ') X'' X' u').map
              ((scalarPullIso S a ha hΓ hΓ' X' X u).hom.app K)) =
      (scalarPullIso S a ha hΓ hΓ' Y'' Y' v').hom.app
          ((pull (S.coherent Γ hΓ) Y' Y v).obj ((lower (S.coherent Γ hΓ) f).obj K)) ≫
        (pull (S.coherent Γ' hΓ') Y'' Y' v').map
          ((scalarPullIso S a ha hΓ hΓ' Y' Y v).hom.app
            ((lower (S.coherent Γ hΓ) f).obj K)) ≫
        (pull (S.coherent Γ' hΓ') Y' Y v ⋙ pull (S.coherent Γ' hΓ') Y'' Y' v').map
          ((scalarLower S a ha hΓ hΓ' f).app K) ≫
        (pull (S.coherent Γ' hΓ') Y'' Y' v').map
          ((exchange (S.coherent Γ' hΓ') sq).hom.app ((scalar S a ha hΓ hΓ' X).obj K)) ≫
        (exchange (S.coherent Γ' hΓ') sq').hom.app
          ((pull (S.coherent Γ' hΓ') X' X u).obj ((scalar S a ha hΓ hΓ' X).obj K))

/-- The native condensed compact-support comparisons, their conjugate and exceptional counit
identities, smooth exceptional invertibility, and the scalar/exchange rectangle with its
composition and pasting coherences. The base datum retains q = p^a, a >= 1 and the specified
algebraic closure. Every coefficient stage retains the finite-subextension-valued convention.
All base arrows in the equations are arbitrary underlying scheme maps; in particular the
same maps and equations apply to compatible semilinear isomorphisms.

Source: latest blueprint fix-lem-exchanges, clauses 1, 2, 4, with sk-prop-scalar-six,
sk-prop-sp-composition and sk-prop-sp-purity-bc
(blueprint: lem-pur-condensed-operation-comparisons).

Proof plan, the ten steps of the node:
1. Use sk-thm-existence on Dctf, then restrict sk-thm-sf-comp-composition. Its normalization
   fixes alpha and B, and supplies independence, naturality, associativity, units and the
   stacked-square composition/exchange law even for base maps not over k.
2. Compose the adjunctions for f and g. Conjugate alpha using the gf adjunction and the
   composite adjunction (def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-conjugate).
   The mate-counit identity gives composition_counit; conjugation and mate pasting give its
   units and associativity (lem-amb-mate-unit-counit, lem-weil-pbc-mate-pasting).
3. On a compactification, B is proper exchange followed by proper image of the inverse
   open mate (def-sfb-compact-support-base-change-maps). Proper and open mate pasting, with
   prop-sfb-module-left-derived-upper-star-comp and internal-module transport, gives their
   identity and successive-base-change equations without flatness assumptions.
4. Substitute these two formulas in B. Naturality moves the middle open map through proper
   exchange, giving exchange_pasting. Independence identifies arbitrary models. The same
   expansion respects alpha. Identity models give exchange_identity.
5. Transpose inverse B using the specified adjunctions. The mate-counit identity followed
   by cancellation of B inverse with B is exceptional_counit; no assertion that an arbitrary
   mate preserves isomorphisms is used.
6. For smooth f of pure relative dimension use prop-pur-condensed-purity-base-change.
   For varying relative dimension use its open loci, provided by
   sbc-lem-smooth-relative-dimension-locally-constant. They remain finite type since the
   standing schemes are Noetherian (lem-weil-pbc-finite-type-over-noetherian). Composition
   conjugation and exchange pasting identify the restricted exceptional maps. The pure
   case and dimension-zero purity make these restrictions invertible. Apply
   lem-sfb-sheaf-cover-local-isomorphism to every cohomology of the cone, obtaining zero
   cone and smooth_exceptional, including the empty scheme.
7. The scalar open comparison is normalized by inverse theta
   (lem-sfb-scalar-six-normalized-immersion). Restrict the mixed scalar/open rectangle to
   the open: both paths are the same scalar/pullback comparison by
   lem-sfb-scalar-pullback-square-coherence. Faithfulness of locally closed extension and
   internal-module transport proves the rectangle before restriction.
8. For the proper factor apply lem-sfb-scalar-geometric-exchange-rectangle to the specified
   unit/pullback/counit scalar mate. Identify its lambda with inverse theta using
   lem-sfb-scalar-six-derived-pullback-normalization and
   lem-sfb-kflat-scalar-comparison-normalization. Paste with step 7 and apply proper image.
   The specified resulting maps are scalarCompactSupportMap and B, giving scalar_exchange.
   The coefficient hypotheses ensure scalar preservation and scalar_isIso; finite
   cohomological dimension of D.k follows from its being an algebraic closure.
9. Paste two copies of scalar_exchange and cancel their shared edges. Pullback-compositor
   and theta coherence gives scalar_exchange_pasting and the outer-square equation.
   Scalar compact-support composition and the composition/exchange law for B identify the
   stacked-square pasting with alpha; scalar_composition records this same b coherence.
10. For compatible semilinear isomorphisms use their actual pro-etale pullbacks and the
   coefficient identifications from the point (sk-prop-sfb-cartesian-coefficients). They
   are inverse equivalences. Apply lem-weil-mate-iso-along-equivalences to inverse B to get
   the same invertibility assertion; steps 2--5 and 7--9 apply to these scheme maps. -/
theorem condensedOperationComparisons (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p) :
    ∃ S : Data D ell, Laws S := by
  sorry

end OperationComparisons
end AlgebraicGeometry.ProEtale.CondensedRing
