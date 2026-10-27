/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportExchangeTransport
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Paper.RelativeExternalPowerRegrouping
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import WeilConjectures.Compactification.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange

/-! # Composition and exchange factors of a relative product

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative,
relative-product proof (1),(3); sec-smooth-purity/sk-prop-an
(blueprint: lem-pur-relative-product-geometric-factors).

All objects are expressed in ordinary fixed-module coordinates. The actual canonical
coefficient equivalence reads the recorded intrinsic finite-Tor predicate in these
coordinates. The exchange is the specified proper-mate/open-extension composite.

## Main statements

* `relative_product_geometric_factors`: geometry, constructibility and retained origins.
* `relative_product_composition_exchange`: normalized transport, independence and inverses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory CategoryTheory.Functor

namespace WeilConjectures.RelativeProduct

/-- Finiteness is supplied by the positive finite coefficient level.
Source: finite coefficient conventions
(blueprint: lem-pur-relative-product-geometric-factors). -/
instance finiteRing (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The prescribed size lift retains the finite coefficient ring.
Source: finite coefficient conventions
(blueprint: lem-pur-relative-product-geometric-factors). -/
instance finiteCoefficient (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- Ordinary fixed-module coordinates for the same small pro-etale derived category.
Source: finite coefficient conventions
(blueprint: lem-pur-relative-product-geometric-factors). -/
abbrev D (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))

/-- Read the existing intrinsic finite-Tor predicate through its canonical equivalence.
Source: finite coefficient conventions and def-weil-finite-tor-amplitude
(blueprint: lem-pur-relative-product-geometric-factors). -/
def ctf (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (K : D P T) : Prop :=
  finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
    ((sfIntrinsicDerivedEquivalence T P.Ring).functor.obj K)

/-- Read existing bounded constructibility through the same coefficient equivalence.
Source: finite coefficient conventions
(blueprint: lem-pur-relative-product-geometric-factors). -/
def boundedConstructible (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (K : D P T) : Prop :=
  intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level P.level_pos T
    ((sfIntrinsicDerivedEquivalence T P.Ring).functor.obj K)

/-- The actual derived external tensor on the chosen scheme fibre product.
Source: relative-product proof, input to (1)
(blueprint: lem-pur-relative-product-geometric-factors). -/
def external (P : PurityFiniteSetting.{u}) {X Y B : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (K : D P X) (L : D P Y) : D P (pullback f g) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (pullback.fst f g)).leftDerivedFunctor.obj K ⊗
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (pullback.snd f g)).leftDerivedFunctor.obj L

/-- Forget the retained pair only to evaluate natural transformations on the full origin class.
Source: relative-product proof, arbitrary witnessed presentations
(blueprint: lem-pur-relative-product-geometric-factors). -/
def origin (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (K : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (W : FixedEtaleOriginWitness T P.Coefficient K) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory :=
  ⟨K.obj, W.complex.obj, W.complex.property, ⟨W.iso⟩⟩

/-- Pull back the specified witness using the canonical derived site comparison.
Source: relative-product proof (3), source of the base-changed compact support
(blueprint: lem-pur-relative-product-geometric-factors). -/
def pullbackOrigin (P : PurityFiniteSetting.{u}) {X T : Scheme.{u}} (a : T ⟶ X)
    (K : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (W : FixedEtaleOriginWitness X P.Coefficient K) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory :=
  ⟨(ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K.obj,
    ((AlgebraicGeometry.Etale.upperStar
      (ModuleCat.{u + 1} P.Coefficient) a).mapDerivedCategoryPlus.obj W.complex).obj,
    ((AlgebraicGeometry.Etale.upperStar
      (ModuleCat.{u + 1} P.Coefficient) a).mapDerivedCategoryPlus.obj W.complex).property,
    ⟨(ProEtale.leftDerivedUpperStarComparisonIso a P.Coefficient).app W.complex ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.mapIso W.iso⟩⟩

/-- Insert the actual finite operations into the recorded supplied-domain exchange.
The proper pullback square supplies theta, its derived adjunctions supply the mate,
and the inverse open base-change comparison supplies beta. Thus this is the specified
proper unit-square-counit exchange followed by open extension, with no supplied map.
Source: relative-product proof (3), def-exchange-projection finite-level formula
(blueprint: lem-pur-relative-product-geometric-factors). -/
def exchange (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) c.i).mapDerivedCategory
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq).i).mapDerivedCategory
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) c.g).leftDerivedFunctor
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) c.g).rightDerivedFunctor
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) c.g)
    (ProEtale.upperStar
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq).g).leftDerivedFunctor
    (ProEtale.lowerStar
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq).g).rightDerivedFunctor
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq).g)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g').leftDerivedFunctor
    (ProEtale.upperStar
      (ModuleCat.{u + 1} P.Coefficient) (pullback.fst c.g g)).leftDerivedFunctor
    (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient)
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (ProEtale.leftDerivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} P.Coefficient) (c.isPullback_i_ofIsPullback sq)).symm

/-- The source compactification comparison is the canonical origin comparison pulled back by g.
Source: relative-product proof (3), independence under canonical comparisons
(blueprint: lem-pur-relative-product-geometric-factors). -/
def sourceComparison (P : PurityFiniteSetting.{u}) {X Y B : Scheme.{u}}
    {f : X ⟶ B} (g : Y ⟶ B) [QuasiCompact f] (c d : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (W : FixedEtaleOriginWitness X P.Coefficient K) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.mapIso
    ((ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso
      P.Coefficient c d).app (origin P X K W))

/-- The target comparison is the canonical primed compactification comparison at La* K.
Source: relative-product proof (3), independence under canonical comparisons
(blueprint: lem-pur-relative-product-geometric-factors). -/
def targetComparison (P : PurityFiniteSetting.{u}) {X Y B : Scheme.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} [QuasiCompact f] (c d : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (W : FixedEtaleOriginWitness X P.Coefficient K) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso P.Coefficient
    (c.ofIsPullback (IsPullback.of_hasPullback f g))
    (d.ofIsPullback (IsPullback.of_hasPullback f g))).app
      (pullbackOrigin P (pullback.fst f g) K W)

/-- The canonical compositor on the full bounded-below origin categories. The compactifications
supply existence, while the published choice-independent origin compositor supplies alpha.
Source: relative-product proof (1)
(blueprint: lem-pur-relative-product-geometric-factors). -/
def composition (P : PurityFiniteSetting.{u}) {X Y B : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) [QuasiCompact f] [QuasiCompact g]
    (cb : Compactification (pullback.snd f g)) (cg : Compactification g)
    (ch : Compactification (pullback.snd f g ≫ g)) :=
  letI := cb.hasCompactification
  letI := cg.hasCompactification
  letI := ch.hasCompactification
  ProEtale.originComposition P.Coefficient (pullback.snd f g) g

/-- Geometric and witnessed domains of the two relative-product factors.
Source: relative-product proof (1),(3)
(blueprint: lem-pur-relative-product-geometric-factors).

Proof:
1. Apply lem-pur-relative-external-power-regrouping to (X,K),(Y,L), and to the
one-factor family (Y,L). Stability under base change and composition gives the displayed
separated finite-type domains, and the external tensor is finite-Tor constructible.
2. Membership in Dctf gives bounded constructibility. Apply
lem-sf-proetale-constructible-origin, clause (ii), to K and the external tensor.
Its bounded etale antecedents give the retained FixedEtaleOriginWitness pairs.
3. The geometric domains allow prop-compactification-refinement to supply the
compactifications used in the subsequent factors statement. No exceptional-adjoint
domain or Verdier-duality axiom is used. -/
theorem relative_product_geometric_factors (P : PurityFiniteSetting.{u})
    (B X Y : Scheme.{u}) (s : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (f : X ⟶ B) (g : Y ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : D P X) (L : D P Y) (_hK : ctf P X K) (_hL : ctf P Y L) :
    (IsSeparated (f ≫ s) ∧ LocallyOfFiniteType (f ≫ s) ∧ QuasiCompact (f ≫ s)) ∧
    (IsSeparated (g ≫ s) ∧ LocallyOfFiniteType (g ≫ s) ∧ QuasiCompact (g ≫ s)) ∧
    (IsSeparated (pullback.fst f g ≫ f ≫ s) ∧
      LocallyOfFiniteType (pullback.fst f g ≫ f ≫ s) ∧
      QuasiCompact (pullback.fst f g ≫ f ≫ s)) ∧
    (IsSeparated (pullback.fst f g) ∧ LocallyOfFiniteType (pullback.fst f g) ∧
      QuasiCompact (pullback.fst f g)) ∧
    (IsSeparated (pullback.snd f g) ∧ LocallyOfFiniteType (pullback.snd f g) ∧
      QuasiCompact (pullback.snd f g)) ∧
    (IsSeparated (pullback.fst f g ≫ f) ∧ LocallyOfFiniteType (pullback.fst f g ≫ f) ∧
      QuasiCompact (pullback.fst f g ≫ f)) ∧
    boundedConstructible P X K ∧ boundedConstructible P (pullback f g) (external P f g K L) ∧
    (∃ Kp : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)),
      Kp.obj = K ∧ Nonempty (FixedEtaleOriginWitness X P.Coefficient Kp)) ∧
    (∃ Hp : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology (pullback f g)) (ModuleCat.{u + 1} P.Coefficient)),
      Hp.obj = external P f g K L ∧
        Nonempty (FixedEtaleOriginWitness (pullback f g) P.Coefficient Hp)) := by
  sorry

/-- The specified composition and exchange, for every retained witness and compactification.
The existential isomorphisms retain the actual exchange as their hom and the actual
functor image of its inverse tensor identity as their hom; they do not replace these maps.
Source: relative-product proof (1),(3)
(blueprint: lem-pur-relative-product-geometric-factors).

Proof:
1. By thm-sf-comp-composition, compact support preserves the bounded-below origin class,
and its canonical alpha at H is invertible, with inverse alpha inverse.
2. For a chosen compactification c, properness of its proper part and its base change
gives qcqs. Exact etale open extension preserves a lower bound. Apply
lem-weil-pbc-transport-identifies-exchange to this proper square at j!W.complex.
3. Apply lem-fix-site-open-exchange to its upper open square. Finiteness of A is
supplied by def-weil-l-adic-coefficient-extension. Substitute these two normalized
identities into def-exchange-projection. The middle comparisons cancel, leaving
exactly compactExchangeTransportAtWitness, formed using def-cbc-exchange-map.
4. Apply thm-cbc-finite-level-proetale with c. It makes this transported arrow invertible
and independent of witness and compactification under the specified comparisons.
Naturality conjugates the identity by W.iso and proves all displayed equalities.
5. Tensor the two inverse identities with the identity of L and apply the compact-support
functor for g. Functoriality gives both displayed inverse maps. The inverse of alpha
is already an isomorphism. None of these steps invokes exceptional adjunction or duality. -/
theorem relative_product_composition_exchange (P : PurityFiniteSetting.{u})
    (B X Y : Scheme.{u}) (s : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (f : X ⟶ B) (g : Y ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (L : D P Y) (_hK : ctf P X K.obj) (_hL : ctf P Y L)
    (H : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology (pullback f g)) (ModuleCat.{u + 1} P.Coefficient)))
    (_hH : H.obj = external P f g K.obj L)
    (WK : FixedEtaleOriginWitness X P.Coefficient K)
    (WH : FixedEtaleOriginWitness (pullback f g) P.Coefficient H)
    (c : Compactification f) (cg : Compactification g)
    (cb : Compactification (pullback.snd f g))
    (ch : Compactification (pullback.snd f g ≫ g)) :
    (exchange P (IsPullback.of_hasPullback f g) c).app K.obj =
      ProEtale.compactExchangeTransportAtWitness P.Coefficient
        (IsPullback.of_hasPullback f g) c WK.complex K.obj WK.iso ∧
    IsIso ((exchange P (IsPullback.of_hasPullback f g) c).app K.obj) ∧
    (∀ W' : FixedEtaleOriginWitness X P.Coefficient K,
      ProEtale.compactExchangeTransportAtWitness P.Coefficient
          (IsPullback.of_hasPullback f g) c WK.complex K.obj WK.iso =
        ProEtale.compactExchangeTransportAtWitness P.Coefficient
          (IsPullback.of_hasPullback f g) c W'.complex K.obj W'.iso) ∧
    (∀ d : Compactification f,
      (exchange P (IsPullback.of_hasPullback f g) c).app K.obj ≫
          (targetComparison P c d K WK).hom =
        (sourceComparison P g c d K WK).hom ≫
          (exchange P (IsPullback.of_hasPullback f g) d).app K.obj) ∧
    (∃ e : ((ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c) ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor).obj K.obj ≅
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (pullback.fst f g)).leftDerivedFunctor ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient)
          (c.ofIsPullback (IsPullback.of_hasPullback f g))).obj K.obj,
      e.hom = (exchange P (IsPullback.of_hasPullback f g) c).app K.obj ∧
      ∃ j : (ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} P.Coefficient) cg).obj
          (((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
              (pullback.fst f g)).leftDerivedFunctor ⋙
            ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} P.Coefficient)
              (c.ofIsPullback (IsPullback.of_hasPullback f g))).obj K.obj ⊗ L) ≅
          (ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} P.Coefficient) cg).obj
            (((ProEtale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} P.Coefficient) c) ⋙
              (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
                g).leftDerivedFunctor).obj K.obj ⊗ L),
        j.hom = (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) cg).map (e.inv ⊗ₘ 𝟙 L) ∧
        j.inv = (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) cg).map (e.hom ⊗ₘ 𝟙 L)) ∧
    IsIso ((composition P f g cb cg ch).hom.app
      (origin P (pullback f g) H WH)) ∧
    IsIso ((composition P f g cb cg ch).inv.app
      (origin P (pullback f g) H WH)) := by
  sorry

end WeilConjectures.RelativeProduct
