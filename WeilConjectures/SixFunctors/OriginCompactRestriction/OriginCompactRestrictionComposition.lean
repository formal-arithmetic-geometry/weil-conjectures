/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality

/-!
# Coherent coefficient comparisons for the dual--pullback--dual composite

Source: latest blueprint, `lem-coef-finite-exceptional.proof.md`, second paragraph,
first three sentences (blueprint: lem-sf-origin-compact-restriction-composition).

All categories are the intrinsic finite-Tor constructible full subcategories.
The natural-number index `n` denotes the positive exponent `n + 1`.
Verdier duality is transported from the recorded fixed-scalar presentation by
its canonical realization equivalence. Scalar extension and pullback are the
recorded constant-ring operations. No exceptional adjunction is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.OriginCompactRestriction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded positive finite coefficient quotient.
Source: coefficient convention (blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev A (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- The actual condensed finite-Tor category, at positive exponent n+1.
Source: finite-Tor domain (blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev C (T : Scheme.{u}) (n : ℕ) :=
  CondensedConstructibleFiniteTor (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) T

/-- The section-normalized finite coefficient equivalence already constructed in the library.
Its forward functor is section-action, not an arbitrary realization.
Source: finite coefficient convention
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def encoding (T : Scheme.{u}) (n : ℕ) : ProEtale.FiniteDiscreteOrdinary.Encoding (A l E n) T :=
  (ProEtale.FiniteDiscreteOrdinary.encoding_exists (A l E n) T).some

/-- Canonical section-action equivalence on the ordinary unbounded derived categories.
Source: finite coefficient convention
(blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev ordinary (T : Scheme.{u}) (n : ℕ) := (encoding l E T n).ordinaryDerived

/-- The ambient native condensed module-derived category.
Source: finite coefficient convention
(blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev Ambient (T : Scheme.{u}) (n : ℕ) :=
  DerivedCategory (ProEtale.FiniteDiscreteOrdinary.Internal (A l E n) T)

/-- The native finite-Tor predicate from the recorded dependency.
Source: finite-Tor domain (blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev ctf (T : Scheme.{u}) (n : ℕ) :=
  condensedConstructibleFiniteTor (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) T

/-- The canonical quotient of the valuation ring at two positive exponents.
Source: the quotient maps in the same blueprint paragraph
(blueprint: lem-sf-origin-compact-restriction-composition). -/
abbrev quotient {a b : ℕ} (h : b ≤ a) :
    Padic.coefficientExtensionRing l E (a + 1) →+*
      Padic.coefficientExtensionRing l E (b + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The actual quotient morphism of commutative condensed rings, by postcomposition.
Source: coefficient tensor (blueprint: lem-sf-origin-compact-restriction-composition). -/
def quotientMap {a b : ℕ} (h : b ≤ a) :
    CommMon.mk (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E a)) ⟶
      CommMon.mk (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E b)) :=
  CommMon.homMk (@Mon.Hom.mk _ _ _ _ _
    (Profinite.continuousMapRingObjMapOfUniverse.{u, u} (quotient l E h)
      continuous_of_discreteTopology)
    (Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (quotient l E h) continuous_of_discreteTopology)))

/-- The actual native ordinary derived extension of condensed coefficient scalars.
Source: det-sp-scalar-extension-functor, clauses 1 and 4
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def QAmbient (T : Scheme.{u}) {a b : ℕ} (h : b ≤ a) :
    Ambient l E T a ⥤ Ambient l E T b :=
  scalarSixChange (quotientMap l E h) T

/-- Restriction of actual scalar extension to the recorded full subcategories.
Source: coefficient tensor (blueprint: lem-sf-origin-compact-restriction-composition). -/
def Q (T : Scheme.{u}) {a b : ℕ} (h : b ≤ a) : C l E T a ⥤ C l E T b :=
  (ctf l E T b).lift ((ctf l E T a).ι ⋙ QAmbient l E T h) (scalar_preserves l E T h)

/-- Tensor unitor transported through the canonical section-action equivalence.
Source: det-sp-scalar-extension-functor, clause 4
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def QUnitAmbient (T : Scheme.{u}) (n : ℕ) : QAmbient l E T (le_refl n) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun m ↦ scalarSixChange m T) (quotientMap_id l E n)) ≪≫
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (ProEtale.coefficientMap (Λ := ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n))
        (Λ' := ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n))
        (𝟙 _) T)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight
        (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (ProEtale.coefficientMap_id
            (Λ := ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) T)) ≪≫
          Functor.mapDerivedCategoryNatIso
            (Mod.comapId (ProEtale.condensedRingObj
              (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) T)) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm)

/-- The restricted standard identity-level tensor unitor.
Source: identity levels (blueprint: lem-sf-origin-compact-restriction-composition). -/
def QUnit (T : Scheme.{u}) (n : ℕ) (K : C l E T n) :
    (Q l E T (le_refl n)).obj K ≅ K :=
  ObjectProperty.isoMk _ ((QUnitAmbient l E T n).app K.obj)

/-- The standard tensor associator with the middle coefficient encoding cancelled.
Source: det-sp-scalar-extension-functor, clause 4
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def QCompAmbient (T : Scheme.{u}) {a b c : ℕ} (h : b ≤ a) (g : c ≤ b) :
    QAmbient l E T h ⋙ QAmbient l E T g ≅ QAmbient l E T (g.trans h) :=
  scalarSixTower (quotientMap l E h) (quotientMap l E g) T ≪≫
    eqToIso (congrArg (fun m ↦ scalarSixChange m T) (quotientMap_comp l E h g))

/-- The standard scalar tensor associator restricted to the native full categories.
Source: tensor associativity (blueprint: lem-sf-origin-compact-restriction-composition). -/
def QComp (T : Scheme.{u}) {a b c : ℕ} (h : b ≤ a) (g : c ≤ b)
    (K : C l E T a) :
    (Q l E T g).obj ((Q l E T h).obj K) ≅ (Q l E T (g.trans h)).obj K :=
  ObjectProperty.isoMk _ ((QCompAmbient l E T h g).app K.obj)

variable (T : Over (Spec (CommRingCat.of D.k)))
  [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]

/-- The specified Verdier functor, in intrinsic constant-ring coordinates.
The fixed-scalar dualizing object is exactly `Ra_T^! A`, as in the recorded
biduality theorem, and the coefficient realization is the published one.
Source: `thm-fix-general-biduality`, used in the source paragraph
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def dualAmbient (n : ℕ) : (Ambient l E T.left n)ᵒᵖ ⥤ Ambient l E T.left n :=
  (derivedHom (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) T.left).flip.obj
    ((encoding l E T.left n).fixedDerived.inverse.obj
      ((ProEtale.sfFiniteExceptionalFixed (A l E n)
        (NagataCompactification T.hom)).obj (𝟙_ _)))

/-- Restriction of the specified contravariant dual to its full domain.
Source: the duals D in the source paragraph
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def dual (hl : l ≠ D.p) (n : ℕ) : (C l E T.left n)ᵒᵖ ⥤ C l E T.left n :=
  (ctf l E T.left n).lift
    ((ctf l E T.left n).ι.op ⋙
      dualAmbient D l E T n)
    (fun K ↦ dual_preserves D l E T hl n K.unop)

variable {T}
variable (X Y : Over (Spec (CommRingCat.of D.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]

/-- Actual ordinary pullback in native condensed coordinates, using the
section-normalized equivalence and the recorded finite derived pullback.
Source: lem-sf-pullback-tor-amplitude
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def pullAmbient (n : ℕ) : Ambient l E Y.left n ⥤ Ambient l E X.left n :=
  (upperStar (ProEtale.FiniteDiscreteOrdinary.coefficient (A l E n)) f.left).mapDerivedCategory

/-- The actual pullback, restricted to the recorded full subcategories.
Source: lem-sf-pullback-tor-amplitude
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def pull (hl : l ≠ D.p) (n : ℕ) : C l E Y.left n ⥤ C l E X.left n :=
  (ctf l E X.left n).lift ((ctf l E Y.left n).ι ⋙ pullAmbient D l E X Y f n)
    (pull_preserves D l E X Y f hl n)


variable (hl : l ≠ D.p)

variable (T)

/-- Identity and quotient-cocycle hypotheses for a supplied duality comparison.
The unit and associator of coefficient tensor are displayed explicitly.
Source: coherent duality comparisons in the source paragraph
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def DualCoherent
    (d : ∀ {a b : ℕ} (h : b ≤ a),
      dual D l E T hl a ⋙ Q l E T.left h ≅
        (Q l E T.left h).op ⋙ dual D l E T hl b) : Prop :=
  (∀ (n : ℕ) (M : C l E T.left n),
    (d (le_refl n)).hom.app (op M) =
      (QUnit l E T.left n ((dual D l E T hl n).obj (op M))).hom ≫
        (dual D l E T hl n).map ((QUnit l E T.left n M).hom).op) ∧
  (∀ {a b c : ℕ} (h : b ≤ a) (g : c ≤ b) (M : C l E T.left a),
    (Q l E T.left g).map ((d h).hom.app (op M)) ≫
        (d g).hom.app (op ((Q l E T.left h).obj M)) ≫
        (dual D l E T hl c).map ((QComp l E T.left h g M).inv).op =
      (QComp l E T.left h g ((dual D l E T hl a).obj (op M))).hom ≫
        (d (g.trans h)).hom.app (op M))

/-- Identity and quotient-cocycle hypotheses for the supplied pullback comparison.
Source: tensor commutes with ordinary pullback in the source paragraph
(blueprint: lem-sf-origin-compact-restriction-composition). -/
def PullCoherent
    (p : ∀ {a b : ℕ} (h : b ≤ a),
      pull D l E X Y f hl a ⋙ Q l E X.left h ≅
        Q l E Y.left h ⋙ pull D l E X Y f hl b) : Prop :=
  (∀ (n : ℕ) (M : C l E Y.left n),
    (p (le_refl n)).hom.app M =
      (QUnit l E X.left n ((pull D l E X Y f hl n).obj M)).hom ≫
        (pull D l E X Y f hl n).map ((QUnit l E Y.left n M).inv)) ∧
  (∀ {a b c : ℕ} (h : b ≤ a) (g : c ≤ b) (M : C l E Y.left a),
    (Q l E X.left g).map ((p h).hom.app M) ≫
        (p g).hom.app ((Q l E Y.left h).obj M) ≫
        (pull D l E X Y f hl c).map ((QComp l E Y.left h g M).hom) =
      (QComp l E X.left h g ((pull D l E X Y f hl a).obj M)).hom ≫
        (p (g.trans h)).hom.app M)

variable
  (dY : ∀ {a b : ℕ} (h : b ≤ a),
    dual D l E Y hl a ⋙ Q l E Y.left h ≅
      (Q l E Y.left h).op ⋙ dual D l E Y hl b)
  (dX : ∀ {a b : ℕ} (h : b ≤ a),
    dual D l E X hl a ⋙ Q l E X.left h ≅
      (Q l E X.left h).op ⋙ dual D l E X hl b)
  (p : ∀ {a b : ℕ} (h : b ≤ a),
    pull D l E X Y f hl a ⋙ Q l E X.left h ≅
      Q l E Y.left h ⋙ pull D l E X Y f hl b)

end WeilConjectures.OriginCompactRestriction
