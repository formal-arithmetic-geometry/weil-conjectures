/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.ProperCompactCoincidence
public import WeilConjectures.SixFunctors.FrobeniusPointTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

public import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
import WeilConjectures.AlgebraicGeometry.CondensedIsomorphismSquareExchange
import WeilConjectures.SecSmoothPurity.CondensedOpenBaseChangeArbitrary
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Proper condensed exchange and Frobenius

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md, opening evaluation sentence;
the proper compact-to-ordinary normalization of
`prop-weil-proper-compact-coincidence` (blueprint: lem-a1-condensed-proper-exchange-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The proper comparison attached to the identity compactification.
Source: the identity compactification paragraph of
`prop-weil-proper-compact-coincidence.proof.md`
(blueprint: lem-a1-condensed-proper-exchange-comparison).
This is the canonical identity-open comparison followed by the
proper direct image, with the displayed left-unitor normalization. -/
noncomputable def properIdentityComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper f) ≅
      (lowerStar Λ f).rightDerivedFunctor :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X)
      (lowerStar Λ f).rightDerivedFunctor ≪≫ Functor.leftUnitor _

/-- Identity compactifications on both sides of the specified scheme square.
Source: proper identity compactification in the node's proof, step 1
(blueprint: lem-a1-condensed-proper-exchange-comparison). -/
def properIdentityCompactificationSquare {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h) :
    CompactificationReindexing.Square
      (Compactification.ofIsProper a) (Compactification.ofIsProper a) g h where
  middle := g
  openSquare := IsPullback.id_vert g
  properSquare := sq

/-- The two displayed arrow equalities, in their actual ambient module categories.
Source: the displayed exchange and naturality formulas of the node
(blueprint: lem-a1-condensed-proper-exchange-comparison).
This predicate only abbreviates those formulas, with no chosen maps or extra data. -/
def ProperExchangeComparison (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom] : Prop :=
  letI : MonObj (condensedRingObj Λ (D.geometricFiber Y₀).left) :=
    Functor.monObjObj (F := upperStarFromPoint (D.geometricFiber Y₀).left) Λ
  letI : IsProper (D.geometricFiber Y₀).hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let sq : CommSq (D.geometricFrobenius Y₀).hom (D.geometricFiber Y₀).hom
      (D.geometricFiber Y₀).hom (WeilConjectures.frobeniusPointIso D).hom := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    exact ⟨(D.galoisMap_projections Y₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2⟩
  (∀ K : BoundedConstructible (condensedRingObj Λ (D.geometricFiber Y₀).left),
    (CompactificationReindexing.squareExchange Λ
      (properIdentityCompactificationSquare sq)).app K.obj ≫
        (properIdentityComparison Λ (D.geometricFiber Y₀).hom).hom.app
          ((upperStar Λ (D.geometricFrobenius Y₀).hom).leftDerivedFunctor.obj K.obj) =
      (upperStar Λ (WeilConjectures.frobeniusPointIso D).hom).leftDerivedFunctor.map
          ((properIdentityComparison Λ (D.geometricFiber Y₀).hom).hom.app K.obj) ≫
        (baseChangeMap Λ sq).app K.obj) ∧
  (∀ (K L : BoundedConstructible (condensedRingObj Λ (D.geometricFiber Y₀).left))
      (u : K ⟶ L),
    (properIdentityComparison Λ (D.geometricFiber Y₀).hom).hom.app K.obj ≫
        (lowerStar Λ (D.geometricFiber Y₀).hom).rightDerivedFunctor.map u.hom =
      (rightDerivedLowerShriekOfCompactification Λ
        (Compactification.ofIsProper (D.geometricFiber Y₀).hom)).map u.hom ≫
        (properIdentityComparison Λ (D.geometricFiber Y₀).hom).hom.app L.obj)

/-- The proper comparison intertwines the specified Frobenius exchanges and is natural,
for both the actual condensed finite extension and the finite-subextension-valued closure.
Source: latest blueprint, `lem-a1-finite-boundary-weights.proof.md`, opening evaluation
sentence, and `prop-weil-proper-compact-coincidence.proof.md`, identity compactification
(blueprint: lem-a1-condensed-proper-exchange-comparison).

Proof: (1) For the identity compactification write J = D(id_!), F = Ra_* and η : J ≅ Id.
The canonical κ is Fη. The compact exchange is the proper mate e at JK followed by Fβ.
This is the semilinear recipe of lem-pod-condensed-automorphism-compact-exchange and
of def-exchange-projection; the separately derived composite is prescribed by
 det-def-sfb-module-derived-lower-shriek.
(2) The identity-open adjoint comparison def-sfb-derived-open-lower-shriek-id normalizes
its unit and counit. The inverse-mate formula of def-weil-pbc-adjunction-mate, together
with lem-sp-condensed-open-base-change-arbitrary and
lem-sf-condensed-isomorphism-square-exchange, gives η at QK composed with β = Qη.
(3) Naturality of e at η gives FQη composed with e at JK = e at K composed with PFη.
Substitute (2) to obtain the first equality before evaluation or cohomology.
(4) Naturality of η at u, followed by F, gives the second equality. All equations live
in the actual ambient derived categories, hence restrict to bounded constructible inputs.
Use the same construction separately for E and the finite-subextension-valued closure. -/
theorem proper_exchange_comparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField l)
    (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom] :
    ProperExchangeComparison (Profinite.continuousMapRingObj.{u} E) D Y₀ ∧
      ProperExchangeComparison (Profinite.padicAlgClRingObj.{u} l) D Y₀ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
