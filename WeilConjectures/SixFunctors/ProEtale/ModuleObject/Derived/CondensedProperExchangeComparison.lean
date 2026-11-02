/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IdentityOpenExchangeNormalization

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

/-- The two exchange and naturality equations for an arbitrary proper self-square.
Its two proof fields are precisely the original displayed formulas before specialization.
Source: the identity compactification and naturality paragraphs of
`prop-weil-proper-compact-coincidence.proof.md`
(blueprint: lem-a1-condensed-proper-exchange-comparison). -/
structure ProperIdentityExchangeComparison {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h) : Prop where
  exchange : ∀ K : BoundedConstructible (condensedRingObj Λ X),
      (CompactificationReindexing.squareExchange Λ
        (properIdentityCompactificationSquare sq)).app K.obj ≫
          (properIdentityComparison Λ a).hom.app
            ((upperStar Λ g).leftDerivedFunctor.obj K.obj) =
        (upperStar Λ h).leftDerivedFunctor.map
            ((properIdentityComparison Λ a).hom.app K.obj) ≫
          (baseChangeMap Λ sq).app K.obj
  naturality : ∀ (K L : BoundedConstructible (condensedRingObj Λ X)) (u : K ⟶ L),
      (properIdentityComparison Λ a).hom.app K.obj ≫
          (lowerStar Λ a).rightDerivedFunctor.map u.hom =
        (rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsProper a)).map u.hom ≫
          (properIdentityComparison Λ a).hom.app L.obj

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
  ProperIdentityExchangeComparison Λ sq

private theorem identity_compactification_exchange
    {C E C' E' : Type*} [Category C] [Category E] [Category C'] [Category E']
    (J : C ⥤ C) (J' : C' ⥤ C')
    (P : E ⥤ C) (R : C ⥤ E) (a : P ⊣ R)
    (P' : E' ⥤ C') (R' : C' ⥤ E') (a' : P' ⊣ R')
    (G : E ⥤ E') (H : C ⥤ C') (θ : G ⋙ P' ≅ P ⋙ H)
    (b : J ⋙ H ≅ H ⋙ J') (i : J ≅ 𝟭 C) (i' : J' ≅ 𝟭 C')
    (χ : (J ⋙ R) ⋙ G ⟶ H ⋙ (J' ⋙ R'))
    (hχ : χ = SuppliedExchangeProjection.compactificationExchangeFromData
      J J' P R a P' R' a' G H H θ b)
    (e : R ⋙ G ⟶ H ⋙ R') (he : e = a.exchangeRight a' θ)
    (hb : ∀ K, b.hom.app K ≫ i'.hom.app (H.obj K) = H.map (i.hom.app K)) (K : C) :
    χ.app K ≫ R'.map (i'.hom.app (H.obj K)) =
      G.map (R.map (i.hom.app K)) ≫ e.app K := by
  rw [hχ, he]
  unfold SuppliedExchangeProjection.compactificationExchangeFromData
  simp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← R'.map_comp, hb, ← Adjunction.exchangeRight_eq_mateEquiv]
  exact ((a.exchangeRight a' θ).naturality (i.hom.app K)).symm

private theorem properIdentityComparison_hom_app {X S : Scheme.{u}} (a : X ⟶ S)
    [IsProper a] (K : CompactificationReindexing.D Λ X) :
    (properIdentityComparison Λ a).hom.app K =
      (lowerStar Λ a).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekId Λ X).hom.app K) := by
  exact Category.comp_id _

private theorem proper_identity_exchange {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h)
    (K : CompactificationReindexing.D Λ X) :
    (CompactificationReindexing.squareExchange Λ
      (properIdentityCompactificationSquare sq)).app K ≫
        (properIdentityComparison Λ a).hom.app
          ((upperStar Λ g).leftDerivedFunctor.obj K) =
      (upperStar Λ h).leftDerivedFunctor.map
          ((properIdentityComparison Λ a).hom.app K) ≫
        (baseChangeMap Λ sq).app K := by
  rw [properIdentityComparison_hom_app, properIdentityComparison_hom_app]
  exact identity_compactification_exchange
    (CompactificationReindexing.J Λ (𝟙 X)) (CompactificationReindexing.J Λ (𝟙 X))
    (CompactificationReindexing.P Λ a) (CompactificationReindexing.R Λ a)
    (derivedUpperStarLowerStarAdjunction Λ a)
    (CompactificationReindexing.P Λ a) (CompactificationReindexing.R Λ a)
    (derivedUpperStarLowerStarAdjunction Λ a)
    (CompactificationReindexing.P Λ h) (CompactificationReindexing.P Λ g)
    (pullbackSquareComparison Λ sq) (CompactificationReindexing.beta Λ (IsPullback.id_vert g))
    (derivedOpenImmersionLowerShriekId Λ X) (derivedOpenImmersionLowerShriekId Λ X)
    (CompactificationReindexing.squareExchange Λ (properIdentityCompactificationSquare sq))
    (by unfold CompactificationReindexing.squareExchange; rfl)
    (baseChangeMap Λ sq) rfl ((identityOpenExchangeNormalization Λ).2.1 g) K

private theorem proper_identity_comparison {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h) :
    ProperIdentityExchangeComparison Λ sq := by
  constructor
  · intro K
    exact proper_identity_exchange Λ sq K.obj
  · intro K L u
    exact ((properIdentityComparison Λ a).hom.naturality u.hom).symm

/-- The proof structure is equivalent to the original conjunction, with exactly the
same quantifiers, coefficient objects, and canonical arrows.
Source: the two displayed equations of this node
(blueprint: lem-a1-condensed-proper-exchange-comparison). -/
theorem properIdentityExchangeComparison_iff {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h) :
    ProperIdentityExchangeComparison Λ sq ↔
    (∀ K : BoundedConstructible (condensedRingObj Λ X),
      (CompactificationReindexing.squareExchange Λ
        (properIdentityCompactificationSquare sq)).app K.obj ≫
          (properIdentityComparison Λ a).hom.app
            ((upperStar Λ g).leftDerivedFunctor.obj K.obj) =
        (upperStar Λ h).leftDerivedFunctor.map
            ((properIdentityComparison Λ a).hom.app K.obj) ≫
          (baseChangeMap Λ sq).app K.obj) ∧
    (∀ (K L : BoundedConstructible (condensedRingObj Λ X)) (u : K ⟶ L),
      (properIdentityComparison Λ a).hom.app K.obj ≫
          (lowerStar Λ a).rightDerivedFunctor.map u.hom =
        (rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsProper a)).map u.hom ≫
          (properIdentityComparison Λ a).hom.app L.obj) := by
  constructor
  · intro h
    exact ⟨h.exchange, h.naturality⟩
  · intro h
    exact ⟨h.1, h.2⟩

private theorem geometricFiber_isProper
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom] :
    IsProper (D.geometricFiber Y₀).hom :=
  MorphismProperty.pullback_snd _ _ inferInstance

private theorem proper_exchange_comparison_for_coefficients
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom] :
    ProperExchangeComparison Λ D Y₀ := by
  let := geometricFiber_isProper D Y₀
  unfold ProperExchangeComparison
  intro sq
  exact proper_identity_comparison Λ sq

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
  exact ⟨proper_exchange_comparison_for_coefficients _ D Y₀,
    proper_exchange_comparison_for_coefficients _ D Y₀⟩

end AlgebraicGeometry.ProEtale.CondensedRing
