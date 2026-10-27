/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.KummerSiteCohomologyNormalization
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.DiscreteExchangeSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.SiteCohomologyPullback
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange

/-! # Relative scalar Kummer classes and the normalized site comparison

Source: latest blueprint sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md,
opening paragraph and Step 3; Stacks Tags 03FD, 099W, 09A6 and 072W
(blueprint: lem-pur-relative-kummer-site-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The specified comparison on higher direct images: exact comparison followed by
cohomology of the canonical counit mate. Source: Stacks 099W and 09A6
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteHigherMap (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (a : X ⟶ B)
    (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : ℤ) :=
  (Functor.mapDerivedCategoryPlusHomologyFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) B) q).hom.app
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) a).obj F) ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map
      ((fixedComparisonDirectImageMatePlus A a).app F)

/-- Pullback of the pro-etale root line through the specified inverse-image square
and scalar extension on roots. Source: Stacks 099R and the relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProCoefficient (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :=
  (sheafComposeForget₂CompUpperStarIso A f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T m A hA)) ≫
    (sheafForget₂ A X).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
          (Scheme.finiteEtaleTateLine T m A hA) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hT hX 1).hom)

/-- Canonical pro-etale abelian cohomology pullback with the specified root-line
coefficient identification. Source: Stacks 099R and 08J6
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (q : ℕ)
    (x : Sheaf.H ((sheafForget₂ A T).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T m A hA))) q) :=
  Sheaf.H.map (kummerSiteProCoefficient A m hm hA f hT hX) q
    (Sheaf.H.mapFunctor (upperStar AddCommGrpCat.{u + 1} f)
      ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) _ q x)

/-- The integral generator on the comparison pullback of the constant module sheaf.
Source: Stacks 03FD and 099W (blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (comparisonConstantSheafIso T).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
      (Etale.ordinaryFiniteIntegralGenerator A T) ≫
    (sheafComposeForget₂CompComparisonUpperStarIso A T).hom.app
      (Etale.ordinaryFiniteConstant A T)

/-- Realize a pro-etale module Ext class in underlying abelian cohomology, with the
specified integral generator. Source: Stacks 03FD
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProExtClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (x : Abelian.Ext
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Etale.ordinaryFiniteConstant A T)) F 1) :
    Sheaf.H ((sheafForget₂ A T).obj F) 1 :=
  (Abelian.Ext.mk₀ (kummerSiteProIntegralGenerator A T)).comp
    (x.mapExactFunctor (sheafForget₂ A T)) (zero_add 1)

/-- All clauses of the relative Kummer site normalization, using the actual comparison
unit, counit mate, edges and exchanges. No finite-type restriction is put on a test
scheme or on a horizontal morphism. Source: relative Kummer proof, opening and Step 3
(blueprint: lem-pur-relative-kummer-site-normalization). -/
def RelativeKummerSiteNormalization (k : Type u) [Field k]
    (m : ℕ) (hm : 0 < m) (A : Type (u + 1)) [CommRing A]
    (hA : (m : A) = 0) : Prop :=
  (∀ (T : Scheme.{u}) (_t : T ⟶ Spec (.of k))
      (q : ℕ)
      (x : kummerSiteEtaleH T A (Scheme.finiteEtaleTateLine T m A hA) q),
    kummerSiteScalarMap (Scheme.ProEt.topology T) A (Scheme.ProEt.mk (𝟙 T))
        (Scheme.ProEt.isTerminalMkId T) _ q
        (kummerSiteComparison T A (Scheme.finiteEtaleTateLine T m A hA) q x) =
      Sheaf.H.map
        ((sheafComposeForget₂CompComparisonUpperStarIso A T).hom.app
          (Scheme.finiteEtaleTateLine T m A hA)) q
        (comparisonCohomologyMap T _ q
          (kummerSiteScalarMap T.smallEtaleTopology A (Scheme.Etale.mk (𝟙 T))
            (Scheme.Etale.isTerminalMkId T) (Scheme.finiteEtaleTateLine T m A hA) q x))) ∧
  (∀ (T : Scheme.{u}) (_t : T ⟶ Spec (.of k))
      (hr : IsUnit (m : Γ(T, ⊤))) (w : Γ(T, ⊤)ˣ),
    kummerSiteComparison T A (Scheme.finiteEtaleTateLine T m A hA) 1
        (kummerSiteEtaleClass T A m hA hr w) = kummerSiteProEtaleClass T A m hA hr w) ∧
  (∀ {X B : Scheme.{u}} (a : X ⟶ B) (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a]
      (M : DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))),
    (comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app M) ≫
      (fixedComparisonDirectImageMatePlus A a).app
        ((Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.obj M) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus A a).inv.app M)) ∧
  (∀ {X B : Scheme.{u}} (a : X ⟶ B) (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a]
      (hr : IsUnit (m : Γ(X, ⊤))) (w : Γ(X, ⊤)ˣ),
    siteComparisonProEtaleEdge A a (Scheme.finiteEtaleTateLine X m A hA) 1
        (siteComparisonCohomologyMap X A (Scheme.finiteEtaleTateLine X m A hA) 1
          (kummerSiteEtaleClass X A m hA hr w)) =
      siteComparisonHigherImageSectionMap A a (Scheme.finiteEtaleTateLine X m A hA) 1
        (siteComparisonEtaleEdge A a (Scheme.finiteEtaleTateLine X m A hA) 1
          (kummerSiteEtaleClass X A m hA hr w))) ∧
  (∀ {X B : Scheme.{u}} (a : X ⟶ B) (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a]
      (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (q : ℤ),
    IsIso (kummerSiteHigherMap A a F q) ∧
    (IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) a).obj F)) →
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj F)))) ∧
    (∀ (D : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
        (s : D ⟶ (DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) a).obj F)),
      IsIso s → IsIso ((comparisonUpperStar (ModuleCat.{u + 1} A) B).map s ≫
        kummerSiteHigherMap A a F q))) ∧
  (∀ {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
      {a : X ⟶ B} {g : B' ⟶ B} (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a] [QuasiCompact a'] [QuasiSeparated a']
      (sq : ChosenCartesianSquare v a' a g)
      (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    ((comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app F)) ≫
      (baseChangeTargetComparisonIso v a' A).hom.app F =
        (baseChangeSourceComparisonIso a g A).hom.app F ≫
          (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj F))) ∧
    (IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app F) →
      IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj F))))) ∧
  (∀ {T' T : Scheme.{u}} (f : T' ⟶ T) (_t : T ⟶ Spec (.of k))
      (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) (w : Γ(T, ⊤)ˣ),
    kummerSiteProPullback A m hm hA f hT hT' 1
        (kummerSiteProAbelianClass T A m hA hT w) =
      kummerSiteProAbelianClass T' A m hA hT' (Units.map f.appTop.hom w))

/-- The module comparison is the abelian pullback, including the actual scalar Kummer
class, normalized units and edge generators, vanishings and the specified exchange.
All schemes and horizontal maps are arbitrary over k; this includes Spec Omega for
extensions of infinite transcendence degree. Source: latest blueprint relative Kummer
proof, opening paragraph and Step 3; Stacks 03FD, 099W, 09A6, 072W and 0B65
(blueprint: lem-pur-relative-kummer-site-normalization).

Proof:
1. Apply lem-pe-left-module-derived-evaluation-forget at the two terminal objects.
The normalized module lift of lem-pe-constant-left-module-inverse-image has the same
forgotten unit. The recorded global comparison is exactly this derived unit evaluated
at the final object. Hence its scalar-forgetting square commutes in every degree.
The constant-integers adjunction and evaluation at 1 give the stated scalar maps.
2. The ordinary Kummer sequence is exact on every k-scheme by lem-amb-kummer-any-base.
Pullback of local units commutes with powers, hence with the kernel inclusion of roots
and the coefficient map z to 1 tensor z. A primitive root trivializes roots on arbitrary,
even nonreduced, k-schemes. Naturality of the connecting maps follows from
lem-weil-pbc-site-cohomology-pullback, lem-weil-pbc-right-derived-universal-delta-functor,
lem-weil-pbc-pullback-cohomology-long-exact-ladder and
lem-sc-p1-right-derived-triangle-connecting. It gives etale Kummer naturality.
3. Substitute the actual Kummer class into step 1. Its pro-etale definition is abelian
comparison pullback, so the module class equality follows by the scalar bijection.
The composition/coefficient laws of lem-weil-pbc-site-cohomology-pullback and the
coherent comparison square of lem-weil-pbc-comparison-pullback give pro-etale naturality.
4. The direct-image comparison is the right mate of the inverse pullback comparison
by lem-weil-pbc-comparison-direct-image-canonical-mate. Apply
lem-pur-mate-unit-compatibility (Mathlib unit_mateEquiv). This gives exactly the unit
equation, with the inverse comparison on the right, for every bounded-below M.
5. Apply lem-pur-site-comparison-edge-section with q=1 and the actual module Kummer
class. Exactness from lem-sf-comparison-pullback-exact gives the displayed higher-image
comparison. Functors preserve zero objects and inverse pairs. Thus the normalized unit
and generator maps retain invertibility; A-linearity identifies generators by their
image of 1. The unit and edge equations identify the transported maps with the named maps.
6. Apply lem-weil-pbc-discrete-exchange-site-comparison to the cartesian square.
Its source/target isomorphisms are exactly S and T. Both etale and ambient pro-etale
exchange are the specified adjunction mates (sbc-def-base-change-map,
def-kun-unbounded-exchange, sk-def-exchange, def-weil-pbc-ambient-ringed-exchange).
Thus T C(Ex_e)=Ex_p S. Conjugating by S,T carries invertibility. No hypothesis of
finite type on g or v is used, so geometric points of arbitrary residue extension apply. -/
theorem relativeKummerSiteNormalization (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Finite (ZMod (ℓ ^ N)) A] [Module.Free (ZMod (ℓ ^ N)) A] :
    RelativeKummerSiteNormalization k (ℓ ^ N) (pow_pos hℓ.pos N) A
      (Etale.relativeKummerAnnihilator A (ℓ ^ N)) := by
  sorry

/-- In the purity datum the scalar-normalized pro-etale class is the datum's actual
coordinate class, after its specified root-line identification.
Source: def-pur-affine-line-datum, last paragraph; relative Kummer proof, opening paragraph
(blueprint: lem-pur-relative-kummer-site-normalization).
Proof: unfold coordinateKummer and kummer in the datum. Its etale class is the inverse
of moduleClassToAbelian applied to the same ordinary boundary and pure-tensor map.
The rootCoefficientMap is the same ordinaryFiniteRootMap by its sectionwise uniqueness.
Exact comparison and the integral-generator comparison give the pro-etale equality. -/
theorem relativeKummerSiteNormalization_coordinate
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) :
    kummerSiteProExtClass P.Coefficient (WeilConjectures.PurityFiniteSetting.Punctured Y)
        (P.twist h (WeilConjectures.PurityFiniteSetting.Punctured Y))
        (P.coordinateKummer h Y aY) =
      kummerSiteProAbelianClass (WeilConjectures.PurityFiniteSetting.Punctured Y)
        P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h)
        (P.exponent_isUnit _
          (WeilConjectures.PurityFiniteSetting.puncturedProjection Y ≫ aY))
        (WeilConjectures.PurityFiniteSetting.coordinateUnit Y) := by
  sorry

end AlgebraicGeometry.ProEtale
