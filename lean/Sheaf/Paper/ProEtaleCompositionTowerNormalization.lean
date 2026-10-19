/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.Paper.ProperOpenCoefficientMate
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Normalization on a compatible pro-etale compactification tower

Source: main-20261015, thm-sf-comp-composition, Construction; Stacks Tags 0F7B and 0F7J
(blueprint: lem-trf-proetale-composition-tower-normalization).

The two sides below are independently constructed: the canonical origin compositor,
conjugated to the supplied candidates by canonical comparisons, and the open adjunct of
inverse ordinary exchange followed by the direct-image and open-extension compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Ordinary derived direct image P on the small pro-etale site.
Source: Construction, notation P (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerP {X Y : Scheme.{u}} (t : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} Λ) t).rightDerivedFunctor

/-- Exact derived extension by zero J on the small pro-etale site.
Source: Construction, notation J (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerJ {X Y : Scheme.{u}} (v : X ⟶ Y) [IsOpenImmersion v] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact derived restriction along a scheme map.
Source: Construction, i_p^* (blueprint: lem-trf-proetale-composition-tower-normalization). -/
abbrev towerPull {X Y : Scheme.{u}} (v : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} Λ) v).mapDerivedCategory

/-- Exact inverse image is left adjoint to total direct image.
Source: Construction, ambient exchange adjunctions
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerPullPushAdjunction {X Y : Scheme.{u}} (v : X ⟶ Y) :
    towerPull Λ v ⊣ towerP Λ v :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).ofNatIsoLeft
    (Functor.leftDerivedFunctorIsoMapDerivedCategory _)

/-- Canonical pullback comparison of the commutative square, descended termwise.
Source: Construction, unit--square--counit exchange
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerPullSquare {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i) :
    towerPull Λ i ⋙ towerPull Λ r ≅ towerPull Λ p ⋙ towerPull Λ b :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) r i).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) w.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) b p) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The actual ambient exchange Ex^p: unit for r, square, counit for p.
Source: Construction, exchange normalization
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerExchange {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) (w : b ≫ p = r ≫ i)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj K) ⟶
      (towerP Λ r).obj ((towerPull Λ b).obj K) :=
  (towerPullPushAdjunction Λ r).unit.app _ ≫
    (towerP Λ r).map ((towerPullSquare Λ b i r p w).hom.app _ ≫
      (towerPull Λ b).map ((towerPullPushAdjunction Λ p).counit.app K))

/-- The open unit eta_b, induced from the actual sheaf adjunction unit.
Source: Construction, inverse open unit
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenUnit {X Y : Scheme.{u}} (b : X ⟶ Y) [IsOpenImmersion b] :
    𝟭 _ ≅ towerJ Λ b ⋙ towerPull Λ b :=
  (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b).unit) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Lambda is Ex^p on J_b N followed by P_r of inverse eta_b.
Source: Construction, displayed lambda
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerLambda {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ))) :
    (towerPull Λ i).obj ((towerP Λ p).obj ((towerJ Λ b).obj N)) ⟶
      (towerP Λ r).obj N :=
  towerExchange Λ b i r p w ((towerJ Λ b).obj N) ≫
    (towerP Λ r).map ((towerOpenUnit Λ b).inv.app N)

/-- Gamma is defined by the Hom bijection from inverse lambda, not by site transport.
The IsIso argument is proof data furnished in the theorem, not an extra hypothesis there.
Source: Construction, displayed open-adjoint prescription
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerGamma {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S)
    (r : H ⟶ V) (p : T ⟶ S) [IsOpenImmersion b] [IsOpenImmersion i]
    (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology H) (ModuleCat.{u + 1} Λ)))
    (hLambda : IsIso (towerLambda Λ b i r p w N)) :
    (towerJ Λ i).obj ((towerP Λ r).obj N) ⟶
      (towerP Λ p).obj ((towerJ Λ b).obj N) :=
  letI := hLambda
  (((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction).homEquiv _ _).symm
      (inv (towerLambda Λ b i r p w N))

/-- E is the unique open-extension compositor conjugate to composite restriction.
Source: Construction, final open compositor
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenComposition {U H T : Scheme.{u}} (j : U ⟶ H) (b : H ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    towerJ Λ j ⋙ towerJ Λ b ≅ towerJ Λ (j ≫ b) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)).leftAdjointUniq
          ((openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) (j ≫ b)).ofNatIsoRight
              (upperStarComp (ModuleCat.{u + 1} Λ) j b)))

/-- Canonical change of candidate on the full etale-origin class. Transport the
canonical etale common-refinement comparison through the named site comparisons,
then descend it uniquely along the etale-origin equivalence. This is not a choice
of an arbitrary isomorphism.
Source: Construction, independence under compactification comparisons
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerCandidateComparison [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X
  let model := compactSupportSiteComparison Λ c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c d)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ≪≫
    (compactSupportSiteComparison Λ d).symm
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model

/-- Alpha^p on the supplied candidates. Conjugate the published canonical origin
composition by the canonical comparisons from e.restrict and d to the chosen models,
and from the chosen composite to d.comp e. Existence of compactifications is a Prop
and cannot select models: the explicit comparison factors here retain the candidates.
This construction does not refer to exchange, lambda or gamma.
Source: thm-sf-comp-composition, Construction and independence
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOriginComposition [Finite Λ] {U V W : Scheme.{u}}
    (h : U ⟶ V) (f : V ⟶ W) [QuasiCompact h] [QuasiCompact f]
    (d : Compactification f) (e : Compactification (h ≫ d.i))
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        e.restrict).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj)) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
      (d.comp e)).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj) :=
  letI : HasCompactification h := e.restrict.hasCompactification
  letI : HasCompactification f := d.hasCompactification
  letI : HasCompactification (h ≫ f) := (d.comp e).hasCompactification
  let O := (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) U).obj L
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).map
      ((towerCandidateComparison Λ e.restrict
        (HasCompactification.compactification h)).hom.app O) ≫
    (towerCandidateComparison Λ d (HasCompactification.compactification f)).hom.app
      ((originCompactSupport Λ h).obj O) ≫
    (originCompositionAmbient Λ h f).hom.app O ≫
    (towerCandidateComparison Λ (HasCompactification.compactification (h ≫ f))
      (d.comp e)).hom.app O

/-- Equality transport for open extension, used with bj=a.
Source: Construction, compatible triangle
(blueprint: lem-trf-proetale-composition-tower-normalization). -/
def towerOpenCongr {X Y : Scheme.{u}} {v v' : X ⟶ Y}
    [IsOpenImmersion v] [IsOpenImmersion v'] (w : v = v') :
    towerJ Λ v ≅ towerJ Λ v' := by
  subst v'
  exact Iso.refl _

/-- The specified pro-etale composition is the open-adjoint tower formula, and its
proper/open arrow is invertible on the displayed bounded-below etale-origin input.
Source: main-20261015, thm-sf-comp-composition, Construction; Stacks 0F7B and 0F7J
(blueprint: lem-trf-proetale-composition-tower-normalization).

Proof (the eight steps of the node):
1. The compatible triangle gives bj=a, rj=h and the Cartesian square pb=ir.
Properness of p and q and finite type over the field give Noetherian schemes and qcqs
proper arrows, by the finite-type-over-Noetherian and qcqs-permanence lemmas. The
coefficient-extension finiteness theorem gives finite Lambda.
2. Exact comparison and exact open extension descend the open comparison termwise.
For M=nu_U^*L, N=J_j M has the explicit etale witness j_!L, and J_b N has witness
b_!j_!L. This uses the extension-zero comparison and etale-origin definitions.
3. Apply the proper/open coefficient-mate site clause to the square with constant
coefficient ring Lambda. Its transported arrow T is the conjugate of the specified
etale proper/open resolution map by the named direct-image and open comparisons.
Interchange coherence identifies its K-injective representative with the one used
by the compact-support composition construction; no automorphism is chosen.
4. Transport-identifies-exchange identifies the restriction exchange with the actual
unit--square--counit towerExchange. Open-comparison unit normalization identifies its
unit with towerOpenUnit. Thus the transported restriction map is towerLambda.
Proper base change on the witness in step 2 and the invertible open unit show it is
invertible, furnishing the existential hLambda below.
5. The coefficient-mate prescription says T is the open adjunct of inverse lambda.
The open adjunction Hom bijection is injective, hence T equals towerGamma. Its
transpose is inverse lambda, equivalently lambda times i^*(gamma) times eta_i is one.
This identifies maps, without claiming that adjunction preserves invertibility.
6. Fix D to the inverse canonical finiteDirectImageComposition. Fix E by uniqueness
of the left adjoint to composite open restriction; towerOpenComposition is that
unit-preserving isomorphism, followed by bj=a. Their identity normalizations follow
from direct-image composition and uniqueness of conjugate open adjoints.
7. Expand the canonical originComposition on the supplied candidates e.restrict, d,
and d.comp e. Its proper/open factor is the transported T of step 3, whose transpose
was identified in steps 4 and 5. Apply P_q and the two compositors of step 6. Replacing
T by gamma gives the displayed equality for this specified alpha, not merely an
existence of some isomorphism between the source and target.
8. Apply the same construction to (r,i), using (i,id) and (b,p), and to (b,p), using
(id,p) and (b,id). Identity-square exchange and the open triangle identities identify
the latter compositor with the identity. The former is T. The composition theorem
makes both compositors isomorphisms on witnessed inputs, so their ratio T=gamma is
invertible. This proves the last clause independently of taking adjuncts. -/
theorem proEtaleCompositionTowerNormalization
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n)
    {U V W : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))] [LocallyOfFiniteType (W ↘ Spec (.of k))]
    [QuasiCompact (W ↘ Spec (.of k))]
    (h : U ⟶ V) (f : V ⟶ W)
    [h.IsOver (Spec (.of k))] [f.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) (e : Compactification (h ≫ d.i)) :
    let Λ := Padic.coefficientExtensionRing l E n
    letI : Finite Λ := Padic.finite_coefficientExtensionRing l E n hn
    let b := pullback.fst e.g d.i
    let r := e.restrict.g
    let w : b ≫ e.g = r ≫ d.i := e.isPullback_restrict.w.symm
    (∀ (N : DerivedCategory
        (Sheaf (Scheme.ProEt.topology e.restrict.Z) (ModuleCat.{u + 1} Λ)))
      (K : DerivedCategory.Plus
        (Sheaf e.restrict.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_eN : (comparisonUpperStar (ModuleCat.{u + 1} Λ) e.restrict.Z).mapDerivedCategory.obj
        K.obj ≅ N),
      ∃ hLambda : IsIso (towerLambda Λ b d.i r e.g w N),
        IsIso (towerGamma Λ b d.i r e.g w N hLambda)) ∧
    ∀ L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    let M := (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj L.obj
    let N := (towerJ Λ e.restrict.i).obj M
    ∃ hLambda : IsIso (towerLambda Λ b d.i r e.g w N),
      (towerOriginComposition Λ h f d e L =
        (towerP Λ d.g).map (towerGamma Λ b d.i r e.g w N hLambda) ≫
          (finiteDirectImageComposition Λ e.g d.g).inv.app ((towerJ Λ b).obj N) ≫
          (towerP Λ (e.g ≫ d.g)).map
            (((towerOpenComposition Λ e.restrict.i b) ≪≫
              towerOpenCongr Λ e.restrict_i_fst).hom.app M)) ∧
        IsIso (towerGamma Λ b d.i r e.g w N hLambda) := by
  sorry

end AlgebraicGeometry.ProEtale
