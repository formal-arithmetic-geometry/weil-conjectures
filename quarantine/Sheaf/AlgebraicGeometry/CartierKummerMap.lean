/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
import Sheaf.CategoryTheory.Sites.TorsorWithSection
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.PbcCoefficientTwists
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # The supported Cartier Kummer morphism

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.md and its proof, paragraphs 1--4;
Stacks Project, Tags 03PL, 0A45 and 099R (blueprint: lem-amb-cartier-kummer-map).

The imported fixed-coefficient presentation restricts the published ringed Tate line
along constant scalars. Its underlying groups and inverse-limit construction are unchanged.
Natural-number level n denotes the positive quotient exponent n+1.

## Main definitions and statement

* The normalization predicates specify Kummer boundaries, root projections, and functoriality.
* `cartier_kummer_map`: existence and uniqueness of the normalized simultaneous system.
* `cartierKummerMap`: its canonical derived morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

open Scheme

/-- Reuse the existing left-exact sheafification at each etale module site.
Source: Stacks 00WX (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierHasSheafifyEtale (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Cache the existing weak etale sheafification separately from left exactness.
Source: Stacks 00WX (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierHasWeakSheafifyEtale (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance

/-- Reuse abelian sheafification for the cohomological Chern-class realization.
Source: Stacks 00WX (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierHasSheafifyAbelian (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  inferInstance

/-- Reuse small Ext for the existing abelian cohomology realization.
Source: Stacks 07A6 (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierHasExtAbelian (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Name the existing abelian structure on etale module sheaves.
Source: Stacks 03D0 (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierAbelianEtale (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

/-- Name the existing abelian structure used by the Chern-class realization.
Source: Stacks 03D0 (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierAbelianGroups (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Cache the existing small Ext instance without changing its universe or category.
Source: Stacks 07A6 (blueprint: lem-amb-cartier-kummer-map). -/
instance cartierHasExtEtale (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant-section comparison for the inclusion of sites, specified by adjunction.
Source: Stacks 099R and 00WX (blueprint: lem-amb-cartier-kummer-map). -/
def cartierConstantComparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (ordinaryFiniteConstant A T) ⟶
      (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).symm
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A)))))

/-- The etale witnesses at every annihilating Kummer exponent.
Source: proof, paragraphs 3--4 (blueprint: lem-amb-cartier-kummer-map). -/
def CartierEtaleKummerFamily : Type (u + 1) :=
  ∀ (n r : ℕ) (_hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hT : IsUnit (l : Γ(T, ⊤))),
    Ext ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
      (ordinaryFiniteConstant (finiteTateCoefficient l E n) D))
        (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) _hA) 2

/-- Relative-boundary normalization of all ordinary etale witnesses.
This retains the actual frame torsor and its canonical section on the complement.
Source: proof, paragraphs 1--3 (blueprint: lem-amb-cartier-kummer-map). -/
@[irreducible]
def CartierEtaleKummerNormalization (κ : CartierEtaleKummerFamily l E) : Prop :=
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    SupportedKummerBoundary (finiteTateCoefficient l E n) (l ^ (r + 1)) hA i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) (κ n r hA i hI hT)

/-- Compatibility with every finite coefficient reduction at a common Kummer exponent.
SupportedKummerScalar specifies both derived scalar units on all unbounded test objects
and fixes the scalar maps on constants and pure root tensors.
Source: proof, final scalar-extension sentence
(blueprint: lem-amb-cartier-kummer-map). -/
@[irreducible]
def CartierEtaleKummerReduction (κ : CartierEtaleKummerFamily l E) : Prop :=
  ∀ (a b : ℕ) (hab : a ≤ b) (r : ℕ)
    (hb : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E b) = 0)
    (ha : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E a) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    SupportedKummerScalar (cartierCoefficientReduction l E a b hab) (l ^ (r + 1)) hb ha i
      (κ b r hb i hI hT) (κ a r ha i hI hT)

/-- Descent of each etale witness to the same arrow in the specified pro-etale twist.
The support comparison is uniquely fixed by the quotient map. The target comparison
is fixed by inverse-limit projection. Quantifying over every r while c is fixed
states independence of the Kummer exponent as equality of derived arrows.
Source: proof, final paragraph (blueprint: lem-amb-cartier-kummer-map). -/
@[irreducible]
def CartierKummerRealization (κ : CartierEtaleKummerFamily l E)
    (c : CartierKummerFamily l E) : Prop :=
  ∀ (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∃ (α : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          ((lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) i).obj
            (ordinaryFiniteConstant (finiteTateCoefficient l E n) D)) ≅ cartierSupported l E n i)
      (q : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) ≅
            finiteTateProSheaf l E n T 1),
      IsFiniteTateSiteComparison l E n T r hA 1 q ∧
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).map
          (supportedConstantUnit (finiteTateCoefficient l E n) i) ≫ α.hom =
        cartierConstantComparison (finiteTateCoefficient l E n) T ≫
          cartierSupportedUnit l E n i ∧
      (Ext.mk₀ α.hom).comp (c n i hI hT) (zero_add 2) =
        ((κ n r hA i hI hT).mapExactFunctor
          (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
          (Ext.mk₀ q.hom) (add_zero 2)

/-- The asserted pro-etale base-change equation under the canonical comparisons.
The support comparison is fixed by the constant quotient unit and the twist comparison
by all root projections. No flatness is imposed on h.
Source: proof, paragraph 4 (blueprint: lem-amb-cartier-kummer-map). -/
@[irreducible]
def CartierKummerBaseChange (c : CartierKummerFamily l E) : Prop :=
  ∀ (n : ℕ) {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i'] (h : T' ⟶ T) (w : D' ⟶ D)
    (_sq : IsPullback w i' i h) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤))),
    ∃ (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).obj
        (cartierSupported l E n i) ≅ cartierSupported l E n i')
      (t : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).obj
        (finiteTateProSheaf l E n T 1) ≅ finiteTateProSheaf l E n T' 1),
      IsFiniteTateProPullback l E n T h 1 t ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h).map
          (cartierSupportedUnit l E n i) ≫ p.hom =
        Scheme.proEtaleConstantInverseImageMap h
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
            (ModuleCat.of (finiteTateCoefficient l E n) (finiteTateCoefficient l E n)) ≫
          cartierSupportedUnit l E n i' ∧
      (Ext.mk₀ p.hom).comp (c n i' hI' hT') (zero_add 2) =
        ((c n i hI hT).mapExactFunctor
          (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) h)).comp
            (Ext.mk₀ t.hom) (add_zero 2)

/-- The ordinary first Chern class, transported by the same projection-normalized
comparison, is the composite with the supported quotient map.
The cohomology class is written directly in Ext: the definition of `ordinaryFiniteClass`
reduces to this expression by cancelling `Ext.homEquiv.symm (Ext.homEquiv k)`.
This avoids elaborating the intermediate derived arrow and its inverse realization.
Source: proof, paragraphs 3--4 (blueprint: lem-amb-cartier-kummer-map). -/
@[irreducible]
def CartierKummerChern (c : CartierKummerFamily l E) : Prop :=
  ∀ (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))),
    ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0),
      ∃ (k : Ext (ordinaryFiniteConstant (finiteTateCoefficient l E n) T)
        (Scheme.finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA) 2)
        (q : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
            (Scheme.finiteEtaleTateLine T (l ^ (r + 1))
              (finiteTateCoefficient l E n) hA) ≅ finiteTateProSheaf l E n T 1),
        IsFiniteTateSiteComparison l E n T r hA 1 q ∧
        (Ext.mk₀ (ordinaryFiniteIntegralGenerator (finiteTateCoefficient l E n) T)).comp
          (k.mapExactFunctor (RawModuleScalarComparison.forget (finiteTateCoefficient l E n) T))
          (zero_add 2) = supportedKummerChern (finiteTateCoefficient l E n)
            (l ^ (r + 1)) hA i hI
              (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) ∧
        (Ext.mk₀ (cartierConstantComparison (finiteTateCoefficient l E n) T)).comp
          ((Ext.mk₀ (cartierSupportedUnit l E n i)).comp (c n i hI hT) (zero_add 2))
            (zero_add 2) =
          (k.mapExactFunctor (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)).comp
              (Ext.mk₀ q.hom) (add_zero 2)

/-- The normalized supported Cartier Kummer map for all positive coefficient levels.
The witness is simultaneous in the scheme, divisor, coefficient level and auxiliary
Kummer exponent. The uniqueness concerns the arrows, rather than auxiliary choices
of covers, resolutions, or comparison proofs.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.md and its proof, paragraphs 1--4; Stacks 03PL, 0A45, 099R
(blueprint: lem-amb-cartier-kummer-map).

Proof:
1. An exponent exists since l has positive integral valuation in O_E. For quotient
exponent m one can take l^m, independently of the ramification index.
2. The Cartier ideal's dual is O(D). Its canonical section is dual to the ideal
inclusion. On a chart I=(f), its dual basis e satisfies s_D=f e; changing f to u f
changes e to u^-1 e and leaves s_D unchanged. Off D it is a specified frame.
3. The frame torsor with this section gives its relative H1 class by
lem-amb-relative-torsor-cohomology, independently of charts and refinements.
4. Apply lem-amb-kummer-any-base to the relative class. Naturality of the boundary
sends its forgotten-support image to the Kummer boundary of O(D), its Chern class.
The multiplicative group is used only as an abelian sheaf, never as a Z/l^r-module.
5. The derived module/abelian coefficient-forgetting comparison respects restriction.
It identifies the relative cones; lem-amb-closed-support-hom turns the relative H2
class into the supported Ext class. The open-closed sequence identifies forgetting
support with precomposition by the supported constant quotient.
6. Apply derived scalar extension to A. The supported constant has stalk Z/l^r on
D and zero off D; its canonical extension has stalk A and zero. Monoidality,
exactness and conservativity of geometric stalks prove the source comparison is
invertible. No flatness of A over Z/l^r is used. The existing ordinary supported
Kummer interface records precisely this relative boundary and these scalar units.
7. Cartier-preserving pullback preserves the local line and its section. The
relative torsor class and Kummer sequence therefore pull back. The root comparison
is normalized inside units; the supported constant exchange is the identity on
stalks, hence invertible. Naturality of support Hom and coefficient forgetting
gives the etale base-change square.
8. By lem-amb-finite-tate-site-descent, the finite root module is a flat rank-one
line, so its ordinary scalar extension
is its derived scalar extension. The original Z_l(1) quotient by l^r is mu_(l^r),
via the root projection. Tensor associativity then gives the specified comparison
with A(1), whose inverse sends x tensor a to p_r(x) tensor a, for every m.
9. The Cartier complement is locally principal and its open immersion is
quasi-compact. Exact comparison pullback and the extension-by-zero comparison
identify the supported quotients, preserving their constant quotient maps.
10. Conjugate the etale map by that supported-source comparison and the twist
comparison. This is c_D; its composite with A_T to i_*A_D is the transported
ordinary Kummer Chern class. This also retains the ordinary etale witness.
11. For s ≥ r the Kummer-sequence diagram has middle map u to u^(l^(s-r)), right
map the identity, and the same power map on roots. Relative-boundary naturality
identifies the classes. Successive K-flat scalar extension is direct extension.
Since p_r=p_(s,r)p_s, the twist comparisons agree. Comparing two exponents through
their maximum proves exponent independence.
12. Choose a common exponent for two quotient coefficients. K-flat tensor
associativity and the constant/pure-tensor formulas identify direct and successive
extension and prove every coefficient-reduction square, including identity levels.
13. Scheme pullback commutes with the inclusion of sites. Its adjunction comparisons
preserve constant quotients and root projections. The etale square in step 7
therefore gives the displayed pro-etale square. Every normalized comparison used
above is unique on local generators; the relative boundary uniquely determines
the etale class, so the simultaneous pair of arrow families is unique.
-/
theorem cartier_kummer_map :
    (∀ n : ℕ, ∃ r : ℕ, ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) ∧
    ∃! data : CartierEtaleKummerFamily l E × CartierKummerFamily l E,
      CartierEtaleKummerNormalization l E data.1 ∧
      CartierEtaleKummerReduction l E data.1 ∧
      CartierKummerRealization l E data.1 data.2 ∧
      CartierKummerChern l E data.2 ∧
      CartierKummerBaseChange l E data.2 ∧
      CartierKummerReduction l E data.2 := by
  sorry

/-- The canonical supported arrow, selected from its uniquely normalized system.
Its target is the published pro-etale Tate line; no new twisting object is chosen.
Source: blueprint, statement (blueprint: lem-amb-cartier-kummer-map). -/
def cartierKummerMap (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    (DerivedCategory.singleFunctor _ 0).obj (cartierSupported l E n i) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (finiteTateProSheaf l E n T 1))⟦(2 : ℤ)⟧ :=
  ((cartier_kummer_map l E).2.exists.choose.2 n i hI hT).hom

end AlgebraicGeometry.Etale
