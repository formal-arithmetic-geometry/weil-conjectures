/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import Sheaf.CategoryTheory.SiteCohomologyPullback
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Additivity and pullback of the finite Kummer first Chern class

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-pur-kummer-additivity;
Stacks Project, Tags 03PL, 03AJ, 040E, 03FD, 08JA and 099R
(blueprint: lem-pur-kummer-additivity).

The finite-root presentation is the one reexported by `FixedFinitePositiveCoefficientTwist`:
comparison inverse image of mu_(ell^N) tensor A represents the specified finite Tate line.
There is no tensor product of G_m with A, and no ramification-divisibility assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The class H²(phi)(delta(alpha(M))), with alpha the canonical frame-torsor class.
Source: Stacks Tags 03PL, 03AJ and 040E (blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChernAbelian (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A m hA T) 2
    (T.kummerδ₁ m hT (Scheme.Pic.toCohomologicalPicardGroup T M))

/-- The actual forget-and-evaluate-on-one comparison is bijective in degree two.
Source: Stacks Tags 03FD and 08JA (blueprint: lem-pur-kummer-additivity).
Proof: Hom_A(A,-) is global sections by evaluation on one. Resolve the target by
injective module sheaves; their underlying abelian sheaves are global-sections acyclic
by lem-weil-pbc-etale-module-cohomology-forget. The acyclic-resolution comparison gives
H² of the same section complex. The Ext/derived-Hom comparison and
lem-pur-rhom-global-sections identify its degree-two cocycles with maps A -> F[2].
The resulting comparison is precisely ordinaryFiniteClass, hence it is bijective. -/
theorem kummerFirstChernRealization_bijective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (ordinaryFiniteClass A T F 2) := by
  sorry

/-- The unique derived morphism realizing the actual Kummer boundary class.
Source: Stacks Tags 03PL, 03FD and 08JA (blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChern (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧ :=
  (Equiv.ofBijective (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T m A hA) 2)
    (kummerFirstChernRealization_bijective A T _)).symm
      (kummerFirstChernAbelian A m hA T hT M)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The finite Kummer Chern class on the small pro-etale site, in the finite-root
presentation of the recorded Tate line. The comparison is applied termwise, exactly
as in siteComparisonDerivedPullbackPlus, on its unbounded ambient category.
Source: Stacks Tag 099R and the finite reduction of def-coefficient-twists-detailed
(blueprint: lem-pur-kummer-additivity). -/
def kummerFirstChern (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (M : T.Pic) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        ((Etale.ordinaryFiniteLine A m hA T)⟦(2 : ℤ)⟧) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
    (Etale.kummerFirstChern A m hA T hT M)

/-- The canonical square comparison g* nu* = nu* g*, by the inverse-image adjunctions
and exact termwise descent. Source: Stacks Tags 03CB and 099R
(blueprint: lem-pur-kummer-additivity). -/
def kummerComparisonPullback (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      Etale.ordinaryFinitePullback A f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- Pullback of a compared finite coefficient object, through the canonical square.
Source: Stacks Tags 03CB and 099R (blueprint: lem-pur-kummer-additivity). -/
def kummerCoefficientPullback (A : Type (u + 1)) [CommRing A]
    {T T' : Scheme.{u}} (f : T' ⟶ T)
    (K : Etale.DerivedCategoryModule A T) (K' : Etale.DerivedCategoryModule A T')
    (e : (Etale.ordinaryFinitePullback A f).obj K ≅ K') :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.obj K' :=
  (kummerComparisonPullback A f).app K ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.mapIso e

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Every power of ell is invertible on a scheme over the fixed field.
Source: purity conventions, ell different from p (blueprint: lem-pur-kummer-additivity).
Proof: ell is prime and distinct from the characteristic p, so its image in k is
nonzero. It is a unit in k; its N-th power remains a unit. The structure morphism's
map on global functions preserves this unit, including when the target ring is zero. -/
theorem kummerPower_isUnit (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (N : ℕ) :
    IsUnit ((P.coefficients.l ^ N : ℕ) : Γ(T, ⊤)) := by
  sorry

/-- Kummer Chern classes are additive, natural for arbitrary pullback (hence for
base-change projections), and independent of the killing exponent. Picard multiplication
is tensor product of invertible modules, and Pic.map is their canonical pullback.
The pro-etale objects are the finite-root presentation of the recorded Tate twist;
its identification with the root-tower reduction is projection-induced.

Source: blueprint lem-pur-kummer-additivity; Stacks Tags 03PL, 03AJ, 040E, 03FD,
08JA and 099R (blueprint: lem-pur-kummer-additivity).
Proof:
1. The coefficient quotient at every positive level is killed by ell^level, since
   ell lies in the maximal ideal of O_E. Any chosen ell^N killing A is invertible
   on T. Apply lem-amb-kummer-any-base to the ordinary Kummer sequence. The
   coefficient insertion z -> z tensor 1 is additive; G_m is never tensored with A.
2. By lem-sc-line-bundle-torsor, frames of M tensor P are the contracted product
   of the two frame torsors: [s,t] maps to s tensor t. On a common trivializing
   cover their transition units multiply. By lem-sc-torsor-h1 this is addition
   of the frame classes in H¹(G_m), with the stated sign convention.
3. Apply lem-weil-pbc-horseshoe-delta-functor to abelian global sections. Its
   boundary and degree-two cohomology maps are additive, giving etale additivity.
   By lem-weil-pbc-etale-module-cohomology-forget and lem-pur-rhom-global-sections,
   evaluation on one identifies these classes additively with derived morphisms.
4. Pulling back frames gives the frame torsor of the pulled-back line bundle:
   both have the pulled-back transition units. Apply the inverse-image and group
   extension clauses of lem-sc-etale-torsor-h1-functoriality.
5. The pulled Kummer sequence maps to that on T' by the canonical roots and units
   comparisons. Powers and inclusions commute. The site-cohomology pullback theorem
   and horseshoe naturality identify their boundaries. Coefficient insertion commutes
   since both routes send z to f*z tensor 1. Use lem-asd-etale-finite-twist-pullback.
   Module/abelian inverse image agrees by the forget-naturality theorem. Compute with
   injective module resolutions, whose underlying abelian terms are acyclic, and
   use the Leray acyclicity comparison. A cocycle s represents the map 1 -> s;
   its pullback represents 1 -> beta(f*s), proving derived-morphism naturality.
6. Comparison inverse image is exact and additive by lem-sf-comparison-pullback-exact.
   A primitive root checks the finite-root comparison is invertible. Tensoring its
   finite presentation with A preserves the comparison. The projections and reductions
   of lem-pur-twist-sheaf-locally-free identify this with the specified Tate line;
   no primitive root enters the projection-defined map. The site-composition theorem
   identifies f*nu* with nu*f*, giving pro-etale additivity and naturality. A projection
   T times_B B' -> T is an instance of the very same pullback equality.
7. For N' >= N map the larger Kummer sequence to the smaller one by the power
   ell^(N'-N) on roots and middle units and identity on the last units. The right
   square commutes since (z^d)^(ell^N) = z^(ell^N'). Horseshoe naturality gives
   the boundary comparison. Coefficient insertion commutes with this power map;
   the normalized twist comparison is invertible by lem-asd-etale-finite-twist-pullback.
   Apply exact comparison for the pro-etale equality. Compare any two exponents to
   their maximum to get full independence, without a ramification divisibility condition.
-/
theorem kummer_additivity (P : PurityFiniteSetting.{u}) (N : ℕ) (hN : 1 ≤ N)
    (hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (∀ M Q : T.Pic,
      Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
          (P.kummerPower_isUnit a N) (M * Q) =
        Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M +
          Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) Q) ∧
    (∀ M Q : T.Pic,
      ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
          (P.kummerPower_isUnit a N) (M * Q) =
        ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M +
          ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) Q) ∧
    (∀ (T' : Scheme.{u}) (a' : T' ⟶ Spec (.of P.field.k))
        (_hs : IsSeparated a') (_hft : LocallyOfFiniteType a') (_hqc : QuasiCompact a')
        (f : T' ⟶ T),
      ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient (P.coefficients.l ^ N) hA)
        (M : T.Pic),
      (Etale.ordinaryFinitePullback P.Coefficient f).map
          (Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M) ≫
        (Etale.ordinaryFiniteShiftedLinePullback P.Coefficient (P.coefficients.l ^ N)
          hA t f (P.kummerPower_isUnit a N)).hom =
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f).hom ≫
        Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T'
          (P.kummerPower_isUnit a' N) (Scheme.Pic.map f M)) ∧
    (∀ (T' : Scheme.{u}) (a' : T' ⟶ Spec (.of P.field.k))
        (_hs : IsSeparated a') (_hft : LocallyOfFiniteType a') (_hqc : QuasiCompact a')
        (f : T' ⟶ T),
      ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient (P.coefficients.l ^ N) hA)
        (M : T.Pic),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory.map
          (ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M) ≫
        (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
          (Etale.ordinaryFiniteShiftedLinePullback P.Coefficient (P.coefficients.l ^ N)
            hA t f (P.kummerPower_isUnit a N))).hom =
      (ProEtale.kummerCoefficientPullback P.Coefficient f _ _
        (Etale.ordinaryFiniteUnitPullback P.Coefficient f)).hom ≫
          ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T'
            (P.kummerPower_isUnit a' N) (Scheme.Pic.map f M)) ∧
    (∀ (N' : ℕ) (_hNN' : N ≤ N')
        (hA' : ((P.coefficients.l ^ N' : ℕ) : P.Coefficient) = 0),
      ∃ (q : T.rootsOfUnitySheaf (P.coefficients.l ^ N') ⟶
          T.rootsOfUnitySheaf (P.coefficients.l ^ N))
        (e : Scheme.finiteEtaleTateLine T (P.coefficients.l ^ N') P.Coefficient hA' ≅
          Scheme.finiteEtaleTateLine T (P.coefficients.l ^ N) P.Coefficient hA),
        q ≫ kernel.ι ((P.coefficients.l ^ N) • 𝟙 T.gmSheaf) =
          (P.coefficients.l ^ (N' - N)) •
            kernel.ι ((P.coefficients.l ^ N') • 𝟙 T.gmSheaf) ∧
        Etale.ordinaryFiniteRootMap P.Coefficient (P.coefficients.l ^ N') hA' T ≫
            (Etale.RawModuleScalarComparison.forget P.Coefficient T).map e.hom =
          q ≫ Etale.ordinaryFiniteRootMap P.Coefficient (P.coefficients.l ^ N) hA T ∧
        (∀ M : T.Pic,
          Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N') hA' T
              (P.kummerPower_isUnit a N') M ≫
            (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map e.hom) =
          Etale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M) ∧
        (∀ M : T.Pic,
          ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N') hA' T
              (P.kummerPower_isUnit a N') M ≫
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory).map
                ((shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map e.hom)) =
          ProEtale.kummerFirstChern P.Coefficient (P.coefficients.l ^ N) hA T
            (P.kummerPower_isUnit a N) M)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
