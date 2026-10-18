/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.Paper.ProEtaleProperOpenComparison
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Finite.Exact
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.BaseChange.Etale
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Site transport of finite proper/open interchange

Source: Stacks Project, Tags 0F7B, 09AF and 099R; the explicit compatibility calculation
in the proof of the DAG node (blueprint: lem-trf-proper-open-site-transport).

The pro-etale arrow is defined by open adjunction from ordinary unit-counit exchange.
The etale arrow is extracted with its proper-support and resolution normalization intact.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The proper-support-normalized etale interchange for finite horizontal maps.
The sheaf witness of `properOpenInterchangeCoherence` is determined by its equality
inside the common ordinary direct image. Descend that normalized sheaf isomorphism
termwise and conjugate by the universal exact-functor comparisons for finite direct
image. On injective representatives this is precisely the resolution map of Tag 0F7B.
Source: Stacks Tag 0F7B (blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportEtale (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' Z' U Z : Scheme.{u}} (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsFinite r] [IsFinite q] (h : j' ≫ q = r ≫ j) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) r)) _ ≪≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      ((Etale.properOpenInterchangeCoherence Λ).choose
        (A := U') (B := Z') (C := U) (D := Z) j' j r q h) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) q)).symm

/-- The canonical composition comparison around the pro-etale square on `D⁺`.
Source: Stacks Tags 099R and 0D6D; the square comparison in the node's step 4
(blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportPullSquare (Λ : Type (u + 1)) [CommRing Λ]
    {U' Z' U Z : Scheme.{u}} (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) (h : j' ≫ q = r ≫ j) :
    (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      ((upperStarComp (ModuleCat.{u + 1} Λ) r j).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) h.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) j' q) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Ordinary ambient exchange: unit for `r`, square pullback comparison, then the
`q` counit. In particular this map is specified independently of site transport.
Source: Stacks Tags 099R and 0D6D; node proof step 4
(blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportExchange (Λ : Type (u + 1)) [CommRing Λ]
    {U' Z' U Z : Scheme.{u}} (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) (h : j' ≫ q = r ≫ j)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z') (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.obj K) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.obj K) :=
  (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.map
      ((properOpenTransportPullSquare Λ j' j r q h).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) q).counit.app K))

/-- The open-extension unit isomorphism on bounded-below complexes, obtained from the
actual sheaf adjunction unit termwise, including its identity-on-sections normalization.
Source: Stacks Tags 09AE and 09AF; node proof step 4
(blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportOpenUnit (Λ : Type (u + 1)) [CommRing Λ]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    𝟭 (DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusIdIso _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Open base change on an extended input, followed by inverse open-extension unit.
Source: Stacks Tags 099R and 09AF; node proof step 4
(blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportDelta (Λ : Type (u + 1)) [CommRing Λ]
    {U' Z' U Z : Scheme.{u}} (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    (h : j' ≫ q = r ≫ j)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology U') (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.obj K)) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj K :=
  properOpenTransportExchange Λ j' j r q h
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.obj K) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.map
      ((properOpenTransportOpenUnit Λ j').inv.app K)

/-- The open base-change map appearing in the defining transpose is invertible.
Source: Stacks Tags 099R, 09AF and 0D6G; node proof steps 2 and 4
(blueprint: lem-trf-proper-open-site-transport).

Proof: restriction to an open subsite is exact and preserves injectives, since its
left adjoint is exact extension by zero. Compute derived direct image on an injective
representative. Restriction of direct image over an object V of U is evaluation on
V times_Z Z', canonically V times_U U' by the Cartesian identification. The ordinary
unit-counit exchange is this identity on sections, so it is invertible degreewise
and after localization. The open-extension unit is also the identity on sections
of the open subsite, hence invertible. Their composite is the displayed delta. -/
theorem isIso_properOpenTransportDelta (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' Z' U Z : Scheme.{u}} [IsNoetherian U'] [IsNoetherian Z']
    [IsNoetherian U] [IsNoetherian Z] (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsFinite r] [IsFinite q] [QuasiCompact j'] [QuasiSeparated j']
    [QuasiCompact j] [QuasiSeparated j] (sq : OpenImmersionSquare r j' j q)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology U') (ModuleCat.{u + 1} Λ))) :
    IsIso (properOpenTransportDelta Λ j' j r q sq.w.symm K) := by
  sorry

/-- The pro-etale proper/open arrow, defined as the transpose of inverse open exchange.
Source: Stacks Tags 099R and 09AF; node's specified transpose convention
(blueprint: lem-trf-proper-open-site-transport). -/
def properOpenTransportProEtale (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' Z' U Z : Scheme.{u}} [IsNoetherian U'] [IsNoetherian Z']
    [IsNoetherian U] [IsNoetherian Z] (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsFinite r] [IsFinite q] [QuasiCompact j'] [QuasiSeparated j']
    [QuasiCompact j] [QuasiSeparated j] (sq : OpenImmersionSquare r j' j q)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology U') (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj K) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.obj K) :=
  have := isIso_properOpenTransportDelta Λ j' j r q sq K
  ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} Λ) j).homEquiv _ _).symm
      (inv (properOpenTransportDelta Λ j' j r q sq.w.symm K))

/-- Site comparison carries the proper-support-normalized etale interchange to the
pro-etale interchange specified by inverse open base change, and the latter is invertible
on every bounded-below etale origin. Source: Stacks Tags 0F7B, 09AF and 099R
(blueprint: lem-trf-proper-open-site-transport).

Proof (the eight steps of the node):
1. Constant-ring identifications preserve constant sections. Finite r and q are proper
(lem-weil-pbc-finite-proper) and finite coefficients are torsion, so the etale proper/open
interchange theorem applies (lem-cbc-proper-open-interchange-coherence). Exact comparison,
pullback and open extension descend the open-unit comparison identity degreewise
(lem-sf-comparison-pullback-exact, lem-weil-pbc-extension-by-zero-exact,
lem-cbc-proetale-extension-zero, lem-sf-open-comparison-unit-normalization,
lem-weil-pbc-localization-universal-property, prop-weil-pbc-proetale-constant-ring-map).
2. Put X = j'!N and M = Rr_*N. Etale open restriction identifies the ordinary exchange
on X with restriction on sections; following by inverse open unit defines the invertible
delta_e (lem-weil-pbc-derived-open-restriction,
lem-weil-pbc-etale-underived-exchange-restriction,
prop-weil-pbc-inverse-image-modules-exact and the extension-zero adjunction).
3. Finite direct image is exact, also on constant-ring modules since forgetting the
action computes kernels and sheafified cokernels. Hence its derived functor is termwise
(lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-exact-functor-derived-functor).
The proper-support normalization sends each section on the open to itself, so the open
transpose of gamma_e is delta_e inverse (lem-cbc-proper-support-sheaf-composition,
lem-weil-pbc-exchange-forget-coefficients).
4. Define delta_p by pro-etale exchange followed by inverse open unit and define gamma_p
by its inverse transpose. The transport-identifies-exchange equation, with f=q, f'=r,
g=j and g'=j', applies to X: the arrows are qcqs, the square Cartesian, X bounded below
and coefficients finite (lem-weil-pbc-transport-identifies-exchange).
5. Expand T as the direct-image mate b_q followed by Rq_*(e_j'). Naturality of exchange
and step 4, then the open-unit identity of step 1 and naturality of b_r, give
  j_p^*(T) followed by delta_p, after a_j = C(delta_e) followed by b_r.
The named b and e are invertible (lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-cbc-proetale-extension-zero-comparison).
6. Transpose G = e_j inverse followed by C(gamma_e) followed by T. Naturality of a_j
and steps 1, 3 and 5 show that delta_p composed with its transpose is b_r. Thus the
transpose is b_r followed by delta_p inverse.
7. Naturality of the pro-etale open unit shows that j_p!(b_r) followed by gamma_p has
the same transpose. Injectivity of the open adjunction Hom bijection proves the stated
equality after precomposing with e_j.
8. S and T are isomorphisms by their canonical comparison factors. Gamma_e is invertible
by the proper/open theorem. The equality expresses gamma_p as the conjugate of
C(gamma_e) by S and T, proving the last assertion. -/
theorem properOpen_site_transport (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' Z' U Z : Scheme.{u}} [IsNoetherian U'] [IsNoetherian Z']
    [IsNoetherian U] [IsNoetherian Z] (j' : U' ⟶ Z') (j : U ⟶ Z)
    (r : U' ⟶ U) (q : Z' ⟶ Z) [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsFinite r] [IsFinite q] [QuasiCompact r] [QuasiSeparated r]
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact j'] [QuasiSeparated j']
    [QuasiCompact j] [QuasiSeparated j] (sq : OpenImmersionSquare r j' j q)
    (N : DerivedCategory.Plus (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((properOpenSiteExtensionIso Λ j).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj N) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ r).app N)) ≫
      properOpenTransportProEtale Λ j' j r q sq
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U').mapDerivedCategoryPlus.obj N) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.map
        ((properOpenTransportEtale Λ j' j r q sq.w.symm).hom.app N) ≫
      ((fixedComparisonDirectImageMatePlus Λ q).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategoryPlus.obj
            N) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso Λ j').hom.app N)) ∧
    IsIso (properOpenTransportProEtale Λ j' j r q sq
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U').mapDerivedCategoryPlus.obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale
