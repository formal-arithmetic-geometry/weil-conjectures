/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.TraceFormula.OrientedPointCohomology
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.PsiConstructibilityDescent
import Sheaf.TraceFormula.PsiProperSurjectiveConstructibility

/-!
# Constructible strata for Psi-good oriented nearby-cycle cohomology

Source: Lu--Zheng, Duality and nearby cycles over general bases, Theorem 4.27(2)
and the following definition of constructibility, v7 author PDF
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).

The canonical site, scalar and stratum transports below connect the recorded nearby-cycle
functor to the recorded constructible sheaf and stratification interfaces. All constructions
have real data. Only the theorem and named properties of the transports are postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.OrientedNearbyCycles CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata

/-- Fixed-ring coefficients of a module over the constant commutative ring sheaf.
Use the existing canonical CommRingCat-to-RingCat coefficient identification and the
recorded constant-ring module restriction, retaining the original module action.
Source: Stacks 03CY; Lu--Zheng, definition after Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def fixedSheaf (S : Site.{u}) (A : Type u) [CommRing A] (M : S.modules A) :
    Sheaf S.topology (ModuleCat.{u} A) :=
  (constantRingModuleRestriction S.topology A).obj
    ((SheafOfModules.restrictScalars (realizationRingIso S.topology A).inv).obj M)

/-- The inverse of the existing transported-site equivalence is continuous.
Source: ILO XI §4.3; Stacks 00X6
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: etaleTopology is the topology induced by AsSmall.down. The inverse equivalence
AsSmall.up carries an etale cover to that induced cover. Applying AsSmall.down to its
image recovers the original cover, so the covering-sieve sheaf condition is unchanged. -/
theorem upContinuous (X : Scheme.{u}) :
    (AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).IsContinuous
      X.smallEtaleTopology (etaleTopology X) := by
  sorry

attribute [instance] upContinuous

/-- Read the existing constant-ring module sheaf on the original small etale site.
The AsSmall equivalence and fixedSheaf perform only canonical site and scalar transport.
Source: Stacks 03CY; ILO XI §4.3
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def etaleFixed (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (L : (etaleDatum.{u, u + 1} X).modules A) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  ((AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) X.smallEtaleTopology (etaleTopology X)).obj
      (fixedSheaf (etaleDatum X) A L)

/-- The already defined two-map oriented product, in the common coefficient universe.
This is an abbreviation of the published datum, with no new topology.
Source: ILO XI §1.1; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev productSite {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  CategoryTheory.OrientedPointCohomology.datum.{u, u} a b

/-- Canonical base-change associativity for the two outer entries of a triple.
The middle etale S-scheme stays fixed. The first arrow uses etaleBaseChangeComp and
the second arrow is the identity on its pullback along j.
Source: ILO XI §1.9; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictBeta {X S X' S' : Scheme.{u}} (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (etaleBaseChange.{u, u + 1} f).prod' (𝟭 (EtaleSite S)) ⋙
        (etaleBaseChange i).prod (etaleBaseChange j) ⟶
      𝟭 (EtaleSite S) ⋙ (etaleBaseChange (i ≫ f)).prod' (etaleBaseChange j) where
  app V := ((etaleBaseChangeComp i f).inv.app V, 𝟙 _)
  naturality := fun V W h ↦ Prod.ext ((etaleBaseChangeComp i f).inv.naturality h)
    (by simp)

/-- Pull back the outer entries of (U to V from W) along i and j, keeping V.
Comma.map gives the actual action on objects and arrows, using canonical fibre-product
associativity. This is the site inverse image of the oriented stratum morphism.
Source: ILO XI §§1.6, 1.9; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictSite {X S X' S' : Scheme.{u}} (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (vanishingDatum.{u, u + 1} f).objects ⥤ (productSite (i ≫ f) j).objects :=
  Comma.map
    ((Functor.rightUnitor ((etaleBaseChange i).prod (etaleBaseChange j)) ≪≫
      (Functor.leftUnitor ((etaleBaseChange i).prod (etaleBaseChange j))).symm).hom)
    (restrictBeta f i j)


/-- The canonical stratum site inverse image is continuous and left exact.
Source: ILO XI §§1.1, 1.6, 1.9
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: limits of triples are computed componentwise; scheme base change preserves
finite limits and the associativity comparisons identify the structural arrows.
Coverings of types (a) and (b) pull back to etale coverings. A type-(c) arrow remains
type (c), since its defining cartesian square remains cartesian after base change.
Thus all generating covers are preserved. The finite-limit cover-preservation criterion
of Stacks 00X6 gives continuity for their generated topologies. On the two projections
and the middle triple this functor gives the immersions and their orientation; hence,
by lem-trf-oriented-product-universal, its geometric morphism is the required lift. -/
theorem restrictSite_properties {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (restrictSite f i j).IsContinuous (vanishingTopology.{u, u + 1} f)
      (productSite (i ≫ f) j).topology ∧ PreservesFiniteLimits (restrictSite f i j) := by
  sorry
/-- Continuity supplied by the canonical stratum functor's property theorem.
Source: ILO XI §1.9 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance restrictSite_continuous {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (restrictSite f i j).IsContinuous (vanishingTopology.{u, u + 1} f)
      (productSite (i ≫ f) j).topology := (restrictSite_properties f i j).1
/-- Left exactness supplied by the canonical stratum functor's property theorem.
Source: ILO XI §1.9 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance restrictSite_finiteLimits {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    PreservesFiniteLimits (restrictSite f i j) := (restrictSite_properties f i j).2

/-- Finite limits on the existing vanishing site's comma category.
Source: ILO XI §1.1 (blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: take finite limits in each of the three etale entries. Base change along f and
the identity preserve these limits, so the two structural arrows into the middle entry
induce the structural arrows of the limit triple. Its three projections determine
unique compatible maps from every cone, proving the comma universal property. -/
theorem vanishing_finiteLimits {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteLimits (VanishingSite.{u, u + 1} f) := by
  sorry
attribute [instance] vanishing_finiteLimits

/-- The existing finite-limit structure on the published two-map oriented triple site.
Source: ILO XI §1.1 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance product_finiteLimits {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    HasFiniteLimits (productSite a b).objects :=
  CategoryTheory.OrientedPointCohomology.triples_finiteLimits a b

/-- The canonical oriented stratum restriction, lifted to constant-ring modules.
Use siteMorphism and the existing canonical moduleMorphism, whose modulePull is exact.
Source: ILO XI §1.9; Stacks 03D2; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictionModules {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :=
  letI := (restrictSite_properties f i j).1
  letI := (restrictSite_properties f i j).2
  moduleMorphism (vanishingDatum.{u, u + 1} f) (productSite (i ≫ f) j)
    (siteMorphism (vanishingTopology.{u, u + 1} f) (productSite (i ≫ f) j).topology
      (restrictSite f i j))

/-- The sheaf L in degree zero, using the same standard localization as nearbyCycles.
Coeff is the recorded canonical ULift of Lambda; no coefficient ring is changed.
Source: Lu--Zheng, Theorem 4.27(2), degree-zero specialization
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev degreeZero (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) :
    EtaleDerived X Λ :=
  (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj L

/-- The q-th cohomology sheaf of the recorded nearby-cycle functor on L[0].
Source: Lu--Zheng, Theorem 4.27(2)
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev cohomology {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [CommRing Λ]
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) (q : ℤ) :=
  (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj
    ((nearbyCycles f Λ).obj (degreeZero X Λ L))


/-- Psi-good nearby-cycle cohomology admits finite constructible locally closed strata
on both factors, with finite constant module values on a covering of each oriented
stratum. The strata may depend on q; no uniform vanishing bound is claimed.

Source: Lu--Zheng, Duality and nearby cycles over general bases, Theorem 4.27(2)
and the following constructibility definition, v7 author PDF
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).

Proof plan, following the five steps of the node:
1. Place the constructible sheaf L in degree zero. It is bounded constructible with
amplitude [0,0], by def-weil-pbc-constructible-complexes.
2. Apply lem-trf-psi-proper-surjective-constructibility to this bounded input and q.
It supplies a proper surjective T to S on which the nearby cycles of the base-changed
family have constructible q-th cohomology.
3. By def-trf-oriented-nearby-cycles, Psi-goodness makes the canonical base-change map
an isomorphism. The exact constant-coefficient inverse image commutes with cohomology.
Consequently the inverse image of G_q is isomorphic to that constructible sheaf.
Transport its strata and finite constant trivializations across this isomorphism.
4. Apply lem-trf-psi-constructibility-descent along the proper surjective T to S.
This gives constructibility of G_q on V_f.
5. Unfold def-trf-oriented-constructible-sheaf with the second map the identity of S.
It yields the two finite locally closed stratifications, constructibility of each part,
and finite constant trivializations on each oriented stratum. The site restriction
constructed above is the universal-property morphism, since it has exactly the two
specified projections and orientation. A covering sieve of the terminal triple encodes
the covering family of the final object, and over Z encodes its slice topos. -/
theorem exists_constructible_cohomology_strata {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (_hm : 1 ≤ m) (_hΛ : (m : Λ) = 0) (_hS : IsUnit (m : Γ(S, ⊤)))
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ))
    (_hc : Scheme.IsConstructibleEtaleModuleSheaf
      (etaleFixed X (Coeff Λ) L)) (_hgood : IsPsiGood f Λ (degreeZero X Λ L))
    (q : ℤ) (_hq : 0 ≤ q) :
    ∃ (A : Scheme.LocallyClosedStratification X) (B : Scheme.LocallyClosedStratification S),
      (∀ a : Fin A.n, Topology.IsConstructible (A.stratum a)) ∧
      (∀ b : Fin B.n, Topology.IsConstructible (B.stratum b)) ∧
      ∀ (a : Fin A.n) (b : Fin B.n),
        ∃ R : (productSite (A.immersion a ≫ f) (B.immersion b)).topology.Cover
          (⊤_ (productSite (A.immersion a ≫ f) (B.immersion b)).objects),
        ∀ (Z : (productSite (A.immersion a ≫ f) (B.immersion b)).objects)
          (r : Z ⟶ ⊤_ (productSite (A.immersion a ≫ f) (B.immersion b)).objects), R r →
          ∃ M : ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ), Finite M ∧
            Nonempty
              ((fixedSheaf (productSite (A.immersion a ≫ f) (B.immersion b)) (Coeff Λ)
                (((restrictionModules f (A.immersion a) (B.immersion b)).modulePull
                  (Coeff Λ)).obj (cohomology f Λ L q))).over Z ≅
                (constantSheaf
                  ((productSite (A.immersion a ≫ f) (B.immersion b)).topology.over Z)
                  (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ))).obj M) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata
