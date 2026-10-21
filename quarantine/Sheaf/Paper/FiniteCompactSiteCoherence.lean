/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.ProperOpenCoefficientMate
public import Sheaf.Paper.RefinementCoefficientMate
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.ComparisonPullbackExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.Compactification.CategoryBaseChange

/-! # Finite-ring compact-support site coherence

Source: Stacks Project, more-etale.tex, Tags 0F7I, 0F7J and 0F7K;
canonical site-square deduction in the DAG
(blueprint: lem-sp-finite-compact-site-coherence).

The tower arrow below uses the specified open adjunct Gamma, not conjugation of
an etale composition arrow. All inputs retain their bounded-below etale witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (R : Type (u + 1)) [CommRing R] [Finite R]

/-- Change of compactification through the canonical common proper refinement,
in bounded-below pro-etale modules. Each leg uses the proper/open refinement map.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteChangePlus {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :=
  (properTransportRefinementPlus R (Compactification.infFst c d) E).symm ≪≫
    properTransportRefinementPlus R (Compactification.infSnd c d) E

/-- Change on an explicitly witnessed etale-origin object. The witness is retained
and the underlying change is the computed common-refinement map.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteChangeAtWitness {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (w : (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E ≅ K) :=
  (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).mapIso w.symm ≪≫
    finiteCompactSiteChangePlus R c d E ≪≫
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).mapIso w

/-- Equality transport of derived open extension, including the open-immersion instance.
Source: Stacks Tag 0F7J (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteOpenCongr {X Y : Scheme.{u}} {j k : X ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion k] (w : j = k) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) k).mapDerivedCategoryPlus := by
  subst k
  exact Iso.refl _

/-- Canonical open-extension composition on a compatible tower, including its
factorization equality. Source: Stacks Tag 0F7J
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteTowerOpen {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cf.i).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.q).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cfg.i).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (proEtaleOpenExtensionComp R T.cf.i T.q).symm ≪≫
    finiteCompactSiteOpenCongr R T.i_q

/-- The computed tower arrow: apply P_q to the open adjunct Gamma, then the proper
and open compositors. The first and last open comparisons insert the etale witness
of J_a N E. Source: Stacks Tag 0F7J, the four displayed functors in its proof
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteTowerPlus {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    [IsNoetherian Y] [IsNoetherian Z]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cg).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cf).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cfg).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) :=
  letI := isNoetherian_of_locallyOfFiniteType T.cf.g
  letI := isNoetherian_of_locallyOfFiniteType T.cfg.g
  letI := isNoetherian_of_locallyOfFiniteType T.cg.g
  (lowerStar (ModuleCat.{u + 1} R) T.cg.g).rightDerivedFunctorPlus.map
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cg.i).mapDerivedCategoryPlus.map
        ((lowerStar (ModuleCat.{u + 1} R) T.cf.g).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso R T.cf.i).inv.app E)) ≫
      properOpenSiteInterchange R T.isPullback.flip
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} R) T.cf.i).mapDerivedCategoryPlus.obj E) ≫
      (lowerStar (ModuleCat.{u + 1} R) T.p).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) T.q).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso R T.cf.i).hom.app E))) ≫
    (proEtaleComparisonDirectImageCompIso R T.p T.cg.g).hom.app _ ≫
    (properTransportDirectImageCongr R T.p_g).hom.app _ ≫
    (lowerStar (ModuleCat.{u + 1} R) T.cfg.g).rightDerivedFunctorPlus.map
      ((finiteCompactSiteTowerOpen R T).hom.app _)

/-- Composition on arbitrary supplied compactifications, computed through the supplied
tower and proper/open common-refinement changes. The middle witness is exactly C_f.
Source: Stacks Tags 0F7I and 0F7J
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteCompositionPlus {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    [IsNoetherian Y] [IsNoetherian Z]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) :=
  (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
      ((finiteCompactSiteChangePlus R c T.cf E).hom) ≫
    (finiteCompactSiteChangeAtWitness R d T.cg
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cf).obj E)
      _ ((compactSupportSiteComparisonPlus R T.cf).app E)).hom ≫
    finiteCompactSiteTowerPlus R T E ≫
    (finiteCompactSiteChangePlus R T.cfg e E).hom


/-- The computed composition at an isomorphic etale-origin input, by functorial
transport of its retained witness. Source: Stacks Tag 0F7J
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteCompositionAtWitness
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    [IsNoetherian Y] [IsNoetherian Z]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (w : (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E ≅ K) :=
  (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).map w.inv) ≫
    finiteCompactSiteCompositionPlus R c d e T E ≫
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) e).map w.hom

/-- The unit for the identity compactification: the derived direct-image identity
and the open-adjunction identity. Source: Stacks Tags 0F7J and 0F7K
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteIdentityProPlus (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper (𝟙 X)) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _
    (Functor.rightDerivedFunctorPlusNatIso
      (G := 𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
      (lowerStarId (ModuleCat.{u + 1} R) X) ≪≫
      Functor.rightDerivedFunctorPlusIdIso _) ≪≫
    Functor.rightUnitor _ ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} R) X)) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- C is invertible on every bounded-below etale complex.
Source: Stacks Tags 09AF and 099R
(blueprint: lem-sp-finite-compact-site-coherence).
Proof: exact open extension and comparison preserve the lower bound. Proper maps
between Noetherian schemes satisfy the qcqs hypotheses of the specified direct-image
mate. The open comparison and that mate are invertible; their pasted C is invertible.
The result F_pro N E retains the etale witness F_et E and the isomorphism C(E).
-/
theorem finiteCompactSiteComparison_isIso
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso ((compactSupportSiteComparisonPlus R c).hom.app E) := by
  sorry

/-- The site square for the actual proper/open refinement arrow. Here c is the fine
compactification and d the coarse one, so rho is the inverse of properTransportRefinementPlus.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence).
Proof: expand rho as P(alpha) followed by the proper compositor, using
lem-amb-etale-compact-comparisons. Normalize direct-image composition with
lem-sfb-derived-composition-adjunction-normalization and lem-weil-pbc-mate-pasting.
The counit mates d then compose. Naturality moves N(alpha) next to d_u; the site
clause of lem-sp-refinement-coefficient-mate replaces the three inner factors by
alpha_pro followed by the open comparison. Naturality of the proper compositor
moves that open comparison to its final position, giving precisely the two paths.
No Cartesian hypothesis is placed on the original refinement square.
-/
theorem finiteCompactSite_refinement
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).hom.app E) ≫
      (compactSupportSiteComparisonPlus R c).hom.app E =
    (compactSupportSiteComparisonPlus R d).hom.app E ≫
      (properTransportRefinementPlus R r E).inv := by
  sorry

/-- Every common refinement gives the same computed change, and the site square
holds for the canonical etale change. Source: Stacks Tag 0F7I
(blueprint: lem-sp-finite-compact-site-coherence).
Proof: apply finiteCompactSite_refinement to both legs, invert the first leg and
compose. The etale independence and cocycle laws of lem-amb-etale-compact-comparisons
identify the resulting etale map for every common refinement. Cancel the invertible
source C to identify the pro-etale maps, including the specified infimum refinement.
-/
theorem finiteCompactSite_common_refinement
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (properTransportRefinementPlus R r E).symm ≪≫
        properTransportRefinementPlus R s E = finiteCompactSiteChangePlus R c d E ∧
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso R c d).hom.app E) ≫
      (compactSupportSiteComparisonPlus R d).hom.app E =
    (compactSupportSiteComparisonPlus R c).hom.app E ≫
      (finiteCompactSiteChangePlus R c d E).hom := by
  sorry

/-- The computed changes satisfy the unit and cocycle laws.
Source: Stacks Tags 0F7I and 0F7K (blueprint: lem-sp-finite-compact-site-coherence).
Proof: use the common-refinement site squares to express every change as
C_c inverse, N of the etale change, C_d. Adjacent C C inverse cancel; the etale
identity and cocycle laws give the two equations. Equality of isomorphisms follows
from equality of their hom maps.
-/
theorem finiteCompactSite_change_coherence
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    finiteCompactSiteChangePlus R c c E = Iso.refl _ ∧
    finiteCompactSiteChangePlus R c d E ≪≫ finiteCompactSiteChangePlus R d e E =
      finiteCompactSiteChangePlus R c e E := by
  sorry

/-- The computed tower composition satisfies the site-comparison equation, for
arbitrary finite commutative coefficients and every supplied compactification tower.
Source: Stacks Tags 0F7I, 0F7J and 0F7K
(blueprint: lem-sp-finite-compact-site-coherence).

Proof (the eight steps of the node):
1. Exact open extensions and N preserve lower bounds. Each proper map between the
Noetherian schemes is qcqs. Thus the specified proper counit mate and the open
comparison are invertible, and F_pro N E has witness F_et E via C(E).
2. Derive the ordinary direct-image compositors with their adjunction normalization,
using lem-sfb-derived-composition-adjunction-normalization. The module sheaf categories
are Grothendieck by lem-cbc-sieve-module-sheaves-grothendieck and the constant-ring
module realization. Exact inverse images and their adjunctions give the Grothendieck
hypotheses. The inverse-image comparisons compose. Parts (2), (3), (4) of
lem-weil-pbc-mate-pasting therefore give composition and identity for the specified d.
The exact open comparison composition equation descends termwise as well.
3. The refinement square follows by expanding P(alpha), applying the site clause of
lem-sp-refinement-coefficient-mate, and using naturality and step 2.
4. On T, lem-amb-unbounded-compact-support-comparisons normalizes etale composition
to P_q(Gamma_et J_a), followed by the proper and open compositors. It restricts on
D+ to lem-amb-etale-compact-comparisons. The pro-etale arrow in this module uses
properOpenSiteInterchange, the specified open adjunct of inverse transported restriction.
5. Evaluate lem-sp-proper-open-coefficient-mate on J_a E. Whisker its site square by
P_q and J_a; attach d_q on the source and P_q P_p J_b(e_a) on the target.
Naturality of d_q and Gamma_pro gives the two comparison paths for the tower word.
6. Postcompose with the proper and open compositors. Step 2 replaces comparison for
the word P_q P_p J_b J_a by C_gf. The result is exactly the equation below.
7. Use lem-cbc-compactifiable-compatible-tower and lem-cbc-compactifiable-cofiltered
to compare arbitrary candidates with the tower. The refinement squares of step 3
move C through each change. Naturality moves C_g through the change of F_f E;
etale tower independence cancels the remaining comparisons. Every tower yields the
same computed pro-etale arrow, equal to transport through C as a conclusion.
8. Identity d is normalized, and identity e is an invertible idempotent by its
composition law. For three maps substitute this equation twice and use naturality:
both paths are C_hgf N(alpha_et_triple) followed by the inverse of
F_h F_g(C_f), F_h(C_g F_f), C_h(F_g F_f). Etale associativity and units give
pro-etale associativity and units. Naturality follows from that of all constituents.
No coefficient presentation or base field is used.
-/
theorem finiteCompactSiteCoherence
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategoryPlus.map
        ((coherenceEtaleCompositor R c d e).hom.app E) ≫
      (compactSupportSiteComparisonPlus R e).hom.app E =
    (compactSupportSiteComparisonPlus R d).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj E) ≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
        ((compactSupportSiteComparisonPlus R c).hom.app E) ≫
      finiteCompactSiteCompositionPlus R c d e T E := by
  sorry

/-- The computed arrow is independent of the tower, including every common refining
tower, and is invertible. Source: Stacks Tags 0F7I and 0F7J
(blueprint: lem-sp-finite-compact-site-coherence).
Proof: the preceding site equation has invertible C, the etale compositor and the
two source comparison factors. Solve for the computed arrow; its expression is
independent of T and invertible. Apply this to each of T and T'.
-/
theorem finiteCompactSite_tower_independence
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T T' : Compactification.Triangle f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    finiteCompactSiteCompositionPlus R c d e T E =
      finiteCompactSiteCompositionPlus R c d e T' E ∧
    IsIso (finiteCompactSiteCompositionPlus R c d e T E) := by
  sorry

/-- Both comparison squares are natural in the etale input.
Source: Stacks Tags 0F7I and 0F7J (blueprint: lem-sp-finite-compact-site-coherence).
Proof: the proper mate, open comparison, proper/open refinement and open adjunct
are natural by their dependency statements. Their compositors are natural. Compose
these identities, inserting and cancelling the witness isomorphisms, for each path.
-/
theorem finiteCompactSite_naturality
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) {b : Compactification f} (r : c.Refinement b)
    {E E' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    (a : E ⟶ E') :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) b).map
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map a) ≫
      (properTransportRefinementPlus R r E').inv =
    (properTransportRefinementPlus R r E).inv ≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).map
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map a) ∧
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).map
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map a)) ≫
      finiteCompactSiteCompositionPlus R c d e T E' =
    finiteCompactSiteCompositionPlus R c d e T E ≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) e).map
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map a) := by
  sorry

/-- Identity normalization for C.
Source: Stacks Tag 0F7K (blueprint: lem-sp-finite-compact-site-coherence).
Proof: the proper counit mate at the identity is normalized to the identity by
mate pasting. The open comparison at the identity is an invertible idempotent by
its composition law, hence the identity under the open unitors. Paste the two facts.
-/
theorem finiteCompactSite_identity
    (X : Scheme.{u}) [IsNoetherian X]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (compactSupportSiteComparisonPlus R (Compactification.ofIsProper (𝟙 X))).hom.app E ≫
      (finiteCompactSiteIdentityProPlus R X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) =
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.map
      (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).shriekOfIsProperIdIso X).hom.app E) := by
  sorry


/-- Refinement identity and transitivity for the computed proper/open arrows.
Source: Stacks Tags 0F7I and 0F7K (blueprint: lem-sp-finite-compact-site-coherence).
Proof: insert the site equation for each refinement. Etale refinement identities
and transitivity hold by lem-amb-etale-compact-comparisons. Cancel adjacent inverse
C factors. This also shows independence of two parallel proper refinement maps.
-/
theorem finiteCompactSite_refinement_coherence
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f) (r : c.Refinement d) (s : d.Refinement e)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (properTransportRefinementPlus R (Compactification.Refinement.id c) E).inv = 𝟙 _ ∧
    (properTransportRefinementPlus R s E).inv ≫
        (properTransportRefinementPlus R r E).inv =
      (properTransportRefinementPlus R (r.comp s) E).inv := by
  sorry

/-- Both composition unit laws, computed through any compatible towers. The target
compactifications are the supplied c, transported along the scheme identity laws.
Source: Stacks Tag 0F7K (blueprint: lem-sp-finite-compact-site-coherence).
Proof: substitute finiteCompactSiteCoherence, and use finiteCompactSite_identity.
The etale unit laws identify the remaining etale composition with its unitor.
Naturality of C moves that unitor across the comparison; cancel the source C.
Tower independence shows that these equations hold for every supplied tower.
-/
theorem finiteCompactSite_composition_units
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (T : Compactification.Triangle (𝟙 X) f)
    (S : Compactification.Triangle f (𝟙 Y))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    finiteCompactSiteCompositionPlus R (Compactification.ofIsProper (𝟙 X)) c
        (c.copy (Category.id_comp f)) T E =
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).map
        ((finiteCompactSiteIdentityProPlus R X).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ∧
    finiteCompactSiteCompositionPlus R c (Compactification.ofIsProper (𝟙 Y))
        (c.copy (Category.comp_id f)) S E =
      (finiteCompactSiteIdentityProPlus R Y).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) := by
  sorry

/-- Associativity of the independently computed compositions, including arbitrary
compactifications and towers. The inner pro-etale input retains the witness F_f^et E
via C_f(E); copy inserts the canonical associativity equality of scheme morphisms.
Source: Stacks Tag 0F7K (blueprint: lem-sp-finite-compact-site-coherence).
Proof: substitute the composition site equation twice into each parenthesization.
Naturality of C_h moves the inner comparison through the outer composition. Cancel
adjacent C inverses: both paths become C_hgf N(alpha_et_triple) times the inverse
of F_h F_g(C_f), F_h(C_g F_f), C_h(F_g F_f). Etale associativity identifies the two
triple maps. Tower independence permits all four towers to be chosen independently.
-/
theorem finiteCompactSite_associativity
    {X Y Z W : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian W]
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cfg : Compactification (f ≫ g)) (cgh : Compactification (g ≫ h))
    (cfgh : Compactification (f ≫ g ≫ h))
    (Tfg : Compactification.Triangle f g)
    (Tgh : Compactification.Triangle g h)
    (Tfgh : Compactification.Triangle (f ≫ g) h)
    (Tf_gh : Compactification.Triangle f (g ≫ h))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) e).map
        (finiteCompactSiteCompositionPlus R c d cfg Tfg E) ≫
      finiteCompactSiteCompositionPlus R cfg e (cfgh.copy (Category.assoc f g h)) Tfgh E =
    finiteCompactSiteCompositionAtWitness R d e cgh Tgh
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj E)
        _ ((compactSupportSiteComparisonPlus R c).app E) ≫
      finiteCompactSiteCompositionPlus R c cgh cfgh Tf_gh E := by
  sorry

end AlgebraicGeometry.ProEtale
