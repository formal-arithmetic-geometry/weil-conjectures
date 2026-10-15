/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# The canonical comparison for bounded below direct images

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
prop-weil-pbc-comparison-direct-image; Stacks Project, Tag 099R
(blueprint: prop-weil-pbc-comparison-direct-image).

The comparison is the existing derived base-change transformation of the canonical
underived mate. The three statements give invertibility, identity compatibility and
composition compatibility. Naturality in the complex is built into the transformation.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical derived composition identification on Etale sheaves, with the
injective-preservation instance supplied by the exact inverse-image adjunction.
Source: blueprint prop-weil-pbc-comparison-direct-image, final proof paragraph;
Stacks, Tag 099R (blueprint: prop-weil-pbc-comparison-direct-image). -/
noncomputable def etaleComparisonDirectImageCompIso (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ≅
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso'
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) g)
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- The canonical derived composition identification on ProEtale sheaves, with the
injective-preservation instance supplied by the exact inverse-image adjunction.
Source: blueprint prop-weil-pbc-comparison-direct-image, final proof paragraph;
Stacks, Tag 099R (blueprint: prop-weil-pbc-comparison-direct-image). -/
noncomputable def proEtaleComparisonDirectImageCompIso (Λ : Type (u + 1)) [Ring Λ]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus ≅
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso'
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g)
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- The canonical comparison for a quasi-compact quasi-separated morphism is invertible.
Source: blueprint prop-weil-pbc-comparison-direct-image; Stacks, Tag 099R
(blueprint: prop-weil-pbc-comparison-direct-image).

Proof: take the mate of the pulled-back etale counit using the pullback comparison.
Exact inverse images and bounded below injective representatives keep both sides in D+.
Localize on affine opens of the target; restriction preserves injectives on both sites.
On an affine ind-etale basis object W = lim W_i, apply derived cohomology continuity
first to W_i and then to U times_V W_i. Quasi-compactness and quasi-separatedness of the
morphism give qcqs stage schemes and affine transition maps. Fixing one index gives the
fixed-stage complexes required by continuity. Derived evaluation of direct image identifies
the middle groups. Global cohomology comparison and pro-etale restriction identify the
result with derived sections of the target. To check this is the specified map, represent
L by etale injectives I and resolve its comparison pullback by pro-etale injectives J.
Comparison pullbacks of injectives are section-acyclic on the basis, so the source section
complex computes derived sections. The comparison-sections formula expresses it as a
filtered colimit of sections of I; exact filtered colimits commute with cohomology. At each
finite stage the counit is identity on sections, so its restriction is precisely the map
used by continuity. Thus the specified mate induces the computed isomorphisms, and basis
derived detection proves it invertible. This follows the seven proof steps of the node. -/
theorem isIso_comparisonDirectImagePlus (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))) := by
  sorry

/-- Identity compatibility of the canonical derived comparison.
Source: blueprint prop-weil-pbc-comparison-direct-image, final proof paragraph
(blueprint: prop-weil-pbc-comparison-direct-image).

Proof: for the identity morphism the defining pulled-back counit mate is the identity
under the canonical identity identifications. The adjunction triangle identities cancel
the inserted unit and counit. Deriving preserves this equality by the universal property
of the bounded below right derived functor and its normalization on injective complexes. -/
theorem comparisonDirectImagePlus_id (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (U : Scheme.{u})
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange (𝟙 U) (ModuleCat.{u + 1} Λ))).app L ≫
      (Functor.rightDerivedFunctorPlusNatIso
        (lowerStarId (ModuleCat.{u + 1} Λ) U) ≪≫
          Functor.rightDerivedFunctorPlusIdIso _).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj L) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
      ((Functor.rightDerivedFunctorPlusNatIso
        (Etale.lowerStarId (ModuleCat.{u + 1} Λ) U) ≪≫
          Functor.rightDerivedFunctorPlusIdIso _).hom.app L) := by
  sorry

/-- Composition compatibility of the canonical derived comparison.
Source: blueprint prop-weil-pbc-comparison-direct-image, final proof paragraph
(blueprint: prop-weil-pbc-comparison-direct-image).

Proof: the counit of a composite adjunction is the composite of its two counits under
associativity. Substitute this into the defining mate formula. Pullback comparison
coherence identifies the two pullback paths, and the triangle identities cancel the
inserted unit-counit pairs. On bounded below injective representatives, direct images
preserve injectives because inverse images are exact. Thus the canonical derived
composition isomorphisms compute the same equality termwise; their universal-property
normalizations give the displayed formula. Naturality in L is already the naturality
of the derived base-change transformation. -/
theorem comparisonDirectImagePlus_comp (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {U V W : Scheme.{u}}
    (f : U ⟶ V) (g : V ⟶ W)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategoryPlus.map
      ((etaleComparisonDirectImageCompIso Λ f g).hom.app L) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (lowerStarComparisonUpperStarBaseChange (f ≫ g) (ModuleCat.{u + 1} Λ))).app L =
    (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ))).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))).app L) ≫
      (proEtaleComparisonDirectImageCompIso Λ f g).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj L) := by
  sorry

end AlgebraicGeometry.ProEtale
