/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.OrientedConstructibleSheafVanishing
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.CategoryTheory.Sites.CoherentConservativeReflection
import Sheaf.Paper.QcqsOrientedTriplePresentation
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.Sites.CoherentToposRepair
import Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.StratifiedOrientedCover

/-!
# Coherent set sheaves on a vanishing topos

Source: Orgogozo, Modifications et cycles proches sur une base générale,
author draft §8.1, printed pp. 17--18; ILO Exposé XI §§1.1--1.7 and 1.9
(blueprint: lem-trf-coherent-set-criterion).

The input is the recorded `VanishingTopos`. Its concrete identity-base-change
normalization is used before restricting to the two stratum factors. Local constancy is
expressed on all
site objects by covering sieves and the usual slice restrictions `Sheaf.over`.
This is equivalent to a covering family of the final topos object with finite
constant models: associated representables generate and refine every such cover.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OrientedConstructibleSheaf AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry

/-- Standard set-sheaf coproducts, using the given sheafification adjunction directly.
This supplies exactly Mathlib's sheafified presheaf colimits, avoiding recursive
instance search through forgetful functors.
Source: ILO XI §1.1 (blueprint: lem-trf-coherent-set-criterion). -/
instance coherentSetCriterion_hasCoproducts
    {X S : Scheme.{u}} (f : X ⟶ S) :
    HasCoproducts.{max (u + 1) v} (VanishingTopos.{u, v} f) :=
  fun _ ↦ @Sheaf.instHasColimitsOfShape _ _ _ _ _ _ _
    HasSheafify.isRightAdjoint inferInstance

/-- The canonical inverse image on set sheaves for a pair of scheme maps.
It first applies the recorded normalization to the general product presentation,
then sheafified left Kan extension along the already defined componentwise base
change of triples. Its two projections are the scheme pullbacks and its
orientation is inherited from the unchanged middle coordinate; thus this is the
map specified by the oriented-product universal property, not an arbitrary map.
Source: ILO XI §1.6 formula (1.a), §1.9
(blueprint: lem-trf-coherent-set-criterion). -/
def orientedStratumSetRestriction {X' S' X S : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    VanishingTopos.{u, v} f ⥤
      Sheaf (productTopology.{u, v} (i ≫ f) (j ≫ 𝟙 S)) (Type (max (u + 1) v)) :=
  sheafToPresheaf (vanishingTopology f) (Type (max (u + 1) v)) ⋙
    (Functor.whiskeringLeft _ _ _).obj (vanishingNormalization f).op ⋙
    (stratumBaseChange.{u, v} f (𝟙 S) i j).op.lan ⋙
    presheafToSheaf (productTopology (i ≫ f) (j ≫ 𝟙 S)) (Type (max (u + 1) v))

/-- Coherence is equivalent to finite local constancy on products of constructible strata.
The constant models are finite sets, and all slice isomorphisms are actual sheaf
isomorphisms on the same localized site.

Source: Orgogozo, author draft §8.1, printed pp. 17--18
(blueprint: lem-trf-coherent-set-criterion).

Proof plan:
1. Finite presentation over the Noetherian base makes X and S qcqs and Noetherian
   (lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-locally-noetherian-quasi-separated). The finite-cover triple site
   (lem-trf-qcqs-oriented-triple-presentation) and
   lem-trf-finitary-site-coherent-generators make the vanishing topos coherent.
2. For coherent A choose a finite coherent-generator cover F → A and a finite
   generator cover G of its kernel pair R. Stratify every coordinate of the triples
   in both F and G by lem-weil-pbc-etale-stratified-finite and take common refinements.
   The oriented-product pullback formula (lem-trf-oriented-product-universal)
   identifies the restricted generators with finite limits of finite locally constant
   sheaves represented by finite étale schemes (lem-galois-flc-representable).
   Finite limits, coproducts, images and quotients by finite locally constant relations
   preserve finite local constancy (lem-trf-finite-locally-constant-coherent).
   Since inverse image is exact and preserves colimits, A = F/R has the required models.
3. Conversely, the finite coproduct of stratum products gives a coherent conservative
   morphism (lem-trf-stratified-product-coherent-conservative). Each stratum product
   is coherent by the same finite-site criterion. Finite local constancy makes the
   restricted sheaves coherent (lem-trf-finite-locally-constant-coherent), after taking
   finite subcovers of the terminal objects. Apply lem-trf-coherent-conservative-reflection
   to obtain coherence of A. Covers by associated representables give precisely the
   covering-sieve formulation used below, including on the empty topos. -/
theorem coherent_iff_finite_constructible_strata
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [CompactSpace S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (A : VanishingTopos.{u, v} f) :
    IsCoherentObject.{max (u + 1) v} A ↔
      ∃ (SX : Scheme.FiniteLocallyClosedStratification X)
        (SS : Scheme.FiniteLocallyClosedStratification S),
        (∀ i : Fin SX.n, Topology.IsConstructible (SX.stratum i)) ∧
        (∀ j : Fin SS.n, Topology.IsConstructible (SS.stratum j)) ∧
        ∀ (i : Fin SX.n) (j : Fin SS.n)
          (U : ProductSite.{u, v} (SX.immersion i ≫ f) (SS.immersion j ≫ 𝟙 S)),
          ∃ R : Sieve U,
            R ∈ productTopology (SX.immersion i ≫ f) (SS.immersion j ≫ 𝟙 S) U ∧
            ∀ (V : ProductSite.{u, v} (SX.immersion i ≫ f) (SS.immersion j ≫ 𝟙 S))
              (r : V ⟶ U), R r →
              ∃ (M : Type (max (u + 1) v)), Finite M ∧
                Nonempty
                  (((orientedStratumSetRestriction f
                    (SX.immersion i) (SS.immersion j)).obj A).over V ≅
                    ((constantSheaf
                      (productTopology (SX.immersion i ≫ f) (SS.immersion j ≫ 𝟙 S))
                      (Type (max (u + 1) v))).obj M).over V) := by
  sorry

end AlgebraicGeometry
