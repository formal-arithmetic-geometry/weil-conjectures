/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.OrientedConstructibleSetSheaf
public import Sheaf.CategoryTheory.Sites.ToposComplementFactorization
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.TraceFormula.EtaleClosedComplementSets
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.OrientedNearbyCycles

/-!
# Closed base restriction of an oriented vanishing topos

Source: Orgogozo, Modifications et cycles proches sur une base generale, author draft,
Lemma 8.3.1 and Section 8.1, printed pp. 17--19; ILO XI Theorem 1.4 and Section 1.9
(blueprint: lem-trf-oriented-closed-base-restriction).

The two maps are specified on triple sites by actual scheme base change. The set-valued
constructibility clause is the set version of the recorded finite rectangle definition.
The module clause uses the recorded module definition and its vanishing-site transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AdicSites
open AlgebraicGeometry.OrientedNearbyCycles AlgebraicGeometry.OrientedConstructibleSheaf

namespace AlgebraicGeometry.OrientedClosedBaseRestriction

/-- The existing oriented triple site as a small-site datum, with no new topology.
Source: ILO XI Section 1.1 (blueprint: lem-trf-oriented-closed-base-restriction). -/
def productDatum {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Site.{max (u + 1) v} := ⟨ProductSite.{u, v} f g, productTopology f g⟩

/-- Change the second outer entry of a vanishing triple by base change along k.
The first and middle entries stay fixed. The structural arrows retain their orientation.
Source: ILO XI Section 1.9 (blueprint: lem-trf-oriented-closed-base-restriction). -/
def restrictionSite {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :
    VanishingSite.{u, v} f ⥤ ProductSite.{u, v} f k :=
  Comma.map
    (F₁ := (𝟭 (EtaleSite.{u, v} X)).prod (etaleBaseChange k))
    (F₂ := 𝟭 (EtaleSite.{u, v} S))
    (F := (𝟭 (EtaleSite.{u, v} X)).prod (etaleBaseChange k))
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    { app := fun _ ↦ (𝟙 _, 𝟙 _)
      naturality := fun _ _ _ ↦ Prod.ext (by simp) (by simp) }

/-- The canonical fibre-product comparison on the first structural arrow of a triple.
Source: ILO XI Section 1.9 (blueprint: lem-trf-oriented-closed-base-restriction). -/
def comparisonBeta {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :
    (etaleBaseChange.{u, v} f).prod' (etaleBaseChange k) ⋙
        (etaleBaseChange (pullback.fst f k)).prod (𝟭 (EtaleSite T)) ⟶
      etaleBaseChange k ⋙ (etaleBaseChange (pullback.snd f k)).prod'
        (𝟭 (EtaleSite T)) :=
  NatTrans.prod'
    ((etaleBaseChangeComp (pullback.fst f k) f).inv ≫
      eqToHom (congrArg (fun a ↦ etaleBaseChange.{u, v} a) (pullback.condition (f := f) (g := k))) ≫
      (etaleBaseChangeComp (pullback.snd f k) k).hom)
    ((Functor.rightUnitor _).hom ≫ (Functor.rightUnitor _).inv)

/-- Pull back the first entry to X times_S T and the middle entry to T; retain the
second entry. The fibre-product comparison gives the new first structural arrow.
Source: Orgogozo Lemma 8.3.1; ILO XI Section 1.9
(blueprint: lem-trf-oriented-closed-base-restriction). -/
def comparisonSite {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :
    ProductSite.{u, v} f k ⥤ VanishingSite.{u, v} (pullback.snd f k) :=
  Comma.map
    (F₁ := (etaleBaseChange (pullback.fst f k)).prod (𝟭 (EtaleSite.{u, v} T)))
    (F₂ := etaleBaseChange k)
    (F := (etaleBaseChange (pullback.fst f k)).prod (𝟭 (EtaleSite.{u, v} T)))
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv) (comparisonBeta f k)

/-- Both specified triple functors are continuous and preserve finite limits.
Source: ILO XI Sections 1.1, 1.9 (blueprint: lem-trf-oriented-closed-base-restriction).
Proof: compute limits in each of the three entries. Scheme base change preserves
finite limits and the displayed associativity comparisons identify the structural arrows.
Types (a) and (b) of covering generators remain etale covers after base change. Type (c)
remains cartesian, so it is again a type-(c) generator. This proves continuity for the
generated topologies. On first, second and middle triples these are exactly the maps
specified by the oriented universal property lem-trf-oriented-product-universal. -/
theorem site_properties {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :
    HasFiniteLimits (VanishingSite.{u, v} f) ∧
    HasFiniteLimits (ProductSite.{u, v} f k) ∧
    (restrictionSite.{u, v} f k).IsContinuous (vanishingTopology f) (productTopology f k) ∧
    PreservesFiniteLimits (restrictionSite.{u, v} f k) ∧
    (comparisonSite.{u, v} f k).IsContinuous (productTopology f k)
      (vanishingTopology (pullback.snd f k)) ∧
    PreservesFiniteLimits (comparisonSite.{u, v} f k) := by
  sorry

/-- The actual canonical morphism E_T to V_f, from its specified triple functor.
Source: ILO XI Section 1.9 (blueprint: lem-trf-oriented-closed-base-restriction). -/
def restriction {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :=
  letI := (site_properties.{u, v} f k).1
  letI := (site_properties.{u, v} f k).2.2.1
  letI := (site_properties.{u, v} f k).2.2.2.1
  siteMorphism (vanishingTopology.{u, v} f) (productTopology f k) (restrictionSite f k)

/-- The actual canonical morphism V_(f_T) to E_T, from its specified triple functor.
Source: Orgogozo Lemma 8.3.1 (blueprint: lem-trf-oriented-closed-base-restriction). -/
def comparison {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) :=
  letI := (site_properties.{u, v} f k).2.1
  letI := (site_properties.{u, v} f k).2.2.2.2.1
  letI := (site_properties.{u, v} f k).2.2.2.2.2
  siteMorphism (productTopology.{u, v} f k) (vanishingTopology (pullback.snd f k))
    (comparisonSite f k)

/-- Canonical inverse image to E_T on modules, followed by the recorded identification
of the commutative-constant-ring presentation with the RingCat presentation.
Source: Stacks 03CY; ILO XI Section 1.9
(blueprint: lem-trf-oriented-closed-base-restriction). -/
def restrictionModules {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S)
    (Λ : Type v) [CommRing Λ] :
    (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ) ⥤ Modules f k Λ :=
  (moduleMorphism (vanishingDatum f) (productDatum f k)
    (restriction f k)).modulePull (Coeff Λ) ⋙
    SheafOfModules.restrictScalars (realizationRingIso (productTopology f k) (Coeff Λ)).inv

/-- Canonical module inverse image by V_(f_T) to E_T, with the inverse coefficient
identification on its source. No arbitrary functor or scalar action is chosen.
Source: Stacks 03CY; ILO XI Section 1.9
(blueprint: lem-trf-oriented-closed-base-restriction). -/
def comparisonModules {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S)
    (Λ : Type v) [CommRing Λ] :
    Modules f k Λ ⥤ (vanishingDatum.{u, v} (pullback.snd f k)).modules (Coeff.{u, v} Λ) :=
  SheafOfModules.restrictScalars (realizationRingIso (productTopology f k) (Coeff Λ)).hom ⋙
    (moduleMorphism (productDatum f k) (vanishingDatum (pullback.snd f k))
      (comparison f k)).modulePull (Coeff Λ)

/-- The assertions to be applied to X and to every closed subscheme Z of X. The essential
image clause says that the actual r is the closed complement of p2 inverse image of S minus T.
Source: Orgogozo Sections 8.1, 8.3; Stacks 08LY
(blueprint: lem-trf-oriented-closed-base-restriction). -/
def Assertions {X T S : Scheme.{u}} (f : X ⟶ S) (k : T ⟶ S) [IsClosedImmersion k] : Prop :=
  Nonempty (restriction.{u, v} f k).direct.FullyFaithful ∧
  (∀ F : VanishingTopos.{u, v} f,
    (restriction f k).direct.essImage F ↔
      closedComplementObjects
        ((p₂ f).inverse.obj ((OrientedProduct.associated (etaleTopology S)).obj
          (AsSmall.up.obj (Scheme.Etale.mk k.openComplement.ι)))) F) ∧
  (comparison.{u, v} f k).inverse.IsEquivalence ∧
  (∀ F : Sheaf (productTopology.{u, v} f k) (Type (max (u + 1) v)),
    IsConstructibleSet f k F ↔
      IsConstructibleVanishingSet (pullback.snd f k) ((comparison f k).inverse.obj F)) ∧
  (∀ F : VanishingTopos.{u, v} f, IsConstructibleVanishingSet f F →
    IsConstructibleSet f k ((restriction f k).inverse.obj F)) ∧
  ∀ (Λ : Type v) [CommRing Λ] [Finite Λ],
    (comparisonModules f k Λ).IsEquivalence ∧
    (∀ F : Modules f k Λ, IsConstructible f k Λ F ↔
      IsConstructibleVanishing (pullback.snd f k) Λ ((comparisonModules f k Λ).obj F)) ∧
    (∀ F : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ),
      IsConstructibleVanishing f Λ F →
        IsConstructible f k Λ ((restrictionModules f k Λ).obj F))

/-- Closed-base restriction, including its finite-set and finite-module constructibility
clauses and the identical assertions after replacing X by any closed subscheme.
Source: Orgogozo Lemma 8.3.1, Section 8.1 and proof of Lemma 8.3.3, printed pp. 17--19;
ILO XI Theorem 1.4 and Section 1.9 (blueprint: lem-trf-oriented-closed-base-restriction).

Proof (the twelve steps of the DAG node):
1. For U = S minus T, adjunction, etale representability and Yoneda identify f inverse h_U
with h_(X times_S U), and k inverse h_U with the initial sheaf. The empty covering proves
h_empty initial. Closed base change and lem-trf-oriented-closed-base-localization identify
the two etale closed complements.
2. The oriented universal property identifies restriction with the closed complement of
p2 inverse h_U: a universal triple factors exactly when its second projection kills h_U.
3. More generally allow Y to T. The orientation's inverse-image mate maps the first
projection's inverse image of h_(X times_S U) to zero. Strictness of the initial sheaf
(lem-trf-set-sheaf-finite-extensivity) forces this object initial. Closed localization
therefore factors the first projection uniquely through X_T, including 2-morphisms.
4. Full faithfulness of k direct (lem-trf-etale-closed-complement-sets) lifts the oriented
arrow uniquely over T. The oriented universal property gives the inverse comparison.
5. The two composites have the original projections and orientation: factorization
uniqueness and faithfulness of k direct identify their arrows. Universal uniqueness gives
both inverse isomorphisms. Applying the equivalence to algebraic operations and using
lem-pe-constant-left-module-inverse-image gives the constant-module equivalence.
6. For restrictions A to X and B to Y, both composite maps have the same first and second
projections and the same oriented arrow. Universal uniqueness gives coherent rectangle
comparison isomorphisms, also for locally closed immersions.
7. Geometric inverse images preserve trivializing covers, terminal objects and finite
constant models. Constants are coproducts of terminal objects; module constants use
lem-sfb-geometric-inverse-image-constant-module. An inverse equivalence reflects these.
8. Finite presentation over Noetherian S makes X Noetherian. Closed subspaces T and X_T
are Noetherian. All locally closed strata are constructible; pullback preserves finite
locally closed partitions. A stratum in X_T is a locally closed stratum in X.
9. Pull X strata back to X_T and retain T strata. Steps 3--7 identify the rectangle
restrictions and their finite local models, proving preservation along comparison.
10. Conversely extend X_T strata to X and adjoin X minus X_T. On each old stratum,
base change to T is an isomorphism. The added complement rectangles are degenerate:
the structural mate maps terminal to initial, so every sheaf has the unique local model.
11. For restriction itself, pull S strata back to T. Universal uniqueness identifies
each restricted rectangle with the inverse image from its original V_f rectangle.
Step 7 preserves finite local models. This proves preservation for the actual r.
12. Repeat for Z closed in X: Z and Z_T have Noetherian spaces by closedness. Steps 1--7
need no finite-presentation hypothesis; steps 8--11 use only these Noetherian spaces.
Identity and empty closed subschemes, empty rectangles and zero modules are included. -/
theorem orientedClosedBaseRestriction
    {X T S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (k : T ⟶ S) [IsClosedImmersion k] :
    Assertions.{u, v} f k ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i], Assertions.{u, v} (i ≫ f) k := by
  sorry

end AlgebraicGeometry.OrientedClosedBaseRestriction
