/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.ProEtaleClosedTensorProjection
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CoefficientHeartFiltration
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.CategoryTheory.WeakSerreBoundedThick
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.ContinuousQbarConstructibleGenerators
import Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles
import Sheaf.Paper.CoefficientHeartOrderedRefinement
import Sheaf.Paper.CoefficientHeartLisseRestriction
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Constructible comparison for the two algebraic-closure coefficient topologies

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
proper coefficient-change obligation
(blueprint: lem-sfb-constructible-algcl-topology-comparison).

The finite-subextension-valued coefficient and the full norm-continuous coefficient
are kept distinct. The map is their sectionwise inclusion. Scalar extension is the
existing total left derived functor, computed on K-flat resolutions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Inclusion of finite-subextension-valued continuous sections into all continuous
sections, as a map of condensed rings. Source: direct-image stability proof (3),
the coefficient-topology obligation's displayed c
(blueprint: lem-sfb-constructible-algcl-topology-comparison). -/
def algClTopologyInclusionRing (ℓ : ℕ) [Fact ℓ.Prime] :
    Profinite.padicAlgClCondensedRing.{u} ℓ ⟶
      Profinite.continuousMapRingSheaf (PadicAlgCl ℓ) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop).subtype.comp
          ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same canonical inclusion on the underlying abelian sheaves, with their
existing ring-object structures. Source: direct-image stability proof (3), c
(blueprint: lem-sfb-constructible-algcl-topology-comparison). -/
abbrev algClTopologyInclusion (ℓ : ℕ) [Fact ℓ.Prime] :
    Profinite.padicAlgClRingObj.{u} ℓ ⟶
      Profinite.continuousMapRingObj (PadicAlgCl ℓ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (algClTopologyInclusionRing ℓ)

/-- The specified ordinary unbounded derived scalar-extension functor along
p_X^*c. Source: direct-image stability proof (3), J_X
(blueprint: lem-sfb-constructible-algcl-topology-comparison). -/
abbrev algClTopologyScalarExtension (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap (algClTopologyInclusion ℓ) X)).leftDerivedFunctor

/-- Derived scalar extension restricts to an equivalence of the full bounded
constant-model constructible subcategories. Both subcategories inherit their ambient
triangulations, and the scalar functor is triangulated. Thus the restricted equivalence
is exact for those inherited structures. The chosen algebraic closure is PadicAlgCl.

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
proper coefficient-change obligation
(blueprint: lem-sfb-constructible-algcl-topology-comparison).

Proof plan, following the ten steps of the node:
1. Finite type over the field makes X Noetherian. Its locally closed strata remain
separated and finite type. The module/ringed-topos comparison identifies internal
relative tensor with sheaf-module tensor. Derived change of rings is triangulated;
its right adjoint is exact termwise restriction, with the scalar-insertion unit.
2. On a trivializing cover, K-flat scalar extension sends a finite free rank-r module
to the same rank-r module over the new ring, including r=0. The normalized inverse-
image comparison descends this calculation. The open and closed projection formulas
identify scalar extension of a_!L with a_! of its scalar extension.
3. The finite-subextension two-colimit descends every source object to a finite field.
Module devissage and the coefficient-heart common stratification and filtration
express it by finitely many shifts and triangles of supported finite-stage lisse
objects. Heart short exact sequences give triangles. The weak-Serre bounded-thick
lemma supplies the inherited source triangulation.
4. The all-continuous constructible-generator lemma gives the inherited target
triangulation. Step 2 sends each source generator to a target generator; step 3
then proves constructible preservation and exactness of the restricted functor.
5. For two supported finite-stage generators, the scalar-unit defect lemma kills
Hom into every shift of the unit's cone. Hom-into-triangle exactness makes the
unit induce Hom bijections. The normalized scalar adjunction identifies these
bijections with the actual functor on morphisms, by naturality of the unit.
6. For each generator, the five lemma and Hom-into-triangle sequences extend these
bijections in the second variable through all finite constructions. Repeat with
Hom-out-of-triangle sequences in the first variable. This gives full faithfulness.
7. Stratified finite models for an all-continuous constructible sheaf give finite-
field models on strata. Pass to an ordered common refinement. The actual fibre
product with the old stratum is a surjective closed immersion; the condensed
pullback equivalence lifts the model to the refined stratum. No factorization
of that stratum through the old one is assumed.
8. Extend these finite-field models to the source coefficient. Step 2 identifies
their supported extensions after scalar change. Recollement gives a finite
filtration of the target sheaf by these supported pieces. Its short exact
sequences give triangles, so step 9 lifts the whole sheaf.
9. Fullness lifts a morphism between image objects to the source. Exactness maps
its source cone to a target cone. TR3 and the Hom five lemma make any two such
cones isomorphic, so the essential image is closed under triangle extensions.
10. Bounded module devissage now lifts every target complex. Together with steps
4 and 6 this gives the stated equivalence; its inverse is exact by the same
cone argument. Empty schemes, rank zero, zero modules and acyclic complexes
start the finite constructions at zero. No flatness or completeness of c is used. -/
theorem constructible_algCl_topology_comparison
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] :
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left
      ).IsTriangulated ∧
    (constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left).IsTriangulated ∧
    ∃ h : ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ℓ) X.left,
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left
          ((algClTopologyScalarExtension ℓ X.left).obj K.obj),
      ((constantModelBoundedConstructible
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left).lift
          ((constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left).ι ⋙
            algClTopologyScalarExtension ℓ X.left) h).IsEquivalence ∧
      ∃ s : (algClTopologyScalarExtension ℓ X.left).CommShift ℤ,
        @Functor.IsTriangulated _ _ _ _ _ _ (algClTopologyScalarExtension ℓ X.left)
          s _ _ _ _ _ _ _ _ := by
  sorry

end AlgebraicGeometry.ProEtale
