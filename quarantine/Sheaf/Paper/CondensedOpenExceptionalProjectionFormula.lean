/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper

/-!
# The canonical open projection formula for condensed module objects

Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`,
Open immersions, sheaves; Derived version
(blueprint: lem-pd-condensed-open-exceptional-projection-formula).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Avoid expanding internal-Hom resolutions during tensor instance comparisons.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

/-- The unit, projection, naturality, transpose and symmetric clauses of the open projection
formula, expressed once for monoidal categories. The projection component is the existing
unit--tensorator--counit construction, with no extra map chosen.
Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`, Open immersions
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
def OpenProjectionFormulaClauses {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C] [MonoidalCategory D]
    {e : C ⥤ D} {r : D ⥤ C} [r.Monoidal] (adj : e ⊣ r)
    (βC : BraidedCategory C) (βD : BraidedCategory D) : Prop :=
  IsIso adj.unit ∧
  (∀ (K : C) (L : D), IsIso
    (((adj.projectionMap r (curriedTensor C) (curriedTensor D)
      (Functor.LaxMonoidal.μNatTrans r)).app K).app L)) ∧
  (∀ (K K' : C) (L L' : D) (a : K ⟶ K') (b : L ⟶ L'),
    e.map (a ⊗ₘ r.map b) ≫
        ((adj.projectionMap r (curriedTensor C) (curriedTensor D)
          (Functor.LaxMonoidal.μNatTrans r)).app K').app L' =
      ((adj.projectionMap r (curriedTensor C) (curriedTensor D)
        (Functor.LaxMonoidal.μNatTrans r)).app K).app L ≫ (e.map a ⊗ₘ b)) ∧
  (∀ (K : C) (L : D),
    adj.homEquiv _ _
        (((adj.projectionMap r (curriedTensor C) (curriedTensor D)
          (Functor.LaxMonoidal.μNatTrans r)).app K).app L) =
      adj.unit.app K ▷ r.obj L ≫ Functor.LaxMonoidal.μ r (e.obj K) L) ∧
  (∀ (K : C) (L : D),
    ((adj.projectionMap r (curriedTensor C) (curriedTensor D)
      (Functor.LaxMonoidal.μNatTrans r)).app K).app L =
    e.map (βC.braiding K (r.obj L)).hom ≫ adj.projectionFormulaMap L K ≫
      (βD.braiding L (e.obj K)).hom)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A named specialization of the published relative module tensor structure.
Source: blueprint main-20261015, relative tensor in the open projection formula
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
instance condensedModuleMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

/-- A named specialization of the published relative K-flat derived monoidal structure.
Source: blueprint main-20261015, relative derived tensor in the open projection formula
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
instance condensedModuleDerivedMonoidal (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  inferInstance

/-- The published canonical monoidal structure on the named total derived pullback.
Source: blueprint main-20261015, derived open projection formula, actual tensorator
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
instance moduleObjectDerivedPullbackMonoidal {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleObjectDerivedPullback Λ j).Monoidal :=
  monoidal_leftDerivedUpperStar Λ j

/-- The Koszul braiding on the specified relative K-flat derived tensor product.
Source: blueprint main-20261015, derived projection formula and its symmetric version
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
@[instance_reducible]
def condensedDerivedBraiding (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  DerivedCategory.braidedCategory' _

/-- The derived open adjunction, transported to the total derived module pullback using
its canonical identification with levelwise restriction.
Source: blueprint main-20261015, open-immersion projection formula
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
def condensedOpenDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⊣ moduleObjectDerivedPullback Λ j :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

/-- The actual unit--tensorator--counit composite for extension by zero and total derived
module pullback. The tensorator is the published derived pullback lax structure.
Source: blueprint main-20261015, open-immersion projection formula
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
def condensedOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (condensedOpenDerivedAdjunction Λ j).projectionMap
    (moduleObjectDerivedPullback Λ j) (derivedTensor Λ U) (derivedTensor Λ X)
    (Functor.LaxMonoidal.μNatTrans (moduleObjectDerivedPullback Λ j))

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The same unit--tensorator--counit construction inside the bounded constructible full
subcategories, for the specified algebraic-closure coefficient. Its adjunction is the
recorded restricted ambient adjunction and its tensorator is the restricted actual one.
Source: blueprint main-20261015, restriction of the open projection formula
(blueprint: lem-pd-condensed-open-exceptional-projection-formula). -/
def condensedQlbOpenProjection :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).projectionMap
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (curriedTensor _) (curriedTensor _)
    (Functor.LaxMonoidal.μNatTrans
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j))

/-- The unit and the canonical open projection component are invertible, naturally in both
arguments, with their stated adjoint and symmetric descriptions. The same actual component
restricts to an isomorphism for bounded constructible algebraic-closure coefficients.

Source: blueprint main-20261015, `det-lem-int-tensor-projection.proof.md`,
Open immersions, sheaves; Derived version
(blueprint: lem-pd-condensed-open-exceptional-projection-formula).

Proof: (1) Use lem-pd-module-ringed-topos-derived-comparison and lem-sfb-alpha-iso to
identify the exact open module functors and their adjunction with ringed-site restriction
and extension by zero. The abelian unit is invertible by full faithfulness of extension
by zero (sk-def-sfb-finite-lower-shriek). Its inverse is module-linear. Exact functor
factorization (lem-weil-pbc-exact-functor-derived-factorization) identifies the derived
unit with its termwise localization, hence it too is invertible.
(2) Apply lem-sfb-open-projection-formula to both arrows of the balanced coequalizer
of def-sfb-modobj-relative-tensor. Extension by zero preserves that coequalizer because
it is a left adjoint (lem-weil-pbc-left-adjoint-preserves-colimits). Both arrows impose
the same scalar relation after alpha. The resulting relative projection isomorphism is
the specified adjoint-of-unit map, as seen on the defining balanced bilinear maps.
(3) Apply this relative formula in each bidegree of two complexes. Extension by zero
preserves the direct sums in totalization. Naturality commutes with both differentials,
and additivity preserves the Koszul sign of def-pc-tensor-complex-sheaves. The inverse
bidegree maps give a chain inverse, including for unbounded complexes.
(4) Choose flat-term K-flat resolutions by lem-pc-kflat-resolution. Restriction preserves
K-flatness by lem-weil-pbc-ringed-pullback-preserves-kflat. Extension by zero preserves it
because its tensor with an acyclic complex is the extension of the tensor with its exact
restriction; it also preserves flat terms by the same underived projection formula.
Use def-pc-kflat-complex and def-pc-flat-sheaf-modules, transported through the comparison.
(5) The K-flat descent of lem-weil-pbc-site-derived-tensor-descent and
sk-def-sfb-derived-tensor-hom computes both derived tensors by these representatives.
The precise transformation clause of lem-pd-module-ringed-topos-derived-comparison
identifies the inverse comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback
with the actual lax tensorator. Thus the displayed composite is exactly the totalized
isomorphism from (3), and is invertible after localization.
(6) Naturality follows from that of the unit, tensorator and counit. The adjunction Hom
bijection gives the asserted transpose. Symmetry exchanges the two factors and their
unit maps, giving the projection map of def-sfb-adjunction-has-projection-formula.
(7) For sk-def-sfb-qlbar-condensed, the functors and tensor restrict by
sk-def-sfb-dc-restricted-functors. The adjunction of
def-sfb-dc-open-lower-shriek-adjunction is the restricted ambient one. Its unit, counit
and tensorator give the ambient composite. Fullness of sk-def-sfb-bounded-constructible
carries the inverse and both inverse identities into the subcategory. -/
theorem condensed_open_exceptional_projection_formula :
    (condensedOpenDerivedAdjunction Λ j.left).OpenProjectionFormulaClauses
      (condensedDerivedBraiding Λ U.left) (condensedDerivedBraiding Λ X.left) ∧
    IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).unit ∧
    (∀ (K : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))
        (L : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)),
      IsIso (((condensedQlbOpenProjection ℓ j).app K).app L)) ∧
    (∀ (K K' : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))
        (L L' : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
        (a : K ⟶ K') (b : L ⟶ L'),
      (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (a ⊗ₘ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map b) ≫
          ((condensedQlbOpenProjection ℓ j).app K').app L' =
        ((condensedQlbOpenProjection ℓ j).app K).app L ≫
          ((boundedConstructibleOpenImmersionLowerShriek
            (Profinite.padicAlgClRingObj ℓ) ℓ j).map a ⊗ₘ b)) ∧
    (∀ (K : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))
        (L : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)),
      (((condensedQlbOpenProjection ℓ j).app K).app L).hom =
        ((condensedOpenProjection (Profinite.padicAlgClRingObj ℓ) j.left).app K.obj).app
          L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
