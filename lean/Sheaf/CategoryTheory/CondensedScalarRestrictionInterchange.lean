/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.CondensedRestrictionMateNormalization
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Shift.CommShift
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.SixFunctors.RingedDerivedAdjointLift
import Sheaf.SixFunctors.RingedDerivedCompositionComparison
import Sheaf.SixFunctors.RingedDerivedTwoIsoComparison

/-! # Scalar conjugacy and group restriction for condensed derived invariants

Source: the current blueprint direct-images proof, paragraph (3), dense-lattice input;
the agent-formulated scalar/restriction interchange, proof steps 1--7; Stacks Project,
Cohomology on Sites, Tags 0D6D, 07A6, 0D6E, 0FPI
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).

The invariant functors, their computation units, scalar comparison and group restriction
are the existing normalized constructions. Scalar-extension adjoints are named parameters:
the statements are invariant under the unique adjunction-compatible changes of these models.
The left comparison is the scalar mate of the identity on underlying trivial actions.
The ringed composition comparisons give this same map by their K-flat normalization.

The computation-unit and shift assertions are already `scalarComparisonExist` and
`scalarComparisonShift` in `CondensedDerivedInvariants`. The coefficient-square equality
is already `coefficientSquare` in `CondensedDerivedRestrictionCalculus`; that downstream
module is not imported, since its proof uses this node. Here both transposes are specified.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Profinite.CondensedAction (trivial)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable {A A' : CondensedBar.Ring.{u}}
variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Scalar restriction and trivial inflation have the unique comparison whose underlying
module map is the identity under the specified scalar-action identification.
Source: paragraph (3), step 1
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).
Proof: both sides give the trivial action on the restricted module. The inverse of the
specified underlying-module comparison is equivariant because its source action is trivial
and scalarAction.action identifies its target action with that same action. These maps are
natural, are inverse to the underlying comparison, and are uniquely fixed by faithfulness. -/
theorem scalarTrivialExist (a : A ⟶ A') :
    ∃! e : Mod.comap a.hom.hom ⋙ trivial (R := A.toMon) (P := G) ≅
        trivial (R := A'.toMon) (P := G) ⋙ (scalarAction a).functor,
      ∀ M : Modules A', (e.hom.app M).val ≫
        (scalarAction a).underlying.hom.app ((trivial (R := A'.toMon) (P := G)).obj M) =
          𝟙 ((Mod.comap a.hom.hom).obj M) := by
  sorry

/-- The scalar/trivial-action identity, determined uniquely by its underlying module maps.
Source: paragraph (3), step 1
(blueprint: lem-sfb-condensed-scalar-restriction-interchange). -/
def scalarTrivial (a : A ⟶ A') :
    Mod.comap a.hom.hom ⋙ trivial (R := A.toMon) (P := G) ≅
      trivial (R := A'.toMon) (P := G) ⋙ (scalarAction a).functor :=
  Classical.choose (scalarTrivialExist (G := G) a)

/-- Localization of the identity scalar/trivial-action comparison, with the canonical
composition comparisons for exact termwise functors.
Source: paragraph (3), steps 1 and 4
(blueprint: lem-sfb-condensed-scalar-restriction-interchange). -/
def scalarTrivialDerived (a : A ⟶ A') :
    scalarBase a ⋙ trivialDerived A G ≅ trivialDerived A' G ⋙ scalarDerived a G :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (scalarTrivial a) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The scalar-adjunction mate of the exact underlying identity. This is the balancing
comparison E_G L_G → L'_G E_0, expressed without choosing representatives or a new map.
Source: paragraph (3), steps 2 and 4; Stacks 0D6D
(blueprint: lem-sfb-condensed-scalar-restriction-interchange). -/
def scalarPullbackComparison (a : A ⟶ A')
    {E₀ : DerivedCategory.{u + 1} (Modules A) ⥤ DerivedCategory.{u + 1} (Modules A')}
    {E : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A' G)}
    (e₀ : E₀ ⊣ scalarBase a) (e : E ⊣ scalarDerived a G) :
    trivialDerived A G ⋙ E ⟶ E₀ ⋙ trivialDerived A' G :=
  ((mateEquiv e₀ e).symm
    (TwoSquare.mk _ _ _ _ (scalarTrivialDerived (G := G) a).hom)).natTrans

/-- The scalar mate is invertible: it is the pullback comparison obtained by composing the
two paths in the coefficient/action ringed square with its identity geometric comparison.
Source: paragraph (3), step 2; Stacks 0D6D
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).
Proof: realize trivial inflation as module pullback along the action-topos projection.
The two coefficient paths have identical structural maps on underlying sheaves. Apply
lem-sfb-ringed-derived-monoidal-comparisons to obtain their invertible comparison. On
flat-term K-flat representatives, lem-sfb-kflat-scalar-comparison-normalization identifies
it with the scalar-adjunction mate above: both preserve insertion x ↦ 1 ⊗ x. Every complex
has a flat-term K-flat resolution (lem-pc-kflat-resolution); naturality identifies the maps
on all derived objects. Neither coefficient flatness nor injective preservation is used. -/
theorem scalarPullbackComparison_isIso (a : A ⟶ A')
    {E₀ : DerivedCategory.{u + 1} (Modules A) ⥤ DerivedCategory.{u + 1} (Modules A')}
    {E : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A' G)}
    (e₀ : E₀ ⊣ scalarBase a) (e : E ⊣ scalarDerived a G) :
    IsIso (scalarPullbackComparison a e₀ e) := by
  sorry

/-- The specified pullback isomorphism, using the preceding invertibility theorem only
for its proof field; its forward map is the explicit scalar mate.
Source: paragraph (3), step 2
(blueprint: lem-sfb-condensed-scalar-restriction-interchange). -/
def scalarPullbackIso (a : A ⟶ A')
    {E₀ : DerivedCategory.{u + 1} (Modules A) ⥤ DerivedCategory.{u + 1} (Modules A')}
    {E : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A' G)}
    (e₀ : E₀ ⊣ scalarBase a) (e : E ⊣ scalarDerived a G) :
    trivialDerived A G ⋙ E ≅ E₀ ⋙ trivialDerived A' G :=
  haveI := scalarPullbackComparison_isIso a e₀ e
  asIso (scalarPullbackComparison a e₀ e)

/-- The conjugate of the derived pullback comparison is precisely the existing
computation-unit-normalized scalar/invariants isomorphism.
Source: paragraph (3), steps 2--3; Stacks 07A6, 0D6E, 0FPI
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).
Proof: conjugate the two normalized ringed composition comparisons and the identity
geometric comparison. Their right-derived-unit equations show that their quotient obeys
scalarComparisonExist's equation on every complex, with scalarInvariants as its ordinary
right comparison. The latter is the fixed-section identity, including its inclusion.
Uniqueness in scalarComparisonExist identifies the conjugate with scalarComparison.
Conjugation of the inverse gives its inverse; no preservation of injectives is assumed. -/
theorem scalarComparison_conjugate (a : A ⟶ A')
    {E₀ : DerivedCategory.{u + 1} (Modules A) ⥤ DerivedCategory.{u + 1} (Modules A')}
    {E : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A' G)}
    (e₀ : E₀ ⊣ scalarBase a) (e : E ⊣ scalarDerived a G) :
    conjugateIsoEquiv ((adjunction A G).comp e) (e₀.comp (adjunction A' G))
      (scalarPullbackIso a e₀ e).symm = scalarComparison (G := G) a := by
  sorry

/-- The inverse transpose through the composite scalar/invariants adjunction bijection,
written using the exact identity comparison and the primed counit.
Source: paragraph (3), step 4
(blueprint: lem-sfb-condensed-scalar-restriction-interchange). -/
def scalarInvariantTranspose (a : A ⟶ A')
    {X : DerivedCategory.{u + 1} (Modules A)}
    {Y : DerivedCategory.{u + 1} (Equivariant A' G)}
    (z : X ⟶ (scalarBase a).obj ((derived A' G).obj Y)) :
    (trivialDerived A G).obj X ⟶ (scalarDerived a G).obj Y :=
  (trivialDerived A G).map z ≫
    (scalarTrivialDerived a).hom.app ((derived A' G).obj Y) ≫
    (scalarDerived a G).map ((adjunction A' G).counit.app Y)

/-- This explicit transpose is the composite Hom bijection, using the pullback comparison
and both scalar-extension adjunctions in the direction specified in the node.
Source: paragraph (3), step 4
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).
Proof: first transpose z across E₀ ⊣ s₀, then across L'_G ⊣ F'_G, precompose with the
pullback comparison, then transpose back across E_G ⊣ s_G. The scalar-mate equation and
the adjunction triangle identities reduce the result to chi followed by s_G(epsilon'). -/
theorem scalarInvariantTranspose_composite (a : A ⟶ A')
    {E₀ : DerivedCategory.{u + 1} (Modules A) ⥤ DerivedCategory.{u + 1} (Modules A')}
    {E : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Equivariant A' G)}
    (e₀ : E₀ ⊣ scalarBase a) (e : E ⊣ scalarDerived a G)
    (X : DerivedCategory.{u + 1} (Modules A))
    (Y : DerivedCategory.{u + 1} (Equivariant A' G))
    (z : X ⟶ (scalarBase a).obj ((derived A' G).obj Y)) :
    scalarInvariantTranspose a z =
      e.homEquiv ((trivialDerived A G).obj X) Y
        ((scalarPullbackIso a e₀ e).hom.app X ≫
          ((adjunction A' G).homEquiv (E₀.obj X) Y).symm
            ((e₀.homEquiv X ((derived A' G).obj Y)).symm z)) := by
  sorry

/-- Both coefficient/restriction composites have the specified common transpose as actual
derived arrows. The exact-localization identity comparisons are retained explicitly.
Source: paragraph (3), steps 6--7
(blueprint: lem-sfb-condensed-scalar-restriction-interchange).
Proof: step 4 gives tau L(d) = epsilon. For the first composite substitute this equation,
use counit naturality for Uf and groupMap_mate over A. For the second use naturality of
chi, groupMap_mate over A', scalarGroupDerived, and restrictionTrivialDerived. Their
underlying identity components identify chi_H with U chi_G. Apply tau L(d) = epsilon
again, then counit naturality. Both results are U(epsilon_G);U(f), with the displayed
identity transports. The composite Hom bijection is injective, yielding coefficientSquare
before applying homology, with no boundedness or coefficient-flatness restriction. -/
theorem scalarRestrictionInterchange_transposes (a : A ⟶ A') (v : H →ₜ* G)
    (N : DerivedCategory.{u + 1} (Equivariant A G))
    (N' : DerivedCategory.{u + 1} (Equivariant A' G))
    (f : N ⟶ (scalarDerived a G).obj N') :
    scalarInvariantTranspose a
        ((groupMap A v).app N ≫ coefficientMap a
          ((groupDerived A v).map f ≫ (scalarGroupDerived a v).hom.app N')) =
      (restrictionTrivialDerived A v).hom.app ((derived A G).obj N) ≫
        (groupDerived A v).map ((adjunction A G).counit.app N) ≫
        (groupDerived A v).map f ≫ (scalarGroupDerived a v).hom.app N' ∧
    scalarInvariantTranspose a
        (coefficientMap a f ≫ (scalarBase a).map ((groupMap A' v).app N')) =
      (restrictionTrivialDerived A v).hom.app ((derived A G).obj N) ≫
        (groupDerived A v).map ((adjunction A G).counit.app N) ≫
        (groupDerived A v).map f ≫ (scalarGroupDerived a v).hom.app N' := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
