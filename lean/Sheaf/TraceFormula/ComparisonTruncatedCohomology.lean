/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.DerivedAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.DerivedCategory.ShiftIdentification
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Cohomology comparison through a vanishing bound

Source: Stacks Project, Cohomology on Sites, Tag 0EZB,
`lemma-V-implies-cohomology-general`, and section-compare-general
(blueprint: lem-trf-comparison-truncated-cohomology).

The identity-site pullback is Mathlib's canonical left adjoint. It is canonically
finer sheafification, by uniqueness of the sheafification adjunction. No arbitrary
comparison map or choice of a cohomology isomorphism is an input.

## Main definitions and statements

* `comparisonDerivedSections`: derived sections of the canonical adjunction unit.
* `comparisonHypercohomology`: its natural transformation on cohomology.
* `comparisonTruncatedCohomology`: invertibility through the given vanishing bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- The identity is continuous from the coarser site to the finer site.
Source: Stacks, section-compare (blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityContinuousOfLE {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [h : Fact (K ≤ J)] :
    (𝟭 C).IsContinuous K J where
  op_comp_isSheaf_of_types F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (F.property.of_le h.out)

/-- The topology inequality persists on slices. Source: Stacks, section-compare-general
(blueprint: lem-trf-comparison-truncated-cohomology). -/
instance overTopologyLE {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C) [h : Fact (τ' ≤ τ)] (X : C) :
    Fact (τ'.toGrothendieck.over X ≤ τ.toGrothendieck.over X) :=
  ⟨fun _ _ hS ↦ Precoverage.toGrothendieck_mono h.out _ hS⟩

/-- The canonical pullback is a left adjoint. Source: Stacks, section-compare
(blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityPullbackLeftAdjoint {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] :
    ((𝟭 C).sheafPullback AddCommGrpCat.{u} K J).IsLeftAdjoint :=
  ((𝟭 C).sheafAdjunctionContinuous AddCommGrpCat.{u} K J).isLeftAdjoint

/-- Direct image is additive as a right adjoint. Source: Stacks, section-compare
(blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityPushforwardAdditive {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] :
    ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{u} K J).Additive :=
  have := ((𝟭 C).sheafAdjunctionContinuous AddCommGrpCat.{u} K J).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Exactness of the identity-site inverse image. Source: Stacks, section-compare
(blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityPullbackFiniteLimits {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] :
    PreservesFiniteLimits ((𝟭 C).sheafPullback AddCommGrpCat.{u} K J) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (𝟭 C) AddCommGrpCat.{u} K J

/-- Inverse image is additive as a left adjoint between abelian categories.
Source: Stacks, section-compare (blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityPullbackAdditive {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] :
    ((𝟭 C).sheafPullback AddCommGrpCat.{u} K J).Additive :=
  ((𝟭 C).sheafAdjunctionContinuous AddCommGrpCat.{u} K J).left_adjoint_additive

/-- A right adjoint to exact inverse image preserves injectives. Source: Stacks,
Tag 0D6E (blueprint: lem-trf-comparison-truncated-cohomology). -/
instance identityPushforwardPreservesInjectives {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] :
    ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{u} K J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((𝟭 C).sheafAdjunctionContinuous AddCommGrpCat.{u} K J)

/-- Derived sections of the adjunction unit, followed by the canonical derived
sections/direct-image identification. Source: Stacks, Tags 0EZB and 0D6E
(blueprint: lem-trf-comparison-truncated-cohomology). -/
def comparisonDerivedSections {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] (U : C) :
    (sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerivedFunctorPlus ⟶
      ((𝟭 C).sheafPullback AddCommGrpCat.{u} K J).mapDerivedCategoryPlus ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      ((𝟭 C).sheafAdjunctionContinuous AddCommGrpCat.{u} K J).derivedPlus.unit
      (sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((𝟭 C).sheafPullback AddCommGrpCat.{u} K J).mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso'
        ((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{u} K J)
        (sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) (Iso.refl _)).hom

/-- The canonical degree-`r` pullback on hypercohomology, as a natural transformation.
Source: Stacks, Tag 0EZB (blueprint: lem-trf-comparison-truncated-cohomology). -/
def comparisonHypercohomology {C : Type u} [SmallCategory C]
    (J K : GrothendieckTopology C) [Fact (K ≤ J)] (U : C) (r : ℤ) :=
  Functor.whiskerRight (comparisonDerivedSections J K U)
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} r)

/-- Relocalization direct image is additive as a right adjoint. Source: Stacks,
Tag 03EH (blueprint: lem-trf-comparison-truncated-cohomology). -/
instance relocalizationPushforwardAdditive {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (J.over X) (J.over Y)).Additive :=
  have := ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (J.over X) (J.over Y)).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Cohomology comparison in degree `r` under `(V_r)`, naturally in the bounded-below
complex. Source: Stacks Project, Tag 0EZB, lemma-V-implies-cohomology-general
(blueprint: lem-trf-comparison-truncated-cohomology).

The five weak Serre conditions and assumptions (1)--(4) are retained separately.
The class A_X is the essential image of the canonical inverse image. Naturality
is encoded by `comparisonHypercohomology`, which is a natural transformation,
and this theorem says that its component is invertible on every allowed object.

Proof following the nine steps in the DAG:
1. Abelian sheaves on these small sites form Grothendieck abelian categories.
   Inverse image is exact sheafification. For A' in the given class the finer
   sheaf condition makes A' → epsilon_* epsilon^* A' an isomorphism: extend the
   identity by the sheafification universal property and use its uniqueness.
   Uses lem-cbc-sieve-module-sheaves-grothendieck,
   lem-weil-pbc-sheafification-exact, lem-weil-pbc-exact-functor-complex-cohomology,
   and def-weil-pbc-sheafification.
2. Use the unit u of the derived adjunction. The exact inverse image acts
   termwise, and both derived functors are triangulated. Shift compatibility
   makes u into a morphism of each distinguished triangle, including its last map.
   Uses lem-weil-pbc-exact-functor-derived-functor, lem-weil-pbc-derived-adjunction-shift,
   lem-sf-exact-functor-derived-triangulated,
   lem-weil-pbc-derived-direct-image-triangulated,
   and lem-weil-pbc-commshift-nattrans-triangle-morphism.
3. On a sheaf A' in degree zero, ordinary higher direct images compute the
   cohomology of R epsilon_* epsilon^* A'. Its degree-zero unit is that in step 1;
   degrees 1 through r vanish by V_r and negative degrees vanish by right
   derived negative vanishing. Thus u is an isomorphism through degree r.
   Shift compatibility gives the same assertion on A'[-q], for 0 ≤ q ≤ r.
   Uses lem-sp-derived-functor-single-identification, lem-sp-derived-well-defined,
   and lem-sp-shift-identification.
4. Truncate L at r. The truncation map is an isomorphism on cohomology through
   r and monic in degree r+1 (zero source). Exact inverse image preserves this.
   Apply the derived-functor truncation lemma to sections on both sites. The
   two truncation maps induce isomorphisms on degree-r hypercohomology.
   Uses def-sbc-standard-tstructure-derived-category
   and lem-weil-pbc-derived-functor-truncation-iso.
5. Filter K = tau_le_r L by its finite standard truncations K_q. Their
   distinguished triangles have successive quotients H^q(K)[-q]. Start with
   K_(-1) = 0, since L is connective. The derived units give morphisms of these
   triangles and therefore natural maps of their long exact cohomology sequences.
   Uses lem-weil-pbc-truncation-triangle, lem-sp-long-exact-of-triangle,
   and lem-sf-derived-homology-long-exact.
6. Induct on q using the five lemma on the five-term segment from H^(i-1)
   of the quotient to H^(i+1) of K_(q-1). The first, second and fourth vertical
   maps are isomorphisms. The fifth is an isomorphism for i < r and monic for
   i = r because its source is zero. This proves u_K is an isomorphism through
   r, and it is monic in degree r+1 since H^(r+1)(K) = 0.
   Uses lem-weil-pbc-five-lemma.
7. Apply the derived-functor truncation lemma to u_K and coarse sections.
   The degree-(r+1) monomorphism checked in step 6 is necessary here. The
   actual map H^r(R Gamma(u_K)) is consequently invertible.
   Uses lem-weil-pbc-derived-functor-truncation-iso.
8. Direct image preserves injectives, and coarse sections after direct image
   are fine sections, with unchanged underlying presheaves. The canonical
   composition isomorphism R Gamma R epsilon_* = R Gamma identifies the map
   in step 7 with `comparisonHypercohomology`, exactly the map defined above.
   Uses lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
9. Naturality of the unit and composition isomorphism gives the commutative
   square for K → L. Both truncation sides are invertible by step 4, so the
   comparison for L is invertible. The same naturality works for every map
   of allowed complexes. For r = 0 the vanishing range is empty and the
   filtration has only q = 0. Assumptions (1), (2), (4) and weak Serre closure
   are part of the situation although (3) and V_r suffice for this argument.
-/
theorem comparisonTruncatedCohomology
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    [hτ : Fact (τ' ≤ τ)]
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (kernel f))
    (hcokernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (cokernel f))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ (T : C) (p : T ⟶ X) (q : T ⟶ Y'), IsPullback p q f g ∧ P q)
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X (τ'.toGrothendieck.overMapPullback AddCommGrpCat.{u} f |>.obj H))
    (htauSheaf : ∀ (X : C) (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ, A' Y ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.toGrothendieck.over X) (τ'.toGrothendieck.over Y)).rightDerived i).obj H))
    (r : ℕ)
    (hr : ∀ (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}),
      (∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
        A' X H' ∧ Nonempty (H ≅
          ((𝟭 (Over X)).sheafPullback AddCommGrpCat.{u}
            (τ'.toGrothendieck.over X) (τ.toGrothendieck.over X)).obj H')) →
      ∀ i : ℕ, 1 ≤ i → i ≤ r →
        IsZero ((((𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (τ'.toGrothendieck.over X) (τ.toGrothendieck.over X)).rightDerived i).obj H))
    (X : C) (L : DerivedCategory.Plus (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}))
    (hconnective : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj L))
    (hcohomology : ∀ i : ℤ, 0 ≤ i → i ≤ (r : ℤ) →
      A' X ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso ((comparisonHypercohomology (τ.toGrothendieck.over X)
      (τ'.toGrothendieck.over X) (Over.mk (𝟙 X)) r).app L) := by
  sorry

end CategoryTheory.RefinedTopologyComparison
