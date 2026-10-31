/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.SmallEnlargedEtaleModules
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion

/-!
# Fppf covering calculus for algebraic spaces

Source: Stacks Project, Topologies on Algebraic Spaces, Tags 03Y8, 0DFC and 03Y9(2),(3)
(blueprint: lem-sfb-space-fppf-covering-calculus).

The family predicate uses the recorded chartwise flatness and local finite presentation,
and the recorded extension-lifting definition of joint surjectivity on point classes.
The pullback and the scheme embedding are the existing actual sheaf constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fppf families are chartwise flat and locally finitely presented, and jointly surjective
on field-valued point classes. No nonemptiness condition is imposed on the index type.
Source: Stacks, Tag 03Y8 (blueprint: lem-sfb-space-fppf-covering-calculus). -/
def IsFppfCover {S : Scheme.{u}} {I : Type w} {X : AlgebraicSpace S}
    {Xᵢ : I → AlgebraicSpace S} (f : ∀ i : I, Xᵢ i ⟶ X) : Prop :=
  (∀ i : I, MapIsFlat (f i) ∧ MapIsLocallyOfFinitePresentation (f i)) ∧
    IsJointlySurjective (fun i : I ↦ (f i).hom.hom)

/-- Every jointly surjective representable étale family is fppf.
Source: Stacks, Tag 0DFC, étale case
(blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node step 1): choose a surjective étale scheme atlas of the target and then of
its pullback to each source [def-trf-algebraic-space,
lem-trf-space-fibre-products-etale-covers]. Representability makes the intervening
scheme map étale; compose the étale charts
[lem-trf-space-representable-etale-scheme-tests]. An étale scheme morphism is flat and
locally of finite presentation [def-weil-etale-morphism]. The chart test descends both
properties to the space map [lem-sfb-space-local-properties-chart-test]. Joint
surjectivity is exactly the hypothesis. The same argument includes empty members. -/
theorem isFppfCover_of_isEtale {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (f : ∀ i : I, Xᵢ i ⟶ X)
    (he : ∀ i : I, IsEtale (f i).hom.hom)
    (hs : IsJointlySurjective (fun i : I ↦ (f i).hom.hom)) :
    IsFppfCover f := by
  sorry

/-- Fppf families remain fppf after any algebraic-space base change.
Source: Stacks, Tag 03Y9(3) (blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node steps 2--3): choose atlases V → X, U → Xᵢ ×_X V and V' → X' ×_X V
[def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers]. The chart map
U → V is flat and locally finitely presented by
[lem-sfb-space-local-properties-chart-test]. Its scheme pullback U ×_V V' → V'
has both properties [lem-weil-pbc-flat-morphism-base-change,
lem-weil-pbc-qcqs-morphism-permanence]. The atlas of the pulled-back source and the
surjective étale chart V' → X' are valid by
[lem-trf-space-representable-etale-scheme-tests], so the chart test descends both
properties. For a field-valued point of X', lift its image in X to some Xᵢ after
an extension [def-trf-algebraic-space-jointly-surjective-family]. The compatible pair
is a section of the sheaf fibre product, proving joint surjectivity. No condition
on the base-changing map occurs. -/
theorem isFppfCover_pullback {S : Scheme.{u}} {I : Type w}
    {X X' : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S}
    (f : ∀ i : I, Xᵢ i ⟶ X) (hf : IsFppfCover f) (a : X' ⟶ X) :
    IsFppfCover (fun i : I ↦ enlargedFibreProductFst a (f i)) := by
  sorry

/-- Composition of an fppf family with an fppf family over each member is fppf.
The composite index is the dependent sum, in the maximum of the two index universes.
Source: Stacks, Tag 03Y9(2) (blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node steps 4--5): choose compatible scheme atlases V → X, U → Xᵢ ×_X V,
and W → Xᵢₖ ×_{Xᵢ} U. Their source projections are surjective étale by
[lem-trf-space-representable-etale-scheme-tests]. The chart test gives flatness and
local finite presentation of U → V and W → U
[lem-sfb-space-local-properties-chart-test]. The composite W → V has both properties
[lem-pc-flat-compose, lem-sbc-locally-finite-presentation-composition]. Use their
étale locality and the presentation criterion to descend to Xᵢₖ → X
[lem-sfb-scheme-etale-source-target-properties,
lem-sfb-space-etale-presentation-property-criterion]. For joint surjectivity, first
lift a point to Xᵢ over an extension L, and then to Xᵢₖ over an extension M of L.
The composite field embedding and naturality give the required lift for the composite
[def-trf-algebraic-space-jointly-surjective-family, def-weil-size-convention]. -/
theorem isFppfCover_comp {S : Scheme.{u}} {I : Type w} {K : I → Type v}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S}
    {Xᵢₖ : ∀ i : I, K i → AlgebraicSpace S}
    (f : ∀ i : I, Xᵢ i ⟶ X) (e : ∀ (i : I) (k : K i), Xᵢₖ i k ⟶ Xᵢ i)
    (hf : IsFppfCover f) (he : ∀ i : I, IsFppfCover (e i)) :
    IsFppfCover (fun j : Sigma K ↦ e j.1 j.2 ≫ f j.1) := by
  sorry

/-- On schemes the algebraic-space predicate is exactly the usual fppf covering condition.
The maps on the left are the actual Yoneda maps, and the right uses Mathlib's precoverage.
Source: Stacks, Tag 03Y8, scheme-comparison paragraph
(blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node step 6): the chart test agrees with scheme flatness and local finite
presentation [lem-sfb-space-local-properties-chart-test]. A scheme point x represents
the field-valued class of Spec κ(x) → T. Every field-valued map factors uniquely
through this representative [lem-weil-pbc-morphism-from-spec-field]. Representatives
that become equal over a common extension have the same underlying scheme point,
so the identification is bijective and commutes with all scheme maps. Consequently
extension-lifting joint surjectivity is precisely ordinary joint surjectivity
[def-trf-algebraic-space-jointly-surjective-family]. Together the three conditions
are exactly [def-pc-fppf-site], including empty schemes and empty families. -/
theorem isFppfCover_scheme_iff {S : Scheme.{u}} {I : Type w}
    (T : Over S) (Tᵢ : I → Over S) (f : ∀ i : I, Tᵢ i ⟶ T) :
    IsFppfCover (X := schemeSpace T) (Xᵢ := fun i : I ↦ schemeSpace (Tᵢ i))
      (fun i : I ↦ ObjectProperty.homMk ⟨yoneda.map (f i)⟩) ↔
        Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (f i).left) ∈
          Scheme.fppfPrecoverage T.left := by
  sorry

/-- An empty-index family is fppf exactly when the target is the empty algebraic space.
Emptiness is an isomorphism to the existing algebraic space of the empty scheme.
Source: Stacks, Tag 03Y8, empty image union and scheme-comparison paragraph
(blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node step 7): by [def-trf-algebraic-space-jointly-surjective-family] an empty
family covers exactly when the target has no field-valued points. Any section over
a nonempty scheme restricts to such a point by the residue-field map
[lem-weil-pbc-morphism-from-spec-field]. Thus there are no sections on nonempty
schemes. On an empty scheme there is exactly one section by the empty fppf covering
and the sheaf condition [def-trf-algebraic-space, def-pc-fppf-site]. These sectionwise
identifications are natural and identify the sheaf with that of the empty scheme.
Conversely the empty scheme has no field-valued points. Member conditions are vacuous. -/
theorem isFppfCover_empty_index_iff {S : Scheme.{u}} {I : Type w} [IsEmpty I]
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (f : ∀ i : I, Xᵢ i ⟶ X) :
    IsFppfCover f ↔ Nonempty (X ≅ schemeSpace (Over.mk (Scheme.emptyTo S))) := by
  sorry

/-- Removing an empty member neither creates nor destroys an fppf covering.
Source: Stacks, Tag 03Y8, empty members in the defining image union
(blueprint: lem-sfb-space-fppf-covering-calculus).
Proof (node step 7): an empty source contributes no field-valued point, so its removal
preserves the extension-lifting condition
[def-trf-algebraic-space-jointly-surjective-family]. Every scheme chart of the empty
space is empty. Scheme flatness and local finite presentation quantify over its
source points, so their chart tests hold vacuously [def-weil-flat-morphism,
def-sbc-locally-finite-presentation, def-sfb-space-morphism-properties]. Hence restoring
the empty member imposes no additional morphism condition. -/
theorem isFppfCover_remove_empty_member_iff {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S}
    (f : ∀ i : I, Xᵢ i ⟶ X) (i₀ : I)
    (h₀ : Nonempty (Xᵢ i₀ ≅ schemeSpace (Over.mk (Scheme.emptyTo S)))) :
    IsFppfCover f ↔ IsFppfCover (fun i : {i : I // i ≠ i₀} ↦ f i.val) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
