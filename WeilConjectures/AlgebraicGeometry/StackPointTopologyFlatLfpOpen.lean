/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen

/-! # Topology of algebraic stacks and openness of flat locally presented maps

Source: Stacks Project, stacks-properties.tex, Tags 04XG and 04XL
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open).

The existing field-object quotient and induced point maps are used unchanged. The topology
is constructed from all smooth surjective scheme atlases, without choosing an atlas. The
canonical comparison with algebraic-space points sends each field representative to its
Yoneda object in the discrete fibred groupoid.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- The point of a stack obtained by applying a scheme chart to a residue-field point.
Source: Stacks Project, Tag 04XG, the paragraph after definition-points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open). -/
def moduliSchemePointMap {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (x : U.left) : ModuliPoints F :=
  moduliPointMap a (Quot.mk _
    ⟨CostructuredArrow.mk (yoneda.map
      (Over.homMk (U.left.fromSpecResidueField x) rfl :
        Over.mk (U.left.fromSpecResidueField x ≫ U.hom) ⟶ U)),
      ⟨U.left.residueField x, inferInstance, ⟨Iso.refl _⟩⟩⟩)

/-- The final topology for all smooth surjective scheme atlases. For an algebraic stack,
any one atlas gives this same topology, as stated below.
Source: Stacks Project, Tag 04XL, lemma-topology-points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open). -/
instance moduliPointTopologicalSpace {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : TopologicalSpace (ModuliPoints F) :=
  ⨆ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (_ : IsSmoothModuliAtlas F U a),
      TopologicalSpace.coinduced (moduliSchemePointMap a) inferInstance

/-- A field-valued presheaf representative determines its actual Yoneda object.
Source: Stacks Project, Tag 04XG, agreement with algebraic-space points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open). -/
def moduliSpaceFieldObject {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type u}
    (x : AlgebraicSpace.PointRepresentative P) : ModuliFieldObject (discreteModuli P) :=
  ⟨CostructuredArrow.mk (yonedaEquiv.symm x.value),
    ⟨x.K, inferInstance, ⟨Iso.refl _⟩⟩⟩

/-- Common-field-equivalent representatives give the same point of the discrete stack.
Source: Stacks Project, Tag 04XG, agreement with algebraic-space points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open).

Proof: a witness L with its two field embeddings and equal restrictions gives a Yoneda
object over Spec L and arrows from it to the two displayed Yoneda objects. Each arrow
identifies its endpoints in ModuliPoints by Quot.sound. Compose the two equalities.
This is the well-definedness of the canonical comparison, not a choice of point classes. -/
theorem moduliSpaceFieldObject_rel {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type u}
    (x y : AlgebraicSpace.PointRepresentative P) (h : x.Rel y) :
    Quot.mk (ModuliFieldRelation (discreteModuli P)) (moduliSpaceFieldObject x) =
      Quot.mk (ModuliFieldRelation (discreteModuli P)) (moduliSpaceFieldObject y) := by
  sorry

/-- Canonical identification from algebraic-space point classes to discrete-stack points.
Source: Stacks Project, Tag 04XG, agreement with algebraic-space points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open). -/
def moduliSpacePointMap {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u) :
    AlgebraicSpace.Point P → ModuliPoints (discreteModuli P) :=
  Quot.lift (fun x ↦ Quot.mk _ (moduliSpaceFieldObject x))
    (moduliSpaceFieldObject_rel (P := P))

/-- The topology on stack points agrees with the usual topology on algebraic spaces.
Source: Stacks Project, Tags 04XG and 04XL
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open).

Proof: field-valued Yoneda objects identify the two quotients bijectively (04XG).
Choose a surjective étale scheme atlas of A. It is also smooth, and the atlas criterion
of lem-sfb-stack-point-topology identifies opens on the stack side with inverse images
on this scheme. The algebraic-space topology has exactly the same atlas criterion.
The two residue-field maps agree by Yoneda, proving that the comparison is a homeomorphism. -/
theorem moduliSpacePointMap_isHomeomorph {S : Scheme.{u}} (A : AlgebraicSpace S) :
    IsHomeomorph (moduliSpacePointMap A.obj.obj) := by
  sorry

/-- Atlas independence, continuity, and openness for flat locally presented space sources.
Source: Stacks Project, Tags 04XG and 04XL, lemma-topology-points
(blueprint: lem-sfb-stack-point-topology-flat-lfp-open).

Proof: (1) Apply lem-sfb-stack-point-topology to obtain the atlas-independent topology,
agreement with scheme and space topologies, and continuity of stack morphisms. Taking
complements in its closed-set criterion gives the displayed open-set criterion. Functors
preserve the isomorphisms over common field extensions defining point equivalence.
(2) For q from A and a smooth surjective scheme atlas p:U → F, the diagonal criterion
lem-sfb-stack-diagonal-space-source-representability makes P = A ×_F U an algebraic space.
Its projection s:P → U is flat and locally finitely presented by
lem-sfb-stack-chartwise-smooth-etale-calculus. It is open by
lem-sfb-flat-lfp-space-universally-open. The other projection r:P → A is continuous by
lem-sfb-stack-point-topology, so r⁻¹(O) is open for open O in A.
(3) The identity p⁻¹(q(O)) = s(r⁻¹(O)) follows in one direction from the fibre-product
comparison. Conversely, equal image point classes of a and u become isomorphic over a
common field extension; the two objects and this isomorphism give an object of P mapping
to a and u (Tag 04XH). Thus p⁻¹(q(O)) is open. The atlas criterion makes q(O) open.
No surjectivity of q is used. -/
theorem stackPointTopology_flat_lfp_open {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsAlgebraicModuliStack F) :
    (∀ (U : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U p → ∀ W : Set (ModuliPoints F),
        IsOpen W ↔ IsOpen (moduliSchemePointMap p ⁻¹' W)) ∧
    (∀ (G : BasedCategory.{v₂, w₂} (Over S)), IsAlgebraicModuliStack G →
      ∀ f : BasedFunctor F G, Continuous (moduliPointMap f)) ∧
    (∀ (A : AlgebraicSpace S) (q : BasedFunctor (discreteModuli A.obj.obj) F),
      ModuliSpaceTest @Flat q → ModuliSpaceTest @LocallyOfFinitePresentation q →
        IsOpenMap (moduliPointMap q ∘ moduliSpacePointMap A.obj.obj)) := by
  sorry

end CategoryTheory
