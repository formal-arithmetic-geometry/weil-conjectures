/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Extension of maps from a nodal curve over a trait

Source: de Jong, Families of curves and alterations, Lemma 3.13, printed p.609,
its graph-domination and rational-exceptional-curve contraction argument
(blueprint: lem-sfb-nodal-trait-map-extension).

The node uses the no-rational-maps variant of that argument. The graph closure below
is constructed by the vanishing ideal of the topological closure of the generic graph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace NodalTraitMapExtension

/-- The generic graph, mapped into the product over the original base.
Source: de Jong, Lemma 3.13, printed p.609
(blueprint: lem-sfb-nodal-trait-map-extension). -/
noncomputable def genericGraph {S C X E : Scheme.{u}} (f : C ⟶ S) (g : X ⟶ S)
    (η : E ⟶ S) (a : pullback f η ⟶ pullback g η)
    (ha : a ≫ pullback.snd g η = pullback.snd f η) : pullback f η ⟶ pullback f g :=
  pullback.lift (pullback.fst f η) (a ≫ pullback.fst g η)
    (by
      calc
        pullback.fst f η ≫ f = pullback.snd f η ≫ η := pullback.condition
        _ = (a ≫ pullback.snd g η) ≫ η := by rw [ha]
        _ = (a ≫ pullback.fst g η) ≫ g := by simp only [Category.assoc, pullback.condition])

/-- The ideal cutting out the reduced closure of the generic graph.
Source: de Jong, Lemma 3.13, printed p.609; Stacks Tags 01J3 and 01J4
(blueprint: lem-sfb-nodal-trait-map-extension). -/
noncomputable def graphClosureIdeal {S C X E : Scheme.{u}} (f : C ⟶ S) (g : X ⟶ S)
    (η : E ⟶ S) (a : pullback f η ⟶ pullback g η)
    (ha : a ≫ pullback.snd g η = pullback.snd f η) :
    (pullback f g).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range (genericGraph f g η a ha)))

/-- The actual reduced graph closure, with no choice of a dominating modification.
Source: de Jong, Lemma 3.13, printed p.609; Stacks Tags 01J3 and 01J4
(blueprint: lem-sfb-nodal-trait-map-extension). -/
noncomputable def graphClosure {S C X E : Scheme.{u}} (f : C ⟶ S) (g : X ⟶ S)
    (η : E ⟶ S) (a : pullback f η ⟶ pullback g η)
    (ha : a ≫ pullback.snd g η = pullback.snd f η) : Scheme.{u} :=
  (graphClosureIdeal f g η a ha).subscheme

/-- The first projection of the reduced graph closure.
Source: de Jong, Lemma 3.13, printed p.609
(blueprint: lem-sfb-nodal-trait-map-extension). -/
noncomputable def graphProjection {S C X E : Scheme.{u}} (f : C ⟶ S) (g : X ⟶ S)
    (η : E ⟶ S) (a : pullback f η ⟶ pullback g η)
    (ha : a ≫ pullback.snd g η = pullback.snd f η) : graphClosure f g η a ha ⟶ C :=
  (graphClosureIdeal f g η a ha).subschemeι ≫ pullback.fst f g

end NodalTraitMapExtension

/-- A generic morphism extends when all geometric projective-line maps to the target
fibres are constant. The source and its reduced graph closure are integral, the source
is normal, and the actual graph projection is an isomorphism. No flatness, integrality
or dimension condition is imposed on the target; the generic map may be constant.

Source: de Jong, Families of curves and alterations, Lemma 3.13, printed p.609,
agent-formulated no-rational-maps version
(blueprint: lem-sfb-nodal-trait-map-extension).

Proof (the node's five steps):
1. Apply lem-sfb-smooth-generic-nodal-trait-normality to obtain an integral normal source
   with dense generic fibre. A DVR is Noetherian. H-projective morphisms are proper
   (lem-pc-projective-proper), and finite type over a Noetherian base gives a Noetherian
   source (lem-weil-pbc-finite-type-over-noetherian). The target is separated.
2. The generic graph is closed by the separated diagonal and
   lem-weil-pbc-closed-immersion-base-change. Its reduced closure is integral by
   lem-weil-pbc-reduced-induced-closed-subscheme and def-pc-integral-scheme. On the open
   generic fibre it is the original graph, so the generic graph projection is an isomorphism.
3. Use lem-pc-projective-base-change and lem-weil-pbc-closed-immersion-comp to make the
   graph projection H-projective, hence proper. Apply lem-sfb-nodal-trait-rational-domination
   to dominate it by a proper surjective map whose reduced geometric fibres are points
   or connected finite unions of projective lines.
4. Every projective-line component has constant image by the target hypothesis. Meeting
   components have the same image; connectedness of the finite incidence graph makes
   all images agree. Reduction preserves underlying points (def-weil-pbc-scheme-reduction).
   The dominating map is surjective on geometric fibres by
   lem-weil-pbc-surjective-base-change, and the graph fibre embeds in the target fibre
   by closed-immersion base change. Thus the graph projection has singleton geometric fibres.
5. Ordinary fibres are finite by surjectivity of the geometric-to-ordinary fibre map.
   Apply thm-pqf-finite-iff-proper-finite-fibres, then
   lem-trf-finite-birational-normal-iso to the finite birational map onto the normal source.
   The inverse graph projection followed by the second projection is the required extension;
   its restriction is the original map by the construction of the graph.
-/
theorem nodal_trait_map_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
    (C X : Scheme.{u}) (f : C ⟶ Spec (.of A)) (g : X ⟶ Spec (.of A))
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f] [IsHProjective g]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A F))))]
    [GeometricallyIntegral (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A F))))]
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A)),
      ConnectedSpace ↥(pullback f t) ∧ IsReduced (pullback f t) ∧
        (pullback f t).IsPureDimension 1)
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A)) (x : ↥(pullback f t)),
      x ∉ (pullback.snd f t).smoothLocus →
        Nonempty (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f t).presheaf.stalk x))
          ((pullback f t).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    (hnoRational : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A))
      (a : ProjectiveLine (Spec (.of Ω)) ⟶ pullback g t),
      a ≫ pullback.snd g t = ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) →
        ∃ q : Spec (.of Ω) ⟶ pullback g t,
          q ≫ pullback.snd g t = 𝟙 _ ∧
          a = (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) ≫ q)
    (uη : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A F))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap A F))))
    (huη : uη ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap A F))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A F)))) :
    IsIntegral C ∧
    IsIntegral (NodalTraitMapExtension.graphClosure f g
      (Spec.map (CommRingCat.ofHom (algebraMap A F))) uη huη) ∧
    (∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)) ∧
    IsIso (NodalTraitMapExtension.graphProjection f g
      (Spec.map (CommRingCat.ofHom (algebraMap A F))) uη huη) ∧
    ∃ v : C ⟶ X, v ≫ g = f ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A F))) ≫ v =
        uη ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A F))) := by
  sorry

end AlgebraicGeometry
