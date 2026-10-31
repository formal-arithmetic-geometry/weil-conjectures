/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousSetConstructions
public import Mathlib.Topology.Category.TopCat.Yoneda
public import Mathlib.CategoryTheory.Sites.LocallyBijective

import WeilConjectures.Topology.SpectralSpace.ConnectedComponentsProfinite

/-! # Descent and component factorization of continuous set functions

Source: Bhatt--Scholze, Lemma 4.2.12 and Lemma 4.3.2(1), pp. 30--31;
Hemo--Richarz--Scholbach, Example 3.1, p. 6
(blueprint: lem-sfb-continuous-set-descent-components).

All presheaves, quotient spaces and comparison maps below are existing constructions.
The pointwise open-neighbourhood clause expresses lifting on an open cover, without
requiring either the coefficient space or the scheme to be nonempty.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuous set functions satisfy profinite and pro-etale descent, factor naturally
through the profinite component quotient on qcqs schemes, and for discrete coefficients
are the constant sheaf via the canonical map sending an element to a constant function.

Source: Bhatt--Scholze, Lemma 4.2.12 and Lemma 4.3.2(1), pp. 30--31;
Hemo--Richarz--Scholbach, Example 3.1, p. 6
(blueprint: lem-sfb-continuous-set-descent-components).

Proof for stage 3, following the seven steps of the node.
1. A finite jointly surjective family of profinite spaces gives a surjection from its
finite disjoint union. This is a quotient map by
`lem-sfb-compact-hausdorff-surjection-quotient`. Compatible continuous functions are
constant on its fibres, so descend uniquely and continuously. An empty jointly
surjective family has empty target and has exactly one gluing.
2. `lem-sfb-set-continuous-functions-fpqc-sheaf` applies to the actual continuous-map
presheaf. Pro-etale covers are fpqc covers by `def-weil-pbc-proetale-site`, so its
restriction `def-sfb-continuous-set-presheaf` is a sheaf.
3. `lem-weil-pbc-qcqs-scheme-spectral` makes the underlying qcqs space spectral.
`lem-pe-spectral-components-profinite` makes its component quotient profinite.
4. Connected components have connected images, hence singleton images in a totally
disconnected target. Factor through the quotient; the factor is continuous by the
quotient topology. Surjectivity of the quotient gives uniqueness and the precomposition
bijection. Precomposition with a scheme map commutes with the component map, and
postcomposition with a coefficient map commutes with this precomposition. These are the
two naturality equalities in the statement.
5. Open subschemes are site objects and their covers are pro-etale covers: use
`lem-weil-pbc-open-immersion-etale`, `det-pe-morphisms-etale-comparison` and weakly etale
composition from `lem-weil-pbc-ind-etale-stability`. Cover affine opens by affine opens
inside the given cover and extract a finite subcover by
`lem-weil-pbc-affine-scheme-qcqs`.
6. For discrete D the open fibres of a continuous section form an open cover on which
it is constant. Equal constants on a nonempty object are equal by evaluation. On an
empty object the empty cover proves both local assertions, also when D is empty.
7. Apply `lem-cbc-set-presheaf-sheafification-local-bijection` to the canonical
constant-presheaf map. Its target is already a sheaf by step 2; its source sheafifies
to `def-weil-pbc-constant-sheaf`. Thus its sheafification adjunct, the specified
`continuousSetConstantMap`, is an isomorphism. -/
theorem continuousSet_descent_components (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (ContinuousMap.yonedaPresheaf
        (CompHausLike.compHausLikeToTop (fun T ↦ TotallyDisconnectedSpace T)) D) ∧
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D) ∧
    (∀ (U : Over X), CompactSpace U.left → QuasiSeparated (toSpecZ U.left) →
      CompactSpace (ConnectedComponents U.left) ∧
      T2Space (ConnectedComponents U.left) ∧
      TotallyDisconnectedSpace (ConnectedComponents U.left) ∧
      (∀ (_ : TotallyDisconnectedSpace D),
        Function.Bijective (fun g : C(ConnectedComponents U.left, D) ↦
          g.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
        (∀ (V : Over X), CompactSpace V.left → QuasiSeparated (toSpecZ V.left) →
          ∀ (a : V ⟶ U) (g : C(ConnectedComponents U.left, D)),
            (g.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩).comp
                a.left.base.hom =
              (g.comp ⟨a.left.base.hom.continuous.connectedComponentsMap,
                a.left.base.hom.continuous.connectedComponentsMap_continuous⟩).comp
                  ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
        (∀ (E : Type (u + 1)) [TopologicalSpace E] [TotallyDisconnectedSpace E]
          (b : C(D, E)) (g : C(ConnectedComponents U.left, D)),
          b.comp (g.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) =
            (b.comp g).comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩))) ∧
    (∀ (_ : DiscreteTopology D),
      (∀ (U : X.ProEt) (s : C(U.left, D)) (x : U.left),
        ∃ (W : U.left.Opens) (d : D), x ∈ W ∧ ∀ y : W, s y = d) ∧
      Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
        (continuousSetConstantPresheafMap X D) ∧
      Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
        (continuousSetConstantPresheafMap X D) ∧
      IsIso (continuousSetConstantMap X D)) := by
  refine ⟨(continuousSetProfiniteSheaf D).property, ?_, ?_, ?_⟩
  · exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf _
      Scheme.proetaleTopology (continuousMapPresheaf D)
      (.of_le Scheme.proetaleTopology_le_fpqcTopology
        (isSheaf_fpqcTopology_continuousMapPresheaf D))
  · intro U hcompact hqs
    have : CompactSpace U.left := hcompact
    have : QuasiSeparated (toSpecZ U.left) := hqs
    have : QuasiSeparatedSpace U.left :=
      quasiSeparatedSpace_of_quasiSeparated (toSpecZ U.left)
    have : SpectralSpace U.left := ⟨⟩
    obtain ⟨hc, ht, hd⟩ := spectralSpace_connectedComponents_profinite (T := U.left)
    refine ⟨hc, ht, hd, ?_⟩
    intro hD
    have : TotallyDisconnectedSpace D := hD
    refine ⟨(continuousMapPresheafEquivOfTotallyDisconnectedSpace D U.left).symm.bijective,
      ?_, ?_⟩
    · intro V _ _ a g
      ext x
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        Continuous.connectedComponentsMap_mk]
    · intro E _ _ b g
      rfl
  · intro hD
    have : DiscreteTopology D := hD
    have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
        (continuousSetConstantPresheafMap X D) := by
      constructor
      intro U s
      change C(U.left, D) at s
      let W (x : U.left) : U.left.Opens :=
        ⟨s ⁻¹' {s x}, (isOpen_discrete {s x}).preimage s.continuous⟩
      let V (x : U.left) : X.ProEt := Scheme.ProEt.mk ((W x).ι ≫ U.hom)
      let f (x : U.left) : V x ⟶ U :=
        MorphismProperty.Over.Hom.mk (Over.homMk (W x).ι) trivial
      apply (Scheme.ProEt.topology X).superset_covering
        ((Sieve.generate_le_iff (Presieve.ofArrows V f) _).mpr ?_)
        (Precoverage.generate_mem_toGrothendieck (J := Scheme.ProEt.precoverage X) ?_)
      · rintro _ _ ⟨x⟩
        refine ⟨s x, ?_⟩
        change ContinuousMap.const (W x).toScheme (s x) = s.comp (W x).ι.base.hom
        ext y
        exact y.property.symm
      · change (Presieve.ofArrows V f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
          Scheme.proetalePrecoverage U.left
        rw [Presieve.map_ofArrows]
        apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
        apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
        refine ⟨?_, fun x ↦ inferInstanceAs (IsOpenImmersion (W x).ι)⟩
        intro x
        exact ⟨x, ⟨x, rfl⟩, rfl⟩
    have hinj : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
        (continuousSetConstantPresheafMap X D) := by
      constructor
      intro V d e h
      by_cases hV : Nonempty V.unop.left
      · obtain ⟨x⟩ := hV
        have hde : d = e := congrArg (fun f : C(V.unop.left, D) ↦ f x) h
        subst e
        simp
      · have : IsEmpty V.unop.left := not_nonempty_iff.mp hV
        exact (Scheme.ProEt.topology X).superset_covering bot_le
          (Scheme.ProEt.bot_mem_topology V.unop)
    refine ⟨?_, hsurj, hinj, ?_⟩
    · intro U s x
      refine ⟨⟨s ⁻¹' {s x}, (isOpen_discrete {s x}).preimage s.continuous⟩, s x,
        rfl, ?_⟩
      intro y
      exact y.property
    · have hw := (Scheme.ProEt.topology X).W_of_isLocallyBijective
        (continuousSetConstantPresheafMap X D)
      have : IsIso ((presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1))).map
          (continuousSetConstantPresheafMap X D)) :=
        ((Scheme.ProEt.topology X).W_iff _).mp hw
      unfold continuousSetConstantMap
      rw [Adjunction.homEquiv_counit]
      infer_instance

end AlgebraicGeometry.ProEtale
