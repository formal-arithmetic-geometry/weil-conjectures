/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.ContinuousSetConstructions

import Sheaf.Paper.NormalizedContinuousSetKanEvaluation
import Sheaf.Paper.NormalizedContinuousSetComparisonCoherence
import Sheaf.Paper.ContinuousSetDescentComponents
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Continuous-function set coefficients and their scheme pullbacks

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6, with ring operations omitted;
Bhatt--Scholze, Lemma 4.2.12, p. 30
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).

The coefficients live in `Type (u + 1)`, the schemes and profinite test spaces in
universe `u`. No finiteness or compactness condition is imposed on the coefficient space.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- There is a unique normalized realization morphism, and it is an isomorphism.
Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Lemmas 4.2.12--4.2.13
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: (1) Quotient-map descent makes the profinite function presheaf a sheaf.
(2) A continuous map to D is constant on connected components, so factors uniquely
and continuously through the component quotient.
(3) Identify X[S] with the pullback of Spec LC(S,Z) and use its spectrum projection r.
(4) The sheafified Kan extension along S ↦ X[S] has the same right adjoint as p_X^*,
so the adjunctions identify their left adjoints with the same units.
(5) The natural maps b ↦ b ∘ r give the unique normalized morphism by this adjunction.
(6) On a weakly contractible affine U, maps U → X[S] are continuous maps π₀(U) → S:
first prove this for finite S by the disjoint open summands, then pass to finite quotients.
Every Kan-colimit class is consequently represented at S = π₀(U), and the normalized
map is c ↦ c ∘ q_U, a bijection. Sheafification does not change these sections.
Such affines cover the site, so the local-bijection theorem makes σ an isomorphism. -/
theorem existsUnique_continuousSetRealization (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    ∃! σ : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D, IsContinuousSetRealization X D σ ∧ IsIso σ := by
  obtain ⟨e, he, h⟩ := normalized_continuous_set_kan_evaluation X
  obtain ⟨σ, hσ, huniq⟩ := (h D).1
  obtain ⟨α, hleg, hfac, heval⟩ := (h D).2 σ hσ
  have hlocal (U : X.ProEt) :=
    Scheme.ProEt.exists_affine_weaklyContractible_covering_family X U
  have hbij (U : X.ProEt) [IsAffine U.left]
      (hw : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} U) :
      Function.Bijective (σ.hom.app (op U)) := by
    obtain ⟨φ, hφ, hrep, hval, ha, hu, hs⟩ := heval U hw
    exact hs
  have hinj : Sheaf.IsLocallyInjective σ := by
    constructor
    intro U a b hab
    obtain ⟨I, V, f, hcov, haff, hw⟩ := hlocal U.unop
    apply (Scheme.ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff (Presieve.ofArrows V f) _).mpr ?_)
      (Precoverage.generate_mem_toGrothendieck (J := Scheme.ProEt.precoverage X) hcov)
    rintro _ _ ⟨i⟩
    have : IsAffine (V i).left := haff i
    apply (hbij (V i) (fun F G e he ↦ hw i F G e
      ((Sheaf.isLocallySurjective_iff_epi e).mp he))).1
    rw [σ.hom.naturality_apply, σ.hom.naturality_apply, hab]
  have hsurj : Sheaf.IsLocallySurjective σ := by
    constructor
    intro U b
    obtain ⟨I, V, f, hcov, haff, hw⟩ := hlocal U
    apply (Scheme.ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff (Presieve.ofArrows V f) _).mpr ?_)
      (Precoverage.generate_mem_toGrothendieck (J := Scheme.ProEt.precoverage X) hcov)
    rintro _ _ ⟨i⟩
    have : IsAffine (V i).left := haff i
    exact (hbij (V i) (fun F G e he ↦ hw i F G e
      ((Sheaf.isLocallySurjective_iff_epi e).mp he))).2 _
  refine ⟨σ, ⟨hσ, (Sheaf.isLocallyBijective_iff_isIso σ).mp ⟨hinj, hsurj⟩⟩, ?_⟩
  intro τ hτ
  exact huniq τ hτ.1

/-- The normalized realization morphism, determined uniquely by its test-function formula.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRealizationHom (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D :=
  (existsUnique_continuousSetRealization X D).exists.choose

/-- The chosen unique morphism retains both normalization and invertibility.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: apply the specification of the unique morphism in the preceding theorem. -/
theorem continuousSetRealizationHom_spec (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    IsContinuousSetRealization X D (continuousSetRealizationHom X D) ∧
      IsIso (continuousSetRealizationHom X D) := by
  exact (existsUnique_continuousSetRealization X D).exists.choose_spec

/-- The canonical continuous-function realization isomorphism.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRealizationIso (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ≅
      continuousSetSheaf X D :=
  @asIso _ _ _ _ (continuousSetRealizationHom X D) (continuousSetRealizationHom_spec X D).2

/-- Naturality in all continuous maps of Hausdorff totally disconnected coefficients.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: both composites send a test function b to h ∘ b ∘ r. The adjunction hom
bijection and the normalization uniqueness in step 5 imply equality (step 7). -/
theorem continuousSetRealization_natural (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D]
    [TopologicalSpace E] [T2Space E] [TotallyDisconnectedSpace E] (h : C(D, E)) :
    (profinitePointSetSchemeInverseImage X).map
        (continuousSetProfiniteFunctor.map (TopCat.ofHom h)) ≫
        continuousSetRealizationHom X E =
      continuousSetRealizationHom X D ≫ continuousSetSheafMap X h := by
  exact ((normalized_continuousSetComparison_coherence continuousSetRealizationHom
    (fun X D _ _ _ ↦ (continuousSetRealizationHom_spec X D).1)).1 X D E h).symm

/-- Finite products, including the empty product, are respected by realization.
The two displayed maps are the canonical maps to products, specified by projections.
Source: Hemo--Richarz--Scholbach, Example 3.1, finite-product refinement
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: sectionwise continuous functions into a product are tuples of continuous functions;
for the empty product there is exactly one function. The point inverse image preserves
finite products. Naturality with respect to each projection therefore identifies the
product comparison with realization of the product (step 7). -/
theorem continuousSetRealization_products (X : Scheme.{u}) (I : Type u) [Finite I]
    (D : I → Type (u + 1)) [∀ i : I, TopologicalSpace (D i)] [∀ i : I, T2Space (D i)]
    [∀ i : I, TotallyDisconnectedSpace (D i)] :
    IsIso (Pi.lift (fun i : I ↦ continuousSetSheafMap X
      (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))) ∧
    IsIso (Pi.lift (fun i : I ↦ (profinitePointSetSchemeInverseImage X).map
      (continuousSetProfiniteFunctor.map (TopCat.ofHom
        (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))))) ∧
    Pi.lift (fun i : I ↦ (profinitePointSetSchemeInverseImage X).map
        (continuousSetProfiniteFunctor.map (TopCat.ofHom
          (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))) ≫
        continuousSetRealizationHom X (D i)) =
      continuousSetRealizationHom X (∀ i : I, D i) ≫
        Pi.lift (fun i : I ↦ continuousSetSheafMap X
          (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩)) := by
  obtain ⟨hpro, hs, hp, heq⟩ :=
    (normalized_continuousSetComparison_coherence continuousSetRealizationHom
      (fun X D _ _ _ ↦ (continuousSetRealizationHom_spec X D).1)).2.1 X I D
  exact ⟨hs, hp, heq.symm⟩

/-- The induced comparison for the actual inverse image is invertible and agrees with
transport of the point comparison through the normalized realization isomorphisms.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following paragraph
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: transpose both composites through the composite adjunction and evaluate on a
profinite test function b. Both give b ∘ r on the base-changed test object, since the
label projection commutes with base change. The adjunction bijection gives equality.
The other three arrows are isomorphisms, so the comparison is an isomorphism (step 8). -/
theorem continuousSetRealization_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    IsIso (continuousSetPullbackMap f D) ∧
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
        (continuousSetRealizationHom Y D) ≫ continuousSetPullbackMap f D =
      (profinitePointSetSchemeComp f).hom.app (continuousSetProfiniteSheaf D) ≫
        continuousSetRealizationHom X D := by
  have heq := (normalized_continuousSetComparison_coherence continuousSetRealizationHom
    (fun X D _ _ _ ↦ (continuousSetRealizationHom_spec X D).1)).2.2.1 Y X f D
  have : IsIso (continuousSetRealizationHom X D) := (continuousSetRealizationHom_spec X D).2
  have : IsIso (continuousSetRealizationHom Y D) := (continuousSetRealizationHom_spec Y D).2
  have : IsIso ((Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
      (continuousSetRealizationHom Y D) ≫ continuousSetPullbackMap f D) := by
    rw [heq]
    infer_instance
  exact ⟨IsIso.of_isIso_comp_left
    ((Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
      (continuousSetRealizationHom Y D)) (continuousSetPullbackMap f D), heq⟩

/-- Identity and composition coherence for the actual induced scheme comparisons.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following paragraph
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: the identity precomposition is the identity. For composition, precomposition by
the two successive projections equals precomposition by the composite projection under
the canonical iterated-pullback isomorphism. Transpose these identities by the inverse
image adjunctions; equivalently apply the point-pullback coherence and step 8. -/
theorem continuousSetRealization_coherence (D : Type (u + 1)) [TopologicalSpace D]
    [T2Space D] [TotallyDisconnectedSpace D] :
    (∀ X : Scheme.{u}, continuousSetPullbackMap (𝟙 X) D =
      (profinitePointSetIdentity X).hom.app (continuousSetSheaf X D)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z),
      (profinitePointSetComp f g).hom.app (continuousSetSheaf Z D) ≫
          (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
            (continuousSetPullbackMap g D) ≫ continuousSetPullbackMap f D =
        continuousSetPullbackMap (f ≫ g) D) := by
  have h := normalized_continuousSetComparison_coherence continuousSetRealizationHom
    (fun X D _ _ _ ↦ (continuousSetRealizationHom_spec X D).1)
  exact ⟨h.2.2.2.1 D, fun X Y Z f g ↦ (h.2.2.2.2 D Z Y X g f).symm⟩

/-- For arbitrary discrete coefficients the continuous-function sheaf is the associated
constant sheaf, via the canonical constant-section comparison.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: the open fibres of a function to D cover its source, and the function is constant
on each fibre. Equal constants agree locally, also on the empty scheme by its empty
cover. Thus the constant-presheaf map is locally bijective, including when D is empty.
The local-bijection sheafification criterion proves invertibility (step 9). -/
theorem continuousSetRealization_discrete (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [DiscreteTopology D] : IsIso (continuousSetConstantMap X D) := by
  exact ((continuousSet_descent_components X D).2.2.2 inferInstance).2.2.2

/-- On qcqs objects, composition with the component quotient gives exactly all sections.
The equivalence is Mathlib's existing connected-component factorization equivalence.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: each connected component has connected image in a totally disconnected target,
hence a singleton image. The unique factor is continuous by the quotient topology.
Precomposition with the quotient is its inverse (step 2). -/
theorem continuousSetRealization_components (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] (U : X.ProEt)
    [CompactSpace U.left] [QuasiSeparated (toSpecZ U.left)]
    (s : C(ConnectedComponents U.left, D)) :
    (continuousMapPresheafEquivOfTotallyDisconnectedSpace D U.left).symm s =
      s.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
  rfl

end AlgebraicGeometry.ProEtale
