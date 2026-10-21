/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections
import Sheaf.Paper.ProfiniteTestObjectFunctor
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.Limits

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

/-- Restriction of Mathlib's continuous-map presheaf to the small pro-etale site.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
abbrev continuousSetPresheaf (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D] :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf D

/-- Continuous functions satisfy descent on the small pro-etale site.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: continuous functions form an fpqc sheaf by quotient-map descent. Restrict this
sheaf along the forgetful functor from the small pro-etale site, whose covering families
are fpqc covering families. This is step 1 of the node's proof. -/
theorem continuousSetPresheaf_isSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D) := by
  sorry

/-- The actual sheaf of continuous functions, with no sheafification of its sections.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨continuousSetPresheaf X D, continuousSetPresheaf_isSheaf X D⟩

/-- Postcomposition of continuous sections with a continuous coefficient map.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetSheafMap (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [TopologicalSpace E] (h : C(D, E)) :
    continuousSetSheaf X D ⟶ continuousSetSheaf X E :=
  ⟨{ app := fun _ ↦ ↾fun s ↦ h.comp s, naturality := fun _ _ _ ↦ rfl }⟩

/-- The existing Mathlib continuous-function sheaf functor on profinite sets.
Source: Hemo--Richarz--Scholbach, Example 3.1; Mathlib `topCatToSheafCompHausLike`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteFunctor :
    TopCat.{u + 1} ⥤ Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) :=
  topCatToSheafCompHausLike.{u + 1, u} (fun T ↦ TotallyDisconnectedSpace T)
    (fun _ _ f hf ↦ ((Profinite.effectiveEpi_tfae f).out 0 2).mp hf)

/-- The profinite coefficient sheaf `S ↦ C(S,D)`, using Mathlib's construction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteSheaf (D : Type (u + 1)) [TopologicalSpace D] :=
  continuousSetProfiniteFunctor.obj (TopCat.of D)

/-- The canonical label map from the spectrum of locally constant integer functions to S.
Source: Hemo--Richarz--Scholbach, Example 3.1, test-object construction; the spectrum
homeomorphism in `lem-weil-pbc-locally-constant-prime-spectrum`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetTestProjection (S : Profinite.{u}) :
    C((profiniteToProEt.obj S).left, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩

/-- The projection of a relative test object to its profinite label space.
Source: Hemo--Richarz--Scholbach, Example 3.1, relative test objects
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRelativeTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((Scheme.proEtaleBaseChange (toSpecZ X)).obj (profiniteToProEt.obj S)).left, S) :=
  (continuousSetTestProjection S).comp
    (pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X)).base.hom

/-- The composite adjunction defining the specified set inverse image from the point.
Source: Hemo--Richarz--Scholbach, Example 3.1; the point-pullback theorem
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetPointAdjunction (X : Scheme.{u}) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
    (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- Test-function normalization of the realization map: the adjoint sends b to b ∘ r.
Source: Hemo--Richarz--Scholbach, Example 3.1, explicit adjunction calculation
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def IsContinuousSetRealization (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
    (σ : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D) : Prop :=
  ∀ (S : Profinite.{u}) (b : C(S, D)),
    (((continuousSetPointAdjunction X).homEquiv _ _ σ).hom.app (op S)) b =
      b.comp (continuousSetRelativeTestProjection X S)

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
  sorry

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
  sorry

/-- The canonical continuous-function realization isomorphism.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRealizationIso (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D] :
    (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ≅
      continuousSetSheaf X D :=
  @asIso _ _ _ _ (continuousSetRealizationHom X D) (continuousSetRealizationHom_spec X D).2

/-- Naturality of the sectionwise direct-image comparison.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: for a morphism of test schemes the two maps to its pullback followed by the
first projection agree by the defining equation of the pullback map. Precomposing a
continuous function with these equal scheme maps gives the claimed equality (step 8). -/
theorem continuousSetDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] {U V : Y.ProEtᵒᵖ} (g : U ⟶ V) :
    (continuousSetPresheaf Y D).map g ≫
        (↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom) =
      (↾fun s ↦ s.comp (pullback.fst U.unop.hom f).base.hom) ≫
        ((Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
          (continuousSetSheaf X D)).obj.map g := by
  sorry

/-- Precomposition on the base-changed test object, as an actual sheaf morphism.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    continuousSetSheaf Y D ⟶
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj (continuousSetSheaf X D) :=
  ⟨{ app := fun V ↦ ↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom
     naturality := fun _ _ g ↦ continuousSetDirectImage_naturality f D g }⟩

/-- The canonical scheme-pullback comparison is the adjunct of precomposition.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following paragraph
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetPullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).obj (continuousSetSheaf Y D) ⟶
      continuousSetSheaf X D :=
  ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _).symm
    (continuousSetDirectImageMap f D)

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The map from the constant presheaf sends an element to the constant function.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetConstantPresheafMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (Functor.const X.ProEtᵒᵖ).obj D ⟶ continuousSetPresheaf X D where
  app U := ↾fun d ↦ ContinuousMap.const U.unop.left d
  naturality _ _ _ := rfl

/-- The canonical constant-sheaf comparison is the sheafification adjunct of constants.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetConstantMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj D ⟶
      continuousSetSheaf X D :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))).homEquiv _ _).symm
    (continuousSetConstantPresheafMap X D)

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
  sorry

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
  sorry

end AlgebraicGeometry.ProEtale
