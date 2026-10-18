/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.Category.Profinite.Limits
import Sheaf.Topology.FiniteQuotientFiberProduct
import Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.Paper.ProfiniteTestObjectFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Relative profinite tests over an affine scheme's component space

Source: Hemo--Richarz--Scholbach, paragraph preceding (4.1) and its factorization sentence;
Bhatt--Scholze, proof and more precise statement of Lemma 2.2.8
(blueprint: lem-zl-component-relative-profinite-site).

The functor in the theorem is specified by a universal property, not by an arbitrary
choice of affine schemes. Its finite stages are coproducts of actual restricted open
subschemes. Its image of every finite-clopen presentation is a limit cone over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

/-- The quotient by connected components, with its quotient topology, bundled as profinite.
Source: Hemo--Richarz--Scholbach, before (4.1); Stacks, Tag 0906
(blueprint: lem-zl-component-relative-profinite-site). -/
def affineComponentSpace (T : Scheme.{u}) [IsAffine T] : Profinite.{u} := by
  letI : SpectralSpace T := {}
  exact @Profinite.of (ConnectedComponents T) _
    (spectralSpace_connectedComponents_profinite (T := T)).1
    (spectralSpace_connectedComponents_profinite (T := T)).2.1
    (spectralSpace_connectedComponents_profinite (T := T)).2.2

/-- A finite stage over the component space: pull back a map of finite sets along a
finite clopen quotient of the base. The quotient's surjectivity is imposed in the theorem.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
noncomputable def componentFiniteStage {S : Profinite.{u}} (A C : FintypeCat.{u})
    (q : S ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C) : Over S :=
  Over.mk (pullback.fst q (FintypeCat.toProfinite.map f))

/-- Exactly the allowed finite stages, including isomorphic presentations.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
def IsComponentFiniteStage {S : Profinite.{u}} (E : Over S) : Prop :=
  ∃ (A C : FintypeCat.{u}) (q : S ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C),
    Function.Surjective q ∧ Nonempty (E ≅ componentFiniteStage A C q f)

/-- The open-and-closed part of the affine base belonging to one finite block. Its
associated scheme carries the restriction of the structure sheaf, via `Scheme.Opens`.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
def componentFiniteOpen (T : Scheme.{u}) [IsAffine T] (A C : FintypeCat.{u})
    (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C)
    (a : A) : T.Opens :=
  ⟨{t | q (ConnectedComponents.mk t) = f a},
    (isOpen_discrete ({f a} : Set (FintypeCat.toProfinite.obj C))).preimage
      (q.hom.hom.continuous.comp ConnectedComponents.continuous_coe)⟩

/-- The finite scheme stage is the disjoint union of the actual clopen subschemes,
including repeated blocks as separate copies and the empty coproduct.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
noncomputable def componentFiniteScheme (T : Scheme.{u}) [IsAffine T]
    (A C : FintypeCat.{u})
    (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C) : Over T :=
  ∐ fun a : A => Over.mk (componentFiniteOpen T A C q f a).ι

/-- The relative profinite test functor, its presentation characterization, and the
factorization of the condensed-point morphism.

Source: Hemo--Richarz--Scholbach, paragraph before (4.1) and factorization after it;
Bhatt--Scholze, Lemma 2.2.8 and its more precise statement
(blueprint: lem-zl-component-relative-profinite-site).

Proof for stage 3 (the twelve steps of the DAG node).
1. Affine schemes are qcqs (`lem-weil-pbc-affine-scheme-qcqs`) and therefore spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`). Apply `lem-pe-spectral-components-profinite`
   to the base and every affine test scheme.
2. Apply `lem-sfb-finite-quotient-fiber-product` to E -> S <- S, using compatible
   finite clopen partitions. The stages are S times A over C, as above. Common
   refinement makes their small nonempty indexing category cofiltered.
3. The cited partition-limit homeomorphism identifies this limit with E over S:
   a compatible tuple has a common S-coordinate and compatible finite block coordinates.
   Those determine exactly one point of E, continuously, including for E empty.
4. `lem-zl-affine-component-site-projection` gives the affine ind-etale scheme with
   space |T| times E over S and inverse-image structure sheaf. On finite stages this
   is the displayed disjoint union of clopen restrictions. Ind-etale implies weakly
   etale (`lem-weil-pbc-ind-etale-stability`); maps between affine schemes are affine
   (`lem-weil-pbc-morphism-affine-schemes-affine`).
5. A map W -> T together with a continuous map W -> E over S gives the unique map
   to that ringed space: its structure-sheaf map comes from W -> T by inverse-image
   adjunction, and is local on stalks. Conversely project to E. These are inverse;
   the map to E factors uniquely through the connected-component quotient.
6. For any permitted presentation, this mapping property and the profinite limit
   identify maps from affine W with compatible maps to the finite scheme stages.
   Glue the unique lifts on affine open covers to obtain the limit property for all W.
7. Uniqueness of limits identifies every presentation with the same functor value,
   respecting all projections. The mapping property makes these comparisons natural.
8. The component-site projection of step 4 preserves finite limits and coverings
   and induces the geometric morphism with direct image precomposition by F.
9. The space and inverse-image structure sheaf both split over finite disjoint unions,
   proving preservation of finite coproducts, including the empty family.
10. At S times K -> S the construction gives T[K], naturally in K, by the finite
    stage description and `lem-weil-pbc-profinite-test-object-functor`.
11. `lem-trf-slice-subtopos-site-presentation` gives the slice inverse image by
    restriction, and direct image at K by evaluation at S times K -> S. The definition
    of `lem-weil-pbc-profinite-point-pullback`, `def-weil-proetale-inverse-image`, and
    `def-sfb-profinite-test-objects` gives the absolute direct image by evaluation at T[K].
12. Step 10 identifies the composite direct image with the absolute one, naturally
    in K and the sheaf. Its adjunction mate, with `def-trf-geometric-morphism`'s
    composition convention, gives the displayed inverse-image isomorphism. -/
theorem component_relative_profinite_site (T : Scheme.{u}) [IsAffine T] :
    ∃ F : Over (affineComponentSpace T) ⥤ T.ProEt,
      (∀ E : Over (affineComponentSpace T), IsAffine (F.obj E).left) ∧
      (∃ p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left),
        (∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
          E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x)) ∧
        (∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E') (x : (F.obj E).left),
          p E' ((F.map a).left x) = a.left (p E x)) ∧
        ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
          (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
          ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
            ∀ w : W.left, p E (m.left w) = g w) ∧
      (∀ (A C : FintypeCat.{u})
        (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C),
        Function.Surjective q →
        Nonempty ((Scheme.ProEt.forget T).obj (F.obj (componentFiniteStage A C q f)) ≅
          componentFiniteScheme T A C q f)) ∧
      (∀ E : Over (affineComponentSpace T),
        ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
          (D : I ⥤ Over (affineComponentSpace T)) (c : Cone D),
          c.pt = E ∧ Nonempty (IsLimit c) ∧ ∀ i : I, IsComponentFiniteStage (D.obj i)) ∧
      (∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
        (D : I ⥤ Over (affineComponentSpace T)) (c : Cone D),
        (∀ i : I, IsComponentFiniteStage (D.obj i)) → IsLimit c →
        Nonempty (IsLimit ((F ⋙ Scheme.ProEt.forget T).mapCone c))) ∧
      PreservesFiniteLimits F ∧
      (∀ (A : Type u) [Finite A], PreservesColimitsOfShape (Discrete A) F) ∧
      (∀ (A : Type u) [Finite A] (E : A → Over (affineComponentSpace T))
        (E₀ : Over (affineComponentSpace T)) (f : ∀ a : A, E a ⟶ E₀),
        (∀ x : E₀.left, ∃ (a : A) (y : (E a).left), (f a).left y = x) →
        Presieve.ofArrows (fun a : A => F.obj (E a)) (fun a : A => F.map (f a)) ∈
          Scheme.ProEt.precoverage T (F.obj E₀)) ∧
      ∃ π : GeometricMorphism
          (Sheaf (Scheme.ProEt.topology T) (Type (u + 1)))
          (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
            (Type (u + 1))),
        Nonempty (π.direct ⋙
            sheafToPresheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
              (Type (u + 1)) ≅
          sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)) ⋙
            (Functor.whiskeringLeft _ _ _).obj F.op) ∧
        ∃ q : GeometricMorphism
            (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
              (Type (u + 1)))
            (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
          q.inverse = (coherentTopology Profinite.{u}).overPullback
            (Type (u + 1)) (affineComponentSpace T) ∧
          Nonempty (profinitePointSetSchemeInverseImage T ≅ (π.comp q).inverse) := by
  sorry

end AlgebraicGeometry.ProEtale
