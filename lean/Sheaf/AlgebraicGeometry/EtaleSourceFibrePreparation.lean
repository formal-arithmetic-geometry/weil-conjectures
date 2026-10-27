/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.RingTheory.FlatnessFaithfullyFlatExtension
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.FiniteStability

/-!
# Étale source descent and preparation of geometric fibres

Source: Stacks Project, Curves, Tag 0C5D, structural descent and taking fibres;
Descent, Tags 036K and 036N; Algebra, Tag 05G5 (4); Morphisms, Tags 01TQ and 01T6
(blueprint: lem-trf-etale-source-fibre-preparation).

The three statements give descent and fibre properties, the formula for every affine
chart, and coverage by such charts, respectively. The canonical fibre comparison is
Mathlib's `pullbackRightPullbackFstIso`, with its direction reversed.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Flatness and local finite presentation descend through an étale covering of the source.
The geometric fibres have the canonical projection-preserving comparisons, an étale covering,
and locally finite type, locally Noetherian sources.

Source: Stacks Project, Tags 0C5D, 036K, 036N and 01T6
(blueprint: lem-trf-etale-source-fibre-preparation).

Proof, node steps 1--4 and 6:
1. Étale maps are flat and locally finitely presented. Composition of flat stalk maps
   (`lem-weil-pbc-flat-ring-map-comp`) proves forward flatness.
2. Choose a point above each source point. The flat local stalk map is faithfully flat
   (`lem-weil-pbc-flat-local-hom-faithfully-flat`). Apply
   `lem-trf-flatness-faithfully-flat-extension` to the stalk tower and its middle ring,
   using the multiplication isomorphism from its scalar extension to the last ring.
3. Apply `lem-trf-lfp-fppf-source-locality` to the given family, independently of flatness
   of `f`. Under either resulting finite-presentation condition all composites are lfp.
4. The pullback universal property gives the comparison and its inverse. Its projections
   characterize it uniquely. Base change of the étale covering gives étaleness and joint
   surjectivity of the maps to the fibre, after exchanging pullback factors.
5. Use the affine charts in the next two statements. Finite presentation implies finite
   type. A field is Noetherian, so `pqf-lem-locnoeth-lft` gives local Noetherianity.
   No finite covering, separation, or hypothesis on the base is used. Empty sources,
   empty fibres, and the empty cover of the empty source satisfy the pointwise clauses. -/
theorem etale_source_fibre_preparation
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (U : I → Scheme.{u}) (h : ∀ i : I, U i ⟶ X)
    [∀ i : I, Etale (h i)]
    (hjoint : ∀ x : X, ∃ (i : I) (y : U i), h i y = x) :
    (Flat f ↔ ∀ i : I, Flat (h i ≫ f)) ∧
    (LocallyOfFinitePresentation f ↔ ∀ i : I, LocallyOfFinitePresentation (h i ≫ f)) ∧
    (LocallyOfFinitePresentation f →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
        (∀ i : I, ∃! a : pullback (h i ≫ f) g ≅ pullback (h i) (pullback.fst f g),
          a.hom ≫ pullback.fst (h i) (pullback.fst f g) = pullback.fst (h i ≫ f) g ∧
          a.hom ≫ pullback.snd (h i) (pullback.fst f g) ≫ pullback.snd f g =
            pullback.snd (h i ≫ f) g) ∧
        (∀ i : I, Etale ((pullbackRightPullbackFstIso f g (h i)).inv ≫
          pullback.snd (h i) (pullback.fst f g))) ∧
        (∀ x : (pullback f g : Scheme.{u}), ∃ (i : I) (y : (pullback (h i ≫ f) g : Scheme.{u})),
          ((pullbackRightPullbackFstIso f g (h i)).inv ≫
            pullback.snd (h i) (pullback.fst f g)) y = x) ∧
        LocallyOfFiniteType (pullback.snd f g) ∧ IsLocallyNoetherian (pullback f g) ∧
        ∀ i : I, LocallyOfFiniteType (pullback.snd (h i ≫ f) g) ∧
          IsLocallyNoetherian (pullback (h i ≫ f) g)) := by
  sorry

/-- Every specified finite-presentation affine chart pulls back to the spectrum of its
scalar-extension algebra, with the prescribed projections and finite presentation over Ω.
Apply this to `f` and to every composite from the source covering.

Source: Stacks Project, Tags 0C5D, 01I4 and 05G5 (4)
(blueprint: lem-trf-etale-source-fibre-preparation).

Proof, node step 5: the chart compatibility and factorization of the field point identify
its pullback over `S` with its pullback over `Spec R`, by the universal property of
`def-pc-fibre-product`. Exchange the two factors and apply
`lem-weil-pbc-fibre-product-affine-spectra` in the order Ω, A. Its projection formulas
identify both maps. `lem-weil-pbc-finite-presentation-base-change-composition`, clause (1),
makes Ω ⊗[R] A finitely presented over Ω. This works for every given chart, including
an empty affine chart (the zero ring), with no nonemptiness hypothesis. -/
theorem geometric_fibre_finite_presentation_affine_chart
    {X S : Scheme.{u}} (f : X ⟶ S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra R Ω]
    (a : Spec (.of A) ⟶ X) (b : Spec (.of R) ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion b] [Algebra.FinitePresentation R A]
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b)
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ b) :
    Algebra.FinitePresentation Ω (Ω ⊗[R] A) ∧
    ∃ e : pullback (a ≫ f) g ≅ Spec (.of (Ω ⊗[R] A)),
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom) =
          pullback.fst (a ≫ f) g ∧
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[R] A))) =
        pullback.snd (a ≫ f) g := by
  sorry

/-- The finite-presentation affine charts through which a geometric point factors cover
its fibre. Taking `f` to be each composite `h i ≫ f` gives the same covering for each `D i`.

Source: Stacks Project, Tags 0C5D, 01I4, 01JY and 01TQ
(blueprint: lem-trf-etale-source-fibre-preparation).

Proof, node step 5: choose an affine open neighbourhood `Spec R` of the image of the
one-point scheme `Spec Ω`, using `lem-weil-pbc-affine-opens-basis`; the field point
factors through it. Cover its inverse image by affine opens `Spec A`. By
`lem-weil-pbc-lfp-affine-opens-finite-presentation` the induced R-algebras are finitely
presented. Base change of these open immersions is open, by
`lem-weil-pbc-open-immersion-base-change`; their images are the inverse images of the
chart images and cover the fibre. The canonical pullback-pasting isomorphism identifies
the resulting open chart with the pullback over S appearing below. The preceding
statement gives its tensor-product formula. Empty fibres impose no pointwise choices;
no quasi-compactness or separation hypothesis is used. -/
theorem geometric_fibre_finite_presentation_affine_charts_cover
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S) :
    ∀ x : (pullback f g : Scheme.{u}), ∃ (R A : CommRingCat.{u})
      (_ : Algebra R A) (_ : Algebra R Ω)
      (a : Spec A ⟶ X) (b : Spec R ⟶ S),
      IsOpenImmersion a ∧ IsOpenImmersion b ∧ Algebra.FinitePresentation R A ∧
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b ∧
      g = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ b ∧
      ∃ y : (pullback (a ≫ f) g : Scheme.{u}),
        ((pullbackRightPullbackFstIso f g a).inv ≫
          pullback.snd a (pullback.fst f g)) y = x := by
  sorry

end AlgebraicGeometry
