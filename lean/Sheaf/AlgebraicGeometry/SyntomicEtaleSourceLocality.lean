/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.TraceFormula.LciPointwiseCriterion
public import Sheaf.AlgebraicGeometry.CompleteIntersectionFibres
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.RingTheory.CompleteIntersectionLocalAlgebra
import Sheaf.RingTheory.FlatLocalCompleteIntersectionSourceFibre

/-!
# Syntomicity under étale covers of the source

Source: Stacks Project, Descent, Tags 036S and 05B7; Morphisms, Tags 02GQ,
01UE and 01UG (blueprint: lem-sfb-syntomic-etale-source-locality).

Syntomicity is expressed as flatness, local finite presentation, and the existing
`Scheme.Hom.HasCompleteIntersectionFibres` condition. The latter tests all fibre
local rings over their canonical residue base fields, as in `lci_pointwise_criterion`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Syntomicity ascends along an étale source map and descends along any jointly
surjective set-indexed family of étale source maps. No quasi-compactness, separation,
Noetherianity, or field-base hypothesis is imposed. The empty covering family is allowed.

Source: Stacks Project, Descent, Tag 036S (lemma-syntomic-syntomic-local-source),
with the fibrewise argument of Tag 05B7 (lemma-syntomic-permanence); Morphisms,
Tags 02GQ (lemma-etale-syntomic), 01UE and 01UG
(blueprint: lem-sfb-syntomic-etale-source-locality).

Proof:
1. Apply lem-sfb-scheme-etale-source-target-properties to flatness and local finite
   presentation. Both properties ascend along an étale source map and descend along
   the jointly surjective family. It remains to test the ordinary fibre local rings.
2. For a locally finitely presented map, choose compatible affine source and target
   opens. By lem-weil-pbc-lfp-affine-opens-finite-presentation their ring map is finitely
   presented. Pulling back the source opens gives affine fibre charts Spec(D ⊗_R κ(s))
   by lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-open-immersion-base-change. These are finitely presented over κ(s) by
   lem-weil-pbc-finite-presentation-base-change-composition, hence finite type. Their
   stalks are prime localizations by lem-weil-pbc-affine-open-stalk-localization,
   so are essentially finite type by def-weil-pbc-essentially-finite-type-algebra.
3. Base change the étale source maps to a fixed fibre, using
   lem-weil-pbc-etale-scheme-base-change; in the covering case use
   lem-weil-pbc-etale-covering-base-change for joint surjectivity. The universal property
   def-pc-fibre-product identifies U ×_X X_s with U_s, by (u,(h(u),t)) ↔ (u,t).
   At corresponding points the resulting map A → B of local κ(s)-algebras is flat,
   by def-weil-etale-morphism and def-weil-flat-morphism.
4. The closed fibre B/m_A B is κ(z). On affine neighbourhoods this follows from
   lem-weil-pbc-affine-open-stalk-localization, the fibre charts given by
   lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-fibre-ring-local-ring-iso, and
   lem-weil-pbc-etale-fibre-discrete-separable-points. These identifications preserve
   the original κ(s)-action. The field is essentially finite type: a quotient of
   W⁻¹D is the localization of D/J at the image of W, and the images of finite
   generators generate D/J. It is regular local of dimension zero, hence a complete
   intersection by its identity presentation and the empty regular sequence in
   def-trf-complete-intersection-local-algebra. Now
   lem-sfb-flat-local-ci-source-fibre gives that B is a complete intersection over
   κ(s) if and only if A is.
5. For ascent apply step 4 at every point of U_s. For descent, joint surjectivity on
   each fibre supplies a point above every point of X_s; apply step 4 there. Combine
   with step 1. Empty fibres have no stalks to test. If X is empty all three
   conditions hold vacuously, so an empty covering family is included.
-/
theorem syntomic_etale_source_locality {X S : Scheme.{u}} (f : X ⟶ S) :
    ((Flat f ∧ LocallyOfFinitePresentation f ∧ f.HasCompleteIntersectionFibres) →
      ∀ (U : Scheme.{u}) (h : U ⟶ X), Etale h →
        Flat (h ≫ f) ∧ LocallyOfFinitePresentation (h ≫ f) ∧
          (h ≫ f).HasCompleteIntersectionFibres) ∧
    (∀ (I : Type v) (U : I → Scheme.{u}) (h : ∀ i : I, U i ⟶ X),
      (∀ i : I, Etale (h i)) →
      (∀ x : X, ∃ (i : I) (z : U i), h i z = x) →
      (∀ i : I, Flat (h i ≫ f) ∧ LocallyOfFinitePresentation (h i ≫ f) ∧
        (h i ≫ f).HasCompleteIntersectionFibres) →
      Flat f ∧ LocallyOfFinitePresentation f ∧ f.HasCompleteIntersectionFibres) := by
  sorry

end AlgebraicGeometry
