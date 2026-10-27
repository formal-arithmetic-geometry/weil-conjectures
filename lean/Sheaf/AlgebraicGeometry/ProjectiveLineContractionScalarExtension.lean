/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Contraction of projective lines and scalar extension

Source: literature/stacks-project/schemes.tex, Tag 01JE (example-projective-line),
Tag 01I1 (lemma-morphism-into-affine), and morphisms.tex, Tag 01S1
(lemma-base-change-surjective).
(blueprint: lem-trf-projective-line-contraction-scalar-extension)

Scalar extension is the canonical functor `Over.pullback` on schemes over `Spec k`.
Its source is the fibre product of the projective line with `Spec L`, canonically
isomorphic to `ProjectiveLine (Spec (.of L))` by `ProjectiveSpace.isPullback_map`.
The component assertion uses an arbitrary reduced closed immersion with irreducible
component image; uniqueness of reduced induced closed subschemes identifies this
presentation with the reduced induced structure of that component.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveLine

/-- A singleton image of a projective line is a rational point, and the morphism
factors through its structure morphism.

Source: Stacks Project, Tags 01JE and 01I1.
(blueprint: lem-trf-projective-line-contraction-scalar-extension)

Proof: Step 1 computes global sections as k: on the two standard charts a compatible
pair satisfies u(t) = v(t⁻¹), so both are the same constant. Equivalently use
lem-sc-p1-monomial(i) at d = 0 and the transition 1 of def-sc-p1-standard.
Step 2 chooses an affine open containing x. The whole source maps into it, so
restrict r using def-weil-open-immersion. Its global section map A → Γ(P¹, O) = k
is a k-algebra map. By lem-weil-pbc-morphism-into-affine-scheme, the corresponding
Spec k → X composed with the structure morphism is r. The chart point t = 0
shows that this rational point has image exactly {x} (def-weil-field-valued-points).
-/
theorem exists_rationalPoint_of_range_singleton
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (r : ProjectiveLine (Spec (.of k)) ⟶ X) [r.IsOver (Spec (.of k))]
    (x : X) (hx : Set.range r = {x}) :
    ∃ a : Spec (.of k) ⟶ X,
      a ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)) ∧
      Set.range a = {x} ∧
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ a = r := by
  sorry

/-- A projective-line morphism has singleton image exactly when its scalar extension does.

Source: Stacks Project, Tags 01JE, 01JP and 01S1.
(blueprint: lem-trf-projective-line-contraction-scalar-extension)

Proof: Steps 1 and 2 give r = a p for a rational point a. Step 3 base changes this
factorization using def-pc-fibre-product. The scalar extension factors through
Spec L, which has one point (def-weil-affine-spectrum); its image is nonempty
because the chart point t = 0 base changes to an L-point. Thus its image is a
singleton. The source fibre product is P¹_L by
lem-nagata-affine-proj-scalar-extension and def-nagata-projective-space-base-change;
the relative ProjectiveLine model also supplies ProjectiveSpace.isPullback_map.
Step 4 uses lem-pc-field-extension-surjective and lem-weil-pbc-surjective-base-change:
the source projection π is surjective. The defining square q r_L = r π then gives
r(P¹_k) = q(r_L(P¹_L)), proving the converse.
-/
theorem range_singleton_scalarExtension_iff
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (r : ProjectiveLine (Spec (.of k)) ⟶ X) [r.IsOver (Spec (.of k))] :
    (∃ y : pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      Set.range (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
        (r.asOver (Spec (.of k)))).left) = {y}) ↔
    ∃ x : X, Set.range r = {x} := by
  sorry

/-- The factorization and scalar-extension criterion apply to reduced closed components
isomorphic over k to the projective line.

Source: Stacks Project, Tags 01JE, 01JP and 01S1, applied to the component restriction.
(blueprint: lem-trf-projective-line-contraction-scalar-extension)

Proof: Step 5 chooses the given k-isomorphism e : P¹_k ≅ R and applies Steps 1--4
to e.hom ≫ i ≫ f. Isomorphisms are surjective, so the singleton-image condition
is unchanged. Since e respects k, its inverse also does, and the factorization
transports back to R. The base changes of e and its inverse are inverse by
functoriality of def-pc-fibre-product. Thus the base-changed images also agree,
which proves the criterion for f restricted to R. A reduced closed immersion
with component image is the reduced induced structure by
lem-weil-pbc-reduced-induced-closed-subscheme.
-/
theorem component_range_singleton_scalarExtension
    (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (C X R : Scheme.{u}) [C.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [R.Over (Spec (.of k))] [IsReduced R]
    (f : C ⟶ X) [f.IsOver (Spec (.of k))]
    (i : R ⟶ C) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hi : Set.range i ∈ irreducibleComponents C)
    (e : ProjectiveLine (Spec (.of k)) ≅ R) [e.hom.IsOver (Spec (.of k))] :
    (∀ x : X, Set.range (i ≫ f) = {x} →
      ∃ a : Spec (.of k) ⟶ X,
        a ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)) ∧
        Set.range a = {x} ∧ (R ↘ Spec (.of k)) ≫ a = i ≫ f) ∧
    ((∃ y : pullback (C := Scheme.{u}) (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      Set.range (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
        ((i ≫ f).asOver (Spec (.of k)))).left) = {y}) ↔
      ∃ x : X, Set.range (i ≫ f) = {x}) := by
  sorry

end AlgebraicGeometry.ProjectiveLine
