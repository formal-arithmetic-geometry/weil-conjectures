/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceConstructibleTopologyComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.ConstructibleTopology

/-! # Open algebraic-space morphisms lift generalizations

Source: Rydh, Submersions and effective descent of étale morphisms, section 1,
paragraph before Remark (1.3), Remark (1.8), Remark (2.5)(2), and end of section 2;
Stacks Project, Morphisms, Tag 040F, lemma-open-generizing
(blueprint: lem-sfb-open-space-generization-lifting).

The quasi-separatedness hypotheses are absolute, using the existing affine-test
criterion. The topology is the existing atlas topology on field-valued point classes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open morphism between quasi-separated algebraic spaces lifts a generalization
through any specified source point, with no surjectivity or finite-presentation assumption.
Source: Rydh, section 1 before Remark (1.3), Remark (1.8), Remark (2.5)(2), and
end of section 2; Stacks Project, Tag 040F, lemma-open-generizing
(blueprint: lem-sfb-open-space-generization-lifting).

Proof:
1. By [lem-a1-space-affine-etale-cover], choose an affine étale chart `p : U → X`
   and a point `u₀` above `x₀`. By [lem-a1-space-point-open-calculus], `p` is open
   and continuous, so `h = f ∘ p` is open. The affine scheme `U` is qcqs by
   [lem-weil-pbc-affine-scheme-qcqs] and spectral by [lem-weil-pbc-qcqs-scheme-spectral].
2. Represent `y₁` by a field spectrum, using [def-a1-algebraic-space-point-classes]
   and [def-weil-affine-spectrum]. This spectrum is qcqs. Since `Y` is quasi-separated,
   [lem-sfb-space-qcqs-permanence] makes its map to `Y` quasi-compact.
   By [lem-sfb-space-quasicompact-constructible-closed], its singleton image is closed
   in the constructible topology. By [lem-sfb-space-constructible-topology-comparison],
   `h` is constructibly continuous, so its fibre `F` over `y₁` is constructibly closed.
3. By [def-weil-spectral-space], the quasi-compact open neighborhoods `B` of `u₀`
   form a basis. By [def-weil-pbc-constructible-topology], they are constructibly closed.
   Every finite intersection `V` of these neighborhoods contains `u₀`; for an empty
   intersection take `V = U`. Since `h(V)` is open and contains `f(x₀)`, the given
   closure condition makes it contain `y₁`. Thus `F ∩ V` is nonempty.
   By [lem-weil-pbc-spectral-constructible-topology-quasi-compact], the constructible
   topology of `U` is compact. The complements of `F` and all `B` therefore cannot
   cover `U`: a finite subcover would contradict these nonempty finite intersections.
   Choose `u₁` in `F` and every `B`. Then `h(u₁) = y₁` and `u₀ ∈ closure {u₁}`.
4. Put `x₁ = p(u₁)`. Its image is `y₁`. Continuity of `p`, from
   [lem-a1-space-point-open-calculus], implies `x₀ ∈ closure {x₁}`: the inverse image
   of any open neighborhood of `x₀` contains `u₀`, hence `u₁`. -/
theorem exists_generization_of_isOpenMap {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (_hX : IsAbsolutelyQuasiSeparated X) (_hY : IsAbsolutelyQuasiSeparated Y)
    (_hf : IsOpenMap (mapPoint f.hom.hom))
    (x₀ : Point X.obj.obj) (y₁ : Point Y.obj.obj)
    (_h : mapPoint f.hom.hom x₀ ∈ closure ({y₁} : Set (Point Y.obj.obj))) :
    ∃ x₁ : Point X.obj.obj,
      x₀ ∈ closure ({x₁} : Set (Point X.obj.obj)) ∧ mapPoint f.hom.hom x₁ = y₁ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
