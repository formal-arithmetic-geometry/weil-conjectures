/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# Étale-local finite presentation of a module

Source: Stacks Project, flat.tex, Tag 057T, proof of (1) iff (4)
(blueprint: lem-trf-etale-module-finite-presentation-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite presentation of a quasi-coherent module is local at an étale neighbourhood.

Source: Stacks Project, flat.tex, Tag 057T, proof of (1) iff (4)
(blueprint: lem-trf-etale-module-finite-presentation-local).

Proof: For the forward implication, restrict a neighbourhood of `x` and apply
finite-presentation preservation under tensor pullback to the restricted étale map.
The inverse image of that neighbourhood contains `x'` because `g x' = x`, and the
composition formula for `tensorPullback` identifies the resulting module with the
restriction of `g^* M`. Conversely, an open neighbourhood of `x'` maps to an open
neighbourhood of `x` because `g` is étale and hence open. Restricting `g` to that
image gives a surjective étale (therefore faithfully flat) covering. Finite
presentation descends along this fpqc covering, and the tensor-pullback composition
formula identifies its pullback with the given restriction of `g^* M`. The residue
field isomorphism is retained as part of the marked étale-neighbourhood hypothesis.
The proof uses `lem-pc-tensor-pullback-finite-presentation`,
`lem-weil-pbc-etale-morphism-open-map`, `lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-etale-covering-affine-refinement`, and `lem-pc-fpqc-descent`.
-/
theorem etale_module_finite_presentation_local
    {X X' : Scheme.{u}} (g : X' ⟶ X) (x : X) (x' : X')
    (_hx : g x' = x) [Etale g] [IsIso (g.residueFieldMap x')]
    (M : X.Modules) [M.IsQuasicoherent] :
    (∃ U : X.Opens, x ∈ U ∧ (M.over U).IsFinitePresentation) ↔
      (∃ U' : X'.Opens, x' ∈ U' ∧
        ((tensorPullback g).obj M |>.over U').IsFinitePresentation) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
