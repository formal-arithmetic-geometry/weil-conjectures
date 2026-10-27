/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.LimitResidueField
import WeilConjectures.AlgebraicGeometry.ProperBasic

/-! # An ample limit fibre gives an ample neighbourhood at a Noetherian stage

Source: Stacks Project, More on Morphisms, Tag 0D2S, lemma-ample-in-neighbourhood,
proof: descent of fibre ampleness and the Noetherian affine neighbourhood.
(blueprint: lem-trf-model-fibre-ample-open).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module ample on a limit fibre becomes ample on a stage fibre and
on the inverse image of an affine neighbourhood at that same stage.

Source: Stacks Project, More on Morphisms, Tag 0D2S, lemma-ample-in-neighbourhood,
middle paragraph of the proof; Limits, Tags 0CUG and 09MT; Cohomology of Schemes,
Tag 0D2N. (blueprint: lem-trf-model-fibre-ample-open).

Proof:
1. Apply lem-weil-pbc-limit-residue-field to the base diagram and the point x.
   The spectra of the stage residue fields have limit Spec κ(x), compatibly with
   their maps to the base schemes. Form the stage fibres by def-pc-scheme-fibre
   and def-pc-fibre-product; their transition maps satisfy the functor laws.
2. Proper base change (lem-weil-pbc-proper-base-change), pqf-lem-proper-basic and
   lem-pc-separated-quasi-separated make the stage fibres quasi-compact and
   quasi-separated.
3. Cover a stage fibre by affine fibre-product charts. Both transition maps in
   the original diagrams are affine. The inverse image of each chart is the
   corresponding affine fibre product at the later stage, by
   lem-weil-pbc-fibre-product-affine-spectra. Apply pqf-lem-affine-local-target to
   conclude that the fibre transitions are affine; no Cartesian transition
   square for the original proper morphisms is required.
4. The fibre system has a limit by lem-weil-pbc-limit-affine-transition.
   The universal properties and lem-kun-fibre-product-limits identify it with
   the fibre of f at x, compatibly with the projections.
5. Pullback composition and lem-weil-pbc-invertible-pullback-tensor identify the
   stage line bundles on these fibres with the pullbacks of the initial fibre
   line bundle, and identify the limit pullback with the restriction of M.
   Apply lem-trf-ample-affine-limit-descent to obtain an ample stage fibre.
6. Apply lem-trf-noetherian-fibre-ample-neighbourhood to that original proper
   stage morphism over its Noetherian base and the pulled-back invertible module.
   It gives the required affine neighbourhood with absolute ampleness, retaining
   the stage-fibre ampleness from step 5.
-/
theorem exists_affine_isAmple_of_limit_fiber
    {I : Type u} [PartialOrder I] [OrderBot I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DY DX : Iᵒᵖ ⥤ Scheme.{u}) (φ : DY ⟶ DX)
    [∀ i : I, IsProper (φ.app (op i))]
    (hYaff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (DY.map (homOfLE h).op))
    (hXaff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (DX.map (homOfLE h).op))
    [∀ i : I, IsLocallyNoetherian (DX.obj (op i))]
    [∀ i : I, CompactSpace (DX.obj (op i))]
    (cY : Cone DY) (hcY : IsLimit cY) (cX : Cone DX) (hcX : IsLimit cX)
    (f : cY.pt ⟶ cX.pt)
    (hf : ∀ i : I, cY.π.app (op i) ≫ φ.app (op i) = f ≫ cX.π.app (op i))
    (M₀ : (DY.obj (op (⊥ : I))).Modules) [M₀.IsInvertible]
    (M : cY.pt.Modules) [M.IsInvertible]
    (eM : (tensorPullback (cY.π.app (op (⊥ : I)))).obj M₀ ≅ M)
    (x : cX.pt)
    (hM : ∃ h : ((tensorPullback (f.fiberι x)).obj M).IsInvertible,
      @IsAmple (f.fiber x) ((tensorPullback (f.fiberι x)).obj M) h) :
    ∃ (i : I) (V : (DX.obj (op i)).Opens),
      cX.π.app (op i) x ∈ V ∧ IsAffineOpen V ∧
      (∃ h : ((tensorPullback ((φ.app (op i)).fiberι (cX.π.app (op i) x))).obj
          ((tensorPullback (DY.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀)).IsInvertible,
        @IsAmple ((φ.app (op i)).fiber (cX.π.app (op i) x))
          ((tensorPullback ((φ.app (op i)).fiberι (cX.π.app (op i) x))).obj
            ((tensorPullback (DY.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀)) h) ∧
      (∃ h : ((tensorPullback ((φ.app (op i)) ⁻¹ᵁ V).ι).obj
          ((tensorPullback (DY.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀)).IsInvertible,
        @IsAmple ((φ.app (op i)) ⁻¹ᵁ V).toScheme
          ((tensorPullback ((φ.app (op i)) ⁻¹ᵁ V).ι).obj
            ((tensorPullback (DY.map (homOfLE (bot_le : (⊥ : I) ≤ i)).op)).obj M₀)) h) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
