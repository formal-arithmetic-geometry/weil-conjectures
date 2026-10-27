/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.StrictTransformComponentClosures
import Sheaf.AlgebraicGeometry.HilbertSamuelNearComponentIncidence

/-! # Component dimensions at a Hilbert--Samuel near point

Source: ILO, Expose VIII, 2.3.13, printed p.94, synchronization discussion;
Bierstone--Milman--Temkin, arXiv:0905.3580, section 6.3
(blueprint: lem-trf-hilbert-samuel-equality-component-rigidity).

We use the scheme-theoretic strict transform of the identity in the intrinsic blowup.
By Stacks Tag 080E (`exists_blowup_comap_iso_strictTransform`), this is the intrinsic
blowup and hence also the strict transform in any ambient blowup with the given center.
Thus the formulation does not require the locally closed embedding to be globally closed,
or impose a choice of ambient extension of the center. The dimension sets are written out
using the existing topological Krull dimension of component subspaces.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Equality of normalized Hilbert--Samuel sequences preserves the set of dimensions of
components through the points. Source: ILO VIII 2.3.13, printed p.94; BMT section 6.3
(blueprint: lem-trf-hilbert-samuel-equality-component-rigidity).

`I.subscheme` is the smooth closed center. Its locally constant function is the restriction
of `function (i ≫ p)` from X, not the Hilbert--Samuel function of the center itself.
The strict transform is scheme-theoretic, and is canonically the blowup of X in I
(Stacks Tag 080E). No component of X is assumed to avoid the center.

Proof, following the five steps of the live Q70 node:
1. Shrink to an affine neighborhood of x, removing components not through x. Finite type
   over Q implies Noetherianity and finitely many components
   (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-noetherian-finitely-many-components`). Apply
   `lem-trf-hilbert-samuel-near-normal-cone`: the normal cone is flat over the center and
   its fiber is B[T_1,...,T_e], e >= 1, with y on the linear vertex. This includes nonclosed y.
2. Components through x correspond to minimal primes of its local ring
   (`lem-weil-pbc-spec-irreducible-components-minimal-primes`). Apply
   `lem-trf-normal-cone-directrix-minimal-primes` to each minimal prime: the vertex quotient
   factors through every component normal cone, so y belongs to each component cone's Proj.
3. By `thm-nagata-strict-transform-is-blowup`, a component strict transform is its intrinsic
   blowup. Its Rees algebra (`def-nagata-affine-blowup`, `def-nagata-rees-algebra`) has fiber
   Proj equal to that component normal-cone Proj, by
   `lemma-nagata-relative-proj-base-change-arbitrary`. Hence y lies on every component strict
   transform. A component contained in the center would have empty such Proj; equality
   rules this out as a consequence, without excluding it from the hypotheses.
4. By `def-nagata-strict-transform` and `lemma-nagata-strict-transform-over-complement`,
   the strict transform is the reduced closure of X minus the center. Closure of its finite
   component decomposition gives exactly the distinct strict transforms of the surviving
   components. Components through y map to components through x, and step 3 gives the converse.
5. Corresponding components have the same function field by
   `lemma-nagata-strict-transform-over-complement`. Blowup charts are of finite type
   (`thm-nagata-global-blowup-proper`, `def-weil-proper-morphism`). Apply
   `lem-weil-pbc-finite-type-domain-dimension-trdeg` to identify each component's dimension
   with its function-field transcendence degree. The bijection in step 4 therefore gives
   equality of the two sets of dimensions. -/
theorem component_dimensions_eq_of_function_eq {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ i ≫ p)]
    (hconstant : IsLocallyConstant (fun c : I.subscheme ↦ function (i ≫ p) (I.subschemeι c)))
    (x : X) (hx : x ∈ I.support) (y : I.strictTransform (𝟙 X))
    (hy : strictTransformToSource (𝟙 X) I.blowupMap I.support.compl y = x)
    (heq : function
      (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ≫ i ≫ p) y =
        function (i ≫ p) x) :
    {d : WithBot ℕ∞ | ∃ W : Set (I.strictTransform (𝟙 X)),
      W ∈ irreducibleComponents (I.strictTransform (𝟙 X)) ∧ y ∈ W ∧
        topologicalKrullDim W = d} =
    {d : WithBot ℕ∞ | ∃ W : Set X,
      W ∈ irreducibleComponents X ∧ x ∈ W ∧ topologicalKrullDim W = d} := by
  obtain ⟨hcomponents, hdim⟩ := strictTransform_component_closures (i ≫ p) I
  have hincidence (W : Set X) (hW : W ∈ irreducibleComponents X) (hxW : x ∈ W) :
      y ∈ closure
        (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹'
          (W \ (I.support : Set X))) := by
    apply near_point_mem_component_closure p i I hconstant y
    · simpa only [hy] using hx
    · simpa only [hy] using heq
    · exact hW
    · simpa only [hy] using hxW
  ext d
  constructor
  · rintro ⟨W', hW', hyW', hd⟩
    obtain ⟨W, hW, hWU, rfl⟩ := (hcomponents W').mp hW'
    refine ⟨W, hW, ?_, (hdim W hW hWU).symm.trans hd⟩
    rw [← hy]
    have hsub : closure
        (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹'
          (W \ (I.support : Set X))) ⊆
        strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹' W :=
      closure_minimal (fun _ h ↦ h.1)
        ((isClosed_of_mem_irreducibleComponents W hW).preimage
          (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl).continuous)
    exact hsub hyW'
  · rintro ⟨W, hW, hxW, hd⟩
    have hyW := hincidence W hW hxW
    have hWU : (W \ (I.support : Set X)).Nonempty := by
      by_contra h
      have hzero : W \ (I.support : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp only [hzero, Set.preimage_empty, closure_empty, Set.mem_empty_iff_false] at hyW
    exact ⟨_, (hcomponents _).mpr ⟨W, hW, hWU, rfl⟩, hyW, (hdim W hW hWU).trans hd⟩

end AlgebraicGeometry.HilbertSamuel
