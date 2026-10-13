/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles
import Sheaf.AlgebraicGeometry.PicardDirectImageTestSections

/-! # Realizing scalar cycles of a fixed perfect direct-image model

Source: Stacks Project, Tag 0BF2, the lifting of a degree-zero cycle through the
base-change comparison. (blueprint: lem-sc-picard-scalar-model-cycles-realization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- Comparing the two derived Hom interfaces unfolds the chosen derived pullback functors.
/-- A connective strictly perfect model with a scalar degree-zero basis realizes its
scalar cycles as sections, compatibly with restriction to the marked residue fibre.
This fixes a model; it constructs no degree-one map and assumes no H¹ injectivity.
Source: Stacks Project, Tag 0BF2, the paragraph after the chain-map calculation,
with the arbitrary base-change comparison of Tag 0B91.
(blueprint: lem-sc-picard-scalar-model-cycles-realization)

Proof: On the affine U a strictly perfect complex has quasi-coherent finite-projective
terms. The supplied section bases therefore sheafify to bases of K⁰ and K¹ on U.
The equality hd identifies its outgoing differential with multiplication by d. Restrict
to V: a scalar a annihilating the restricted vector is a degree-zero cycle. There are
no degree-minus-one terms, so there are no degree-zero boundaries. Apply the comparison
hE and canonical open base change for the relatively flat invertible module L. Degree-zero
homology of the direct image is ordinary pushforward, so this cycle gives a section σ
on X_V. Since hdw makes the residue differential zero, the residue degree-zero homology
is the one-dimensional scalar term. The same comparison at Spec κ(w) gives the additive
equivalence c with fibre sections. The comparison is compatible with the adjunction
unit: canonical derived base change is the mate of pullback composition, and taking H⁰
recovers the underived mate. Thus σ restricts to c.symm of a(w).
Factor W.fromSpecResidueField w through V and base change f to obtain j. Its fibre above
w is the residue fibre of X_V, canonically isomorphic to the stated fibre Y. Every point
above w is hit: the projection Spec κ(w) ×_V X_V → X_V has exactly that image, by the
residue-field fibre description. Tensor-pullback composition and the equality of the
composite maps to X supply e. Computing the mate on global sections yields exactly the
adjunction-unit expression in the conclusion, including the restriction from j⁻¹(⊤)
to ⊤. These comparisons come from a single hE and e0, so c works for every V. For m = 0
all scalars are cycles. The point w excludes an empty U or V. -/
theorem picard_scalar_model_cycles_realization
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
      DerivedCategory.Q.obj K))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
      ∃ c : Γ((Modules.tensorPullback
          (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤) ≃+
            W.residueField w,
        ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U),
          ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
            (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
              (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
                ∃ y, j y = x) ∧
            ∃ e : (Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
                (Modules.tensorPullback
                  (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
              ∀ a : Γ(W, V),
                (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
                ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
                  e.hom.app ⊤
                    (((Modules.tensorPullback j).obj
                      ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                        (homOfLE j.preimage_top.ge).op
                          (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                            ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                              (Opposite.op ⊤) σ)) =
                    c.symm (W.evaluation V w hwV a) := by
  classical
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  obtain ⟨c, hc⟩ := picard_scalar_derived_cycles W E w U hwU hU m d K hK hneg
    e0 e1 hE hd hdw
  obtain ⟨q, hq⟩ := picard_direct_image_test_sections f L W k w
  refine ⟨(q (W.fromSpecResidueField w)).symm.trans c, ?_⟩
  intro V hwV hVU
  obtain ⟨j, hj, e, he⟩ := hq V hwV
  refine ⟨j, hj, e, ?_⟩
  intro a ha
  obtain ⟨ξ, hξ⟩ := hc V hwV hVU a ha
  refine ⟨q V.ι ξ, ?_⟩
  exact (he ξ).trans (congrArg (q (W.fromSpecResidueField w)) hξ)

end AlgebraicGeometry.Scheme
