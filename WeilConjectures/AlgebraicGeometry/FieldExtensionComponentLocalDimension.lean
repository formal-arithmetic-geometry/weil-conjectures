/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Sober
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.LocallyAlgebraicDimensionComponents

/-! # Component dimensions after extension of the ground field

Source: Stacks Project, Tags 02FY (1), 01T6, 01IS, and 0A21 (5) / 0B1B.
(blueprint: lem-trf-field-extension-component-local-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem localDim_homeomorph_le {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

private theorem localDim_field_fiber {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (x : X) :
    topologicalKrullDimAt (f.asFiber x) = topologicalKrullDimAt x := by
  let j := f.fiberι (f x)
  have hj : Function.Surjective j := by
    intro z
    exact ⟨(f.fiberHomeo (f x)).symm ⟨z, Subsingleton.elim _ _⟩,
      f.fiberι_fiberHomeo_symm _ _⟩
  let e := (Equiv.ofBijective j ⟨j.isEmbedding.injective, hj⟩).toHomeomorphOfIsInducing
    j.isEmbedding.toIsInducing
  have hx : e (f.asFiber x) = x := f.fiberι_asFiber x
  apply le_antisymm
  · simpa only [hx] using localDim_homeomorph_le e (f.asFiber x)
  · have h := localDim_homeomorph_le e.symm (e (f.asFiber x))
    rw [Homeomorph.symm_apply_apply] at h
    rwa [hx] at h

/-- Extending the ground field preserves local topological dimension. The base-changed scheme
is locally Noetherian; every component has a generic point, and its dimension equals the local
dimension at any such point and at its image in the original scheme. Constant local dimension
therefore gives the same dimension for every component after the field extension.

Source: Stacks Project, Tags 02FY (1), 01T6, 01IS, and 0A21 (5) / 0B1B.
(blueprint: lem-trf-field-extension-component-local-dimension)

Proof:
1. The second pullback projection is locally of finite type by
   [lem-weil-pbc-lft-base-change]. A field is Noetherian, so [pqf-lem-locnoeth-lft]
   makes its source locally Noetherian, as in [pqf-def-locnoeth].
2. Apply [lem-sc-fibre-dimension-after-base-change] to the two structure morphisms to the
   spectra of the fields. Their fibres identify with the whole schemes by
   [def-pc-scheme-fibre]. The dimensions in [def-kun-dimension] and
   [def-kun-topological-dimension-at-point] are the local topological dimensions, giving
   equality at every point and its first-projection image (Tag 02FY (1)).
3. A scheme is sober by [lem-sc-scheme-sober], so every closed irreducible component has
   a generic point (Tag 01IS).
4. For any such point z of D, [def-sc-generic-point] gives D = closure {z}.
   Any other component containing z contains D by closedness and therefore equals D by
   maximality in [def-weil-irreducible-components]. Apply
   [lem-trf-locally-algebraic-dimension-components] to the locally finite type scheme over
   the extended field: the maximum of dimensions of components through z is just dim D
   (Tag 0B1B). Combine with step 2 at z.
5. If all local dimensions on Y are d, evaluate that hypothesis at the image of z and use
   step 4. For empty Y, the first projection forces its pullback to be empty too, so the
   point and component assertions are vacuous [def-pc-fibre-product].
-/
theorem field_extension_component_local_dimension
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] :
    IsLocallyNoetherian (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ∧
      (∀ w : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        topologicalKrullDimAt w = topologicalKrullDimAt
          (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L))) w)) ∧
      (∀ D : Set ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        D ∈ irreducibleComponents
            ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) →
          (∃ z : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
            IsGenericPoint z D) ∧
          ∀ z : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
            IsGenericPoint z D →
              topologicalKrullDim D = topologicalKrullDimAt z ∧
                topologicalKrullDimAt z = topologicalKrullDimAt
                  (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k L))) z)) ∧
      ∀ d : ℕ, (∀ y : Y, topologicalKrullDimAt y = (d : WithBot ℕ∞)) →
        ∀ D : Set ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
          D ∈ irreducibleComponents
              ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap k L)))) →
            topologicalKrullDim D = (d : WithBot ℕ∞) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let q : pullback g b ⟶ Spec (.of L) := pullback.snd g b
  have : LocallyOfFiniteType q := MorphismProperty.pullback_snd _ _ inferInstance
  have hnoeth : IsLocallyNoetherian (pullback g b) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have hdim (w : ↥(pullback g b)) : topologicalKrullDimAt w =
      topologicalKrullDimAt (pullback.fst g b w) := by
    exact (localDim_field_fiber q w).symm.trans
      (((fibre_dimension_after_base_change g b w).2.2).trans
        (localDim_field_fiber g (pullback.fst g b w)))
  have hcomponent (D : Set ↥(pullback g b)) (hD : D ∈ irreducibleComponents ↥(pullback g b))
      (z : ↥(pullback g b)) (hz : IsGenericPoint z D) :
      topologicalKrullDim D = topologicalKrullDimAt z := by
    obtain ⟨C, hC, hzC, hdimC⟩ :=
      (topologicalKrullDimAt_eq_max_component_dimension q z).2
    have hDC : D ⊆ C :=
      (hz.mem_closed_set_iff (isClosed_of_mem_irreducibleComponents C hC)).mp hzC
    have hCD : C ⊆ D := hD.2 hC.1 hDC
    have hEq : C = D := Set.Subset.antisymm hCD hDC
    subst C
    exact hdimC
  refine ⟨hnoeth, hdim, ?_, ?_⟩
  · intro D hD
    refine ⟨QuasiSober.sober hD.1 (isClosed_of_mem_irreducibleComponents D hD), ?_⟩
    intro z hz
    exact ⟨hcomponent D hD z hz, hdim z⟩
  · intro d hd D hD
    obtain ⟨z, hz⟩ := QuasiSober.sober hD.1 (isClosed_of_mem_irreducibleComponents D hD)
    exact (hcomponent D hD z hz).trans ((hdim z).trans (hd _))

end AlgebraicGeometry
