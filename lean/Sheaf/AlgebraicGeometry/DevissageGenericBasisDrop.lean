/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.Support
import WeilConjectures.Topology.IrreducibleOpenComplementDimension

/-!
# A generic-fibre basis and the dimension of its cokernel support

Source: Stacks Project, More on Flatness, Tag 05HF, `lemma-existence-alpha`,
with its proof applied to any finite-type quasi-coherent module on the smooth target
(blueprint: lem-trf-devissage-generic-basis-drop).

The free sheaf is the coproduct of `r` copies of the structure sheaf. The residue map
is the stalk map of `α`, extended along the composite from the ambient local ring
through the fibre local ring to its residue field. Thus it is exactly the induced map
from `κ(ξ)^r`, using the canonical free-stalk and tensor-symmetry identifications.
The existential set `Z` names the actual stalk support of the pulled-back cokernel.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A generic-fibre basis can be lifted to global sections, with smaller-dimensional
cokernel support on the fibre. Source: Stacks Project, Tag 05HF,
`lemma-existence-alpha` (blueprint: lem-trf-devissage-generic-basis-drop).

Proof:
1. On the affine scheme write `H = M̃` with `M` finite, by
   `lem-weil-pbc-quasi-coherent-finite-type-affine` and
   `lem-weil-pbc-affine-tilde-gamma-adjunction`. The stalk-localization formula
   `lem-weil-pbc-spec-tilde-stalk-localization` identifies its residue tensor with
   `M ⊗ κ(p)`: send `(m/s) ⊗ a` to `m ⊗ a/s`, with inverse `m ⊗ a ↦ (m/1) ⊗ a`.
2. Images of finitely many generators span this vector space. Retain a generator
   exactly when its image is independent of the preceding retained ones. These
   images form a basis; its size is `r`, possibly zero. The lifts define `R^r → M`.
3. Apply tilde and its counit to obtain `α`. Tilde preserves coproducts, so its source
   is the stated free sheaf. Naturality of the stalk-localization map identifies
   its residue map with the basis map. By
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`, the cokernel is the tilde of
   the quotient by the image. Images of the original generators generate this quotient,
   so it remains finite type and quasi-coherent.
4. Tensor right exactness (`lem-weil-pbc-tensor-right-exact`) makes the residue tensor
   of this quotient zero. Localize and apply
   `lem-weil-pbc-nakayama-local-generators` to the empty generating list. The quotient
   stalk at the image of `ξ` is zero.
5. The affine fibre-product formula `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-fibre-ring-residue-field-iso` identify this residue field with `κ(ξ)`.
   The pullback-stalk formula `lem-weil-pbc-module-stalk-pullback` shows the fibre
   cokernel stalk at `ξ` is zero. By `lem-weil-pbc-tilde-pullback-base-change`, the
   fibre cokernel is the tilde of a finite scalar extension. Its support is the
   zero locus of its annihilator by `lem-weil-pbc-finite-module-support-annihilator`.
   Thus the actual support `Z` is closed and proper, and misses `ξ`.
6. Geometric irreducibility makes the fibre irreducible. Apply
   `new-node-irreducible-open-complement-dimension` to its nonempty open complement
   and the dimension bound `d`. If `Z` is nonempty, its dimension is strictly below `d`.
7. The dimension at a point is at most the dimension of the whole support, since
   the whole support is an open neighbourhood in the defining infimum
   (`def-kun-dimension`). When `d = 0`, a nonempty support would have a nonnegative
   dimension strictly less than zero, which is impossible. No flatness or finite
   presentation of `H` has been used. -/
theorem devissage_generic_basis_drop {Y B : Scheme.{u}} [IsAffine Y] [IsAffine B]
    (f : Y ⟶ B) [Smooth f] [GeometricallyIrreducible f] (d : ℕ)
    (hdim : ∀ t : B, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞))
    (b : B) (H : Y.Modules) (hH : H.IsQuasiCoherentFiniteType)
    (ξ : f.fiber b) (hξ : IsGenericPoint ξ Set.univ) :
    ∃ (r : ℕ) (α : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ H),
      IsIso ((ModuleCat.extendScalars
        (((f.fiberι b).stalkMap ξ) ≫ (f.fiber b).residue ξ).hom).map
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace ((f.fiberι b) ξ)).map α)) ∧
      IsQuasiCoherentFiniteType (X := Y) (cokernel α) ∧
      ∃ Z : Set (f.fiber b),
        Z = {x | ¬ Subsingleton
          (((tensorPullback (f.fiberι b)).obj (cokernel α)).presheaf.stalk x)} ∧
        IsClosed Z ∧ Z ⊂ Set.univ ∧ ξ ∉ Z ∧
        (Z.Nonempty → topologicalKrullDim Z < (d : WithBot ℕ∞) ∧
          ∀ z : Z, topologicalKrullDimAt z < (d : WithBot ℕ∞)) ∧
        (d = 0 → Z = ∅) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
