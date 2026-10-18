/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.Separable

import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion

/-!
# Fibrewise unramified locus and base change

Source: Stacks Project, Morphisms, Tags 0475 and 02GF
(blueprint: lem-trf-unramified-locus-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The union of source opens on which the morphism is unramified.
Source: Stacks Project, Morphisms, Tag 0475
(blueprint: lem-trf-unramified-locus-base-change). -/
def unramifiedLocus {Z S : Scheme.{u}} (h : Z ⟶ S) : Set Z :=
  {z | ∃ O : Z.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ h)}

/-- The unramified locus is open, is characterized by unramified fibre neighbourhoods and
by the fibre residue map with finite separable residue extension, and commutes with base change.
Source: Stacks Project, Morphisms, Tag 0475 and Tag 02GF, (1), (2), (6)
(blueprint: lem-trf-unramified-locus-base-change).

Proof plan: (1) The union defining the locus is the set of points with an unramified source
neighbourhood. Tag 0475 identifies it with the fibrewise locus, proves openness, and proves
arbitrary-base-change compatibility. The forward inclusion also follows by base-changing each
unramified open using `lem-weil-pbc-unramified-base-change-open`.
(2) The fibre morphism is locally of finite type by `lem-weil-pbc-lft-base-change`. Apply
`lem-trf-unramified-maximal-ideal-residue-criterion` to that morphism. Its base is a field,
so the maximal-ideal condition says that the fibre residue map is an isomorphism. The
residue field at `h.asFiber z` is canonically the residue field at `z`; the remaining condition
is finiteness and separability of the residue extension induced by `h`. -/
theorem unramifiedLocus_baseChange
    {Z S : Scheme.{u}} (h : Z ⟶ S) [LocallyOfFiniteType h] :
    IsOpen (unramifiedLocus h) ∧
      (∀ z : Z, z ∈ unramifiedLocus h ↔
        h.asFiber z ∈ unramifiedLocus (h.fiberToSpecResidueField (h z))) ∧
      (∀ z : Z, z ∈ unramifiedLocus h ↔
        IsIso ((h.fiber (h z)).residue (h.asFiber z)) ∧
          (h.residueFieldMap z).hom.Finite ∧
          @Algebra.IsSeparable (S.residueField (h z)) (Z.residueField z) _ _
            (h.residueFieldMap z).hom.toAlgebra) ∧
      (∀ {S' : Scheme.{u}} (k : S' ⟶ S),
        unramifiedLocus (pullback.snd h k) =
          (pullback.fst h k) ⁻¹' unramifiedLocus h) := by
  sorry

end AlgebraicGeometry
