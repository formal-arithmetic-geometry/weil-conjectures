/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.RingTheory.GRing

/-!
# Regular maps and finite type base change

Source: Stacks Project, More on Algebra, Lemma Tag 07C1 (blueprint:
lem-weil-pbc-regular-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingHom

/-- A regular ring map remains regular after base change along a finite type ring map.

This is the statement of Stacks Project, More on Algebra, Lemma Tag 07C1:
if `φ : R → Λ` is regular and `R → R'` is of finite type, then the map
`R' → Λ ⊗_R R'` induced by the second tensor factor is regular.
(blueprint: lem-weil-pbc-regular-base-change)

Proof (the six steps of the node, following Stacks 07C1):
1. Flat base change makes the second-factor map flat. Use
   lem-weil-pbc-flat-module-base-change, tensor symmetry, and def-weil-pbc-flat-ring-map.
2. For a prime p' of R', its inverse image p is prime. The induced residue-field map
   κ(p) → κ(p') commutes with the structure maps (def-weil-pbc-localization-at-prime).
   Finite type of R → R' makes this field extension finitely generated, by
   lem-weil-pbc-finite-type-residue-field-extension-finitely-generated.
3. Put A = κ(p) ⊗[R] Λ. Tensor symmetry and two applications of
   lem-weil-pbc-tensor-cancel-base-change identify the new fibre with κ(p') ⊗[κ(p)] A.
   The two R-algebra structures on κ(p') agree by step 2.
4. Regularity of φ makes A Noetherian and geometrically regular (def-weil-pbc-g-ring).
   Apply lem-weil-pbc-geometrically-regular-finitely-generated-extensions to κ(p')/κ(p).
   The fibre is Noetherian by step 3 and def-weil-pbc-noetherian-ring.
5. For any finite purely inseparable extension k''/κ(p')
   (def-weil-pbc-finite-purely-inseparable-extension), tensor cancellation identifies
   its base-changed fibre with k'' ⊗[κ(p)] A. This extension of κ(p) is finitely generated:
   adjoin generators of κ(p')/κ(p) and a finite κ(p')-basis of k''.
   Apply lem-weil-pbc-geometrically-regular-finitely-generated-extensions again.
   Ring isomorphisms preserve regularity (def-weil-regular-scheme), so the new fibre
   is geometrically regular by def-weil-pbc-g-ring.
6. Flatness and the Noetherian, geometrically regular fibres give regularity of the
   second-factor map by def-weil-pbc-g-ring.
-/
theorem regular_base_change
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.FiniteType R R'] (hφ : (algebraMap R Λ).IsRegular) :
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] Λ ⊗[R] R').toRingHom.IsRegular := by
  sorry

end RingHom
