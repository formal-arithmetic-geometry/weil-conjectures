/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.RingedTensorSquarePresentation

/-! # Tensor compatibility on ordinary module sheaves

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory
namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

/-- Tensor compatibility of the linear square on two ordinary module sheaves.

Proof: precompose with the iterated scalar-extension insertion on the inverse
image of a generalized pure tensor m tensor n. The four canonical pure-tensor
formulas identify each path with the tensor of the two iterated insertions.
The insertion equation of s identifies these insertions on m and n. Naturality
of s.sets with respect to the generalized pair of sections identifies the
underlying inverse-image elements, since finite-limit preserving inverse image
preserves their product. Consequently the two composites agree on these inserted
pure tensors. The scalar-extension universal property extends this equality to
scalar multiples, linearity extends it to sums, and the tensor and sheafification
universal properties give equality of module-sheaf morphisms. Structural ring
maps need not be flat; the same calculation works for zero rings and zero modules.
Source: Stacks, Cohomology on Sites, Tag 07A4 (lemma-pullback-tensor-product),
and the tensor part of Tag 0E48 (remark-compatible-with-diagram).
(blueprint: lem-weil-pbc-ringed-square-module-tensor-compatibility). -/
theorem ringedSquareModuleTensorCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (M N : SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) :
    s.modules.hom.app ((monoidalCategory Y.ring).tensorObj M N) ≫
      h.pullback.map (f.ordinaryTensor.mu M N).hom ≫
      (h.ordinaryTensor.mu (f.pullback.obj M) (f.pullback.obj N)).hom =
    k.pullback.map (g.ordinaryTensor.mu M N).hom ≫
      (k.ordinaryTensor.mu (g.pullback.obj M) (g.pullback.obj N)).hom ≫
      (monoidalCategory X'.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N) := by
  sorry

end SheafOfModules
