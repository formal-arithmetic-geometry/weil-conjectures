/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.Modules.ResidueFiber
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Pullback, tensor products and fibres of invertible modules

Source: Stacks Project, Modules, Tags 01CD, 0B8L, 01C8, 01CT, 01CA, 01CB;
Sheaves, Tags 0096, 0097, 0098; Algebra, Tags 00D0, 00CY, 00D2
(blueprint: lem-weil-pbc-invertible-pullback-tensor).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Invertible modules remain invertible under pullback and tensor product. Pullback
commutes naturally with tensor products and composition, with the stated action on
sections. Symmetry swaps tensor sections; by associativity and adjacent transpositions,
this also permits every permutation of a finite tensor product (including the empty
product, the structure module). Fibres commute with pullback and tensor product, and
these identifications send section values to their indicated pure tensors.

Source: Stacks Project, Modules, Tags 01CD, 0B8L, 01C8, 01CT, 01CA, 01CB;
Sheaves, Tags 0096, 0097, 0098
(blueprint: lem-weil-pbc-invertible-pullback-tensor).

Proof, following the node's eight steps:
1. Trivialize an invertible module near each point (def-sc-invertible-module). Its stalk
is a free rank-one local-ring module; tensoring with the residue field
(def-weil-residue-field) gives a one-dimensional fibre.
2. Pull back a trivializing open cover, using
lem-weil-pbc-invertible-pullback-invertible (01C8, 0B8L).
3. Trivialize both factors on common opens and apply lem-pc-tensor-dual-invertible
(01CT): the tensor of two copies of the structure module is the structure module.
4. Apply lem-weil-pbc-module-pullback-tensor (01CD), including its naturality and its
formula on tensor sections.
5. Compose the adjunctions of def-pc-module-pullback (0096). Both successive and
composite pullbacks are left adjoints of the same pushforward (0097). The comparison
isomorphism compatible with the units therefore sends the successive pullback of a
section to its composite pullback.
6. Apply lem-weil-pbc-module-tensor-symmetric-monoidal (01CA). Its symmetry swaps
pure tensor sections, and composites of associators and adjacent symmetries reorder
any finite family, since adjacent transpositions generate every permutation.
7. By lem-weil-pbc-module-stalk-pullback (0098), the pulled-back stalk is the base
extension of the original stalk, sending the pulled-back germ to the germ tensored
with one. Extend further to the residue field. Associativity of base extension (00D2)
and the residue-field map identify this with extension of the original fibre; following
the germ gives the asserted section-value formula.
8. By lem-weil-pbc-module-stalk-tensor (01CB), the tensor stalk is the tensor of
stalks, with the tensor-germ formula. Extend to the residue field and use associativity
and commutativity (00D0, 00CY, 00D2) to obtain the tensor of fibres. Following the two
germs gives the tensor of their values. -/
theorem invertible_pullback_tensor {X Y : Scheme.{v}} (f : X ⟶ Y) :
    let pb : ∀ {A B : Scheme.{v}} (h : A ⟶ B) (N : B.Modules) (V : B.Opens),
        Γ(N, V) → Γ((tensorPullback h).obj N, h ⁻¹ᵁ V) :=
      fun {_ _} h N V s ↦
        ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app N).val.app (op V) s
    (∀ (L : Y.Modules) [L.IsInvertible],
      (∀ y : Y, Module.rank (Y.residueField y) (residueFiber L y) = 1) ∧
      ((tensorPullback f).obj L).IsInvertible) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible], (L ⊗ M).IsInvertible) ∧
    (∃ e : ∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible],
        (tensorPullback f).obj (L ⊗ M) ≅
          (tensorPullback f).obj L ⊗ (tensorPullback f).obj M,
      (∀ (L M L' M' : Y.Modules)
          [L.IsInvertible] [M.IsInvertible] [L'.IsInvertible] [M'.IsInvertible]
          (a : L ⟶ L') (b : M ⟶ M'),
        (tensorPullback f).map (a ⊗ₘ b) ≫ (e L' M').hom =
          (e L M).hom ≫ ((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b)) ∧
      (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible]
          (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)),
        (e L M).hom.app (f ⁻¹ᵁ V) (pb f (L ⊗ M) V (tmulSection s t)) =
          tmulSection (pb f L V s) (pb f M V t))) ∧
    (∀ (W : Scheme.{v}) (g : W ⟶ X) (L : Y.Modules) [L.IsInvertible],
      ∃ e : (tensorPullback g).obj ((tensorPullback f).obj L) ≅
          (tensorPullback (g ≫ f)).obj L,
        ∀ (V : Y.Opens) (s : Γ(L, V)),
          e.hom.app ((g ≫ f) ⁻¹ᵁ V) (pb g ((tensorPullback f).obj L)
            (f ⁻¹ᵁ V) (pb f L V s)) = pb (g ≫ f) L V s) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible]
        (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)),
      (β_ L M).hom.app V (tmulSection s t) = tmulSection t s) ∧
    (∀ (n : ℕ) (L : Fin n → Y.Modules) [∀ i, (L i).IsInvertible]
        (π : Equiv.Perm (Fin n)),
      Nonempty ((List.ofFn L).foldr (fun A B ↦ A ⊗ B) (𝟙_ Y.Modules) ≅
        (List.ofFn (fun i ↦ L (π.symm i))).foldr (fun A B ↦ A ⊗ B) (𝟙_ Y.Modules))) ∧
    (∀ (L : Y.Modules) [L.IsInvertible] (x : X),
      ∃ e : residueFiber ((tensorPullback f).obj L) x ≅
          (ModuleCat.extendScalars (f.residueFieldMap x).hom).obj (residueFiber L (f x)),
        ∀ (V : Y.Opens) (hx : f x ∈ V) (s : Γ(L, V)),
          e.hom (residueValue (pb f L V s) x hx) =
            (1 : X.residueField x) ⊗ₜ[Y.residueField (f x), (f.residueFieldMap x).hom]
              residueValue s (f x) hx) ∧
    (∀ (L M : Y.Modules) [L.IsInvertible] [M.IsInvertible] (y : Y),
      ∃ e : residueFiber (L ⊗ M) y ≅ (residueFiber L y ⊗ residueFiber M y),
        ∀ (V : Y.Opens) (hy : y ∈ V) (s : Γ(L, V)) (t : Γ(M, V)),
          e.hom (residueValue (tmulSection s t) y hy) =
            residueValue s y hy ⊗ₜ[Y.residueField y] residueValue t y hy) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
