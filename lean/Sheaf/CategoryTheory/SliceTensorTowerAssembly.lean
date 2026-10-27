/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SliceTensorGeneratorInterfaces

/-! # Intermediate generator comparisons

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY, 03EK and 0E8I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.LocalizedStrictTensor

namespace SheafOfModules.SliceTensorGenerator

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Normalized scalar comparisons induce the ordinary strict tower comparison.
Source: Stacks 0E8I, 03DI and 03CY; ordinary projection and strict assembly in
lem-sf-cbc-slice-tensor-generator-coherence, Steps 3, 5, 7 and 8.
(blueprint: lem-sf-slice-tensor-tower-assembly).

Proof: Apply exists_ringedSliceTensorGenerators with H the underlying module
of the coefficient algebra. Transport its ordinary tensors through the
sheafification tensor identifications. This gives a normalized ordinary
comparison at each coefficient algebra. On a generator both its forward map
and t followed by restriction of l, inverse k and inverse tv send [m] tensor s
to [m tensor s]; the sheafification adjunction and tensor generation identify
the maps. For a coefficient map b, both composites send [m] tensor s to
[m tensor b(s)]; the same test proves coefficient naturality. Assemble the
level isomorphisms with NatIso.ofComponents, first over the tower and then over
slice modules. Coefficient naturality gives the tower squares, and module
naturality gives the second assembly. Generator extensionality gives uniqueness.
No chain, unit, flatness or boundedness hypothesis is needed here. -/
theorem tensorTowerAssembly_exists
    (k : ∀ A : Under R,
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A)
    (t : ∀ A : Under R, TensorLift.{c, v, r} R A)
    (tv : ∀ A : Under R,
    TensorLift.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A))
    (l : ∀ A : Under R, LinearComparison.{c, v, r} R V A)
    (hk : ∀ A,
    ScalarExtensionNormalized.{c, v, r} R V A (k A))
    (ht : ∀ A, TensorLiftNormalized.{c, v, r} R A (t A))
    (htv : ∀ A,
    TensorLiftNormalized.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A) (tv A))
    (hl : ∀ A, LinearNormalized.{c, v, r} R V A (l A))
    : ∃ o : ∀ S : AlgebraTowers.{c, v, r} R,
    localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
      reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
        towerExtension.{c, v, r} R V,
      (∀ S, OrdinaryNormalized.{c, v, r} R V S (o S)) ∧
      (∀ S e,
    OrdinaryNormalized.{c, v, r} R V S e → e = o S) ∧
      (∀ (S : AlgebraTowers.{c, v, r} R)
    (M : Modules.{max c v, v, r} (R.over V)) (n : ℕᵒᵖ),
    ((o S).hom.app M).app n =
      (t (S.obj n)).hom.app ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
        (scalars.{c, v, r} R (S.obj n)).map ((l (S.obj n)).hom.app M) ≫
        (k (S.obj n)).inv.app
          ((extend.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).hom).obj M) ≫
        (localizedSystemExtension.{c, v, r} R V).map
          ((tv (S.obj n)).inv.app M)) ∧
      (∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T),
    Functor.whiskerLeft (localizedSystemExtension.{c, v, r} R V)
        ((reductionFamily.{c, v, r} R).map a) ≫ (o T).hom =
      (o S).hom ≫
        Functor.whiskerRight
          ((reductionFamily.{max c v, v, r} (R.over V)).map
            (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V)))
          (towerExtension.{c, v, r} R V)) := by sorry

end SheafOfModules.SliceTensorGenerator
