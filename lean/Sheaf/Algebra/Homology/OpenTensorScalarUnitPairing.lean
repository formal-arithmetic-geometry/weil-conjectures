/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Algebra.Homology.OpenTensorScalarUnitData
/-! # Scalar-unit pairings in strict coefficient tensor towers

Source: Stacks Project, Modules on Sites, Tag 03EK; Cohomology on Sites, Tag 0GL1.
(blueprint: lem-sf-open-tensor-scalar-unit-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.LocalizedStrictTensor SheafOfModules.SliceTensorGenerator
namespace SheafOfModules.OpenTensorAugmentation
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The scalar-unit pairings, before introducing an open tensor comparison.
Source: Stacks 03EK and 0GL1 (blueprint: lem-sf-open-tensor-scalar-unit-pairing). -/
structure ScalarUnits (A : AlgebraTowers.{c, v, r} R) where
  /-- The prescribed coefficient transitions on both total tensors. -/
  totals : StrictTotals.{c, v, r} R V A
  /-- The source augmentation is a natural map from the constant strict tower. -/
  cT : (Functor.const ℕᵒᵖ).obj (source.{c, v, r} R V) ⟶ totals.T R V
  /-- It inserts 1 into both scalar tensor factors on homogeneous generators. -/
  cT_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C) (f : W ⟶ V)
    (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W)),
    (((cT.app n).app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y) =
      targetSection.{c, v, r} R V (A.obj n) Z p q d h W
        (extensionSection.{c, v, r} R V (Z.1.X p) W f x) y 1 1
  /-- The slice augmentation is also a strict, natural chain map. -/
  cS : (Functor.const ℕᵒᵖ).obj (sliceSource.{c, v, r} R V) ⟶ totals.S R V
  /-- Its formula on the actual tensor presheaf generators. -/
  cS_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : Over V)
    (x : (Z.1.X p).val.obj (op W)) (y : (Z.2.X q).val.obj (op W.left)),
    (((cS.app n).app Z).f d).val.app (op W)
        (sliceSourceSection.{c, v, r} R V Z p q d h W x y) =
      sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h W x y 1 1

/-- The scalar-unit maps and coefficient transitions exist independently of the
projection formula for the open embedding.
Source: Stacks 03EK (section-tensor-product), 0GL1 (lemma-j-shriek-and-tensor).
(blueprint: lem-sf-open-tensor-scalar-unit-pairing).

Proof: for every coefficient algebra A, the maps x ↦ 1 tensor x on the two
factors are linear over the original ring and compatible with restrictions.
Their tensor pairing is balanced, so the tensor universal property, followed by
sheafification, gives the two unit maps. A coefficient map sends both scalar
entries through its ring map; the same balanced universal property constructs
its transition. Equality of these maps is tested on the two scalar pure tensor
factors, using sheafification uniqueness, so identity and composition hold.
Naturality in both module arguments follows by replacing x and y by their
images. In bidegree (p,q) the formulas commute with d tensor 1 and 1 tensor d;
retaining (p,q) retains the sign (-1)^p, so direct-sum totalization gives chain
maps on arbitrary unbounded inputs. A coefficient transition preserves 1 in
each factor, proving compatibility with the constant-tower augmentations.
For the slice construction use the pure-tensor restriction isomorphism to
identify restriction of scalar extension of the second argument. No open
projection comparison or flatness assertion is used. -/
theorem scalarUnits_exists (A : AlgebraTowers.{c, v, r} R) :
    Nonempty (ScalarUnits.{c, v, r} R V A) := by sorry

end SheafOfModules.OpenTensorAugmentation
