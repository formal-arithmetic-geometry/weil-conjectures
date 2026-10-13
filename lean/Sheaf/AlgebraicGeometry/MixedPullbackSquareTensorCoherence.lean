/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Tensor coherence of the canonical pullback square
Source: Stacks Project, cohomology.tex, Tags 079U and 08HY;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Canonical square comparison, made from the fixed composition comparisons.
Source: Stacks Project, Remark 08HY
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence). -/
def mixedPullbackSquareComparison
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
      derivedPullback f ⋙ derivedPullback (pullback.fst f g) :=
  let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) a b
  c (pullback.snd f g) g ≪≫
    eqToIso (congrArg (fun k : pullback f g ⟶ Y => derivedPullback k)
      pullback.condition.symm) ≪≫ (c (pullback.fst f g) f).symm

/-- Tensor coherence of the canonical square comparison.
Source: Stacks Project, cohomology.tex, Lemma 079U and Remark 08HY;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-pullback-square-tensor-coherence).

Proof: choose K-flat representatives of P and Q. Their tensor and successive
pullbacks are K-flat. The normalization equations identify all four tensorators with
ordinary pullback tensor comparisons, and the two composition comparisons with the
mates of ordinary direct-image composition. Both ordinary paths carry a pure tensor
to the tensor of the same pulled-back sections. Localize this equality and cancel
only the invertible K-flat derived counits. Naturality and resolution isomorphisms
transport the result to arbitrary P and Q. Equality of the scheme composites supplies
the canonical equality transport. No base-change morphism is cancelled. -/
theorem mixedPullbackSquareComparison_tensor
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (P Q : schemeDerivedCategory Y) :
    (derivedPullback (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso g).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
      ((mixedPullbackSquareComparison f g).hom.app P ⊗ₘ
        (mixedPullbackSquareComparison f g).hom.app Q) =
    (mixedPullbackSquareComparison f g).hom.app (P ⊗ Q) ≫
      (derivedPullback (pullback.fst f g)).map
        ((mixedHomTensorPullbackIso f).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
        ((derivedPullback f).obj P, (derivedPullback f).obj Q) := by sorry

end AlgebraicGeometry
