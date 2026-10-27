/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module
public import Sheaf.Paper.TowerP1LevelWords
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Tensoring finite word-comparison squares

Source: composition-factors proof (1), tower paragraph; the Levels tensor-word
construction. The tensor constraint is the prescribed site's derived constraint.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCompositionFactors

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E)

/-- Tensor two finite word comparisons using the actual site and realization constraints.
Source: composition-factors proof (1), tower paragraph; Levels tensor-word construction
(blueprint: lem-sp-tensor-word-comparison).

Proof: the endpoint comparison arrows of tensorWord are composites of four invertible
arrows, so are invertible. For the equation, paste four squares. The site's derived
monoidal comparison is natural in its first variable by conjugating the natural
left-derived tensor transformation with its canonical identification with the exact
site functor. It is natural in its second variable because each displayed constraint
is already an isomorphism of functors. Horizontal pasting gives simultaneous
naturality. Apply realization to that square. Next use naturality of the specified
TensorCoordinates.derived. Tensor the two given comparison squares in the level
category. Finally use naturality of the inverse tensorEvaluation. Vertical pasting
and associativity give precisely the defined tensorWord comparison, without choosing
any replacement endpoint identification. This argument applies to all four level
words, including unit words and zero morphisms, and requires no purity hypotheses. -/
theorem tensor_word_comparison {T : Scheme.{u}} (n : ℕ)
    (tc : SpTowerP1.TensorCoordinates l E n b T)
    {K K' L L' : SpTowerP1.LevelWord l E n T}
    {f : K.tower ⟶ K'.tower} {g : L.tower ⟶ L'.tower}
    {f' : K.etale ⟶ K'.etale} {g' : L.etale ⟶ L'.etale}
    (hf : SpTowerP1.WordComparison l E n K K' f f')
    (hg : SpTowerP1.WordComparison l E n L L' g g') :
    SpTowerP1.WordComparison l E n
      (SpTowerP1.tensorWord l E n b tc K L) (SpTowerP1.tensorWord l E n b tc K' L')
      ((SpTowerShriek.tensor l E b T).map (Prod.mkHom f g))
      (((Etale.derivedTensor (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) T).map
        f').app L.etale ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) T).obj
          K'.etale).map g') := by sorry

end AlgebraicGeometry.ProEtale.SpCompositionFactors
