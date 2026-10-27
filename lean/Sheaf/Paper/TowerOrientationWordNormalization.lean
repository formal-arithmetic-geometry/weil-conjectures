/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Sheaf.Paper.TowerTensorTransposeWords
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Unit normalization for the finite tower orientation word

Source: the tower paragraph of composition-factors proof (1), and the unit
normalization of tower-gamma (1).
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

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCompositionFactors

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_1
  AlgebraicGeometry.ProEtale.ModuleDerivedCategory._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem word_precompose {T : Scheme.{u}} (n : ℕ)
    {K L : SpTowerP1.LevelWord l E n T}
    {N : Etale.DerivedCategoryModule (SpTowerP1.levelRing l E n) T}
    (t : N ⟶ L.etale) [IsIso t]
    {f : K.tower ⟶ L.tower} {g : K.etale ⟶ N}
    (h : SpTowerP1.WordComparison l E n K L f (g ≫ t)) :
    SpTowerP1.WordComparison l E n K
      ⟨L.tower, N, (SpTowerP1.nu l E n T).map t ≫ L.comparison⟩ f g := by
  haveI := h.2.1
  refine ⟨h.1, by infer_instance, ?_⟩
  simpa only [Functor.map_comp, Category.assoc] using h.2.2

/-- Change the finite orientation comparison from its retained origin to the
counit-normalized dualizing word.
Source: composition-factors proof (1), tower paragraph; tower-gamma (1)
(blueprint: lem-sp-tower-orientation-word-normalization).

Proof: precompose the target word with the exceptional image of the inverse unit
comparison, the inverse finite right-adjoint comparison, and the image of ui.inv.
All three arrows are invertible. Functoriality of nu and associativity identify
its new comparison square with the given square. The source library proves that
the inverse single/derived-unit isomorphism is the identity. Consequently the
extra exceptional image of this map is an identity, and the displayed composite
is exactly the dualizingWord comparison. This uses the specified unit and right
adjoint comparisons, without choosing any new endpoint identification. -/
theorem tower_orientation_word_normalized {X V Y : Scheme.{u}}
    (j : X ⟶ V) [IsOpenImmersion j] (p : V ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y)
      (SpTowerGamma.originalUnit l E b q Y))
    (n : ℕ)
    (ui : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p)
      hF G adj lv n ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩).etale ≅
        Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y)
    (K : SpTowerP1.LevelWord l E n X)
    (f : K.tower ⟶ (SpTowerGamma.exceptional l E b q G).obj
      ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)
    (g : K.etale ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p))
    (ha : SpTowerP1.WordComparison l E n K
      (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p)
        hF G adj lv n ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩) f
      (g ≫ (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
        (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app
          (MonoidalCategory.tensorUnit _) ≫ (lv.realization n).right.map ui.inv)) :
    SpTowerP1.WordComparison l E n K
      (SpTensorTranspose.dualizingWord l E b o q j p hF G adj lv hU n ui) f g := by
  let v := SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n)
      (lv.realization n)
  let t := (Etale.rightDerivedUpperShriek
      (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p)).map
        (PurityFiniteSetting.smoothPurityUnitIso (SpTowerP1.levelRing l E n) Y).inv ≫
    v.inv.app _ ≫ (lv.realization n).right.map ui.inv
  have ht : t = v.inv.app (MonoidalCategory.tensorUnit _) ≫
      (lv.realization n).right.map ui.inv := by
    dsimp only [t]
    rw [reassoc_of% (v.inv.naturality
      (PurityFiniteSetting.smoothPurityUnitIso (SpTowerP1.levelRing l E n) Y).inv)]
    erw [PurityFiniteSetting.smoothPurityUnitIso, Etale.singleFunctorObjUnitIso_inv,
      CategoryTheory.Functor.map_id, Category.id_comp]
  apply word_precompose l E b n
    (L := SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p)
      hF G adj lv n ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩) t
  simpa only [ht, Category.assoc] using ha

end AlgebraicGeometry.ProEtale.SpCompositionFactors
