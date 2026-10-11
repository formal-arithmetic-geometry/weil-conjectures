/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.Paper.FiniteSplitEtaleHypercover
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The augmented free complex of a split étale hypercover

Source: Stacks Project, Hypercoverings, Tags 01GC, 01GD, 01GE and 01GW;
blueprint `sec-curve-estimates/sk-prop-h2`, order 948.
(blueprint: lem-weil-pbc-hypercover-free-resolution)

The augmentation is a quasi-isomorphism to the free sheaf on the terminal étale
object (the identity of the base). This is precisely exactness of the augmented
complex, including surjectivity at its last term. Coefficients in a constant ring
are expressed as module-valued sheaves, with sectionwise scalar action.
-/

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover

/-- The augmented alternating-face free abelian sheaf complex is exact.
Source: Stacks Project, Hypercoverings, Tags 01GC, 01GD and 01GE.
(blueprint: lem-weil-pbc-hypercover-free-resolution)

Proof: (1) Apply Yoneda to the hypercover. Each matching map is locally surjective:
pull it back along a section of the matching presheaf to obtain an étale cover
with a tautological lift. The degree-zero comparison is the Čech nerve of U₀ → X;
lem-weil-pbc-cech-nerve-free-homology gives its free-sheaf homology.
(2) Set Kⁿ = coskₙ skₙ h_U. The matching-object/coskeleton identification
(lem-weil-pbc-matching-object-coskeleton) and local surjectivity allow
lem-weil-pbc-coskeleton-free-homology-comparison to identify the homology of Kⁿ
with that of Kⁿ⁻¹. K⁰ is 1-coskeletal; for n = 1 this supplies the needed hypothesis.
(3) Homology in degree i depends only on degrees through i+1, where h_U agrees
with Kⁱ⁺¹. Transfer positive vanishing and the augmentation-induced H₀ identification.
The unit of sheafification supplies the free sheaves (def-weil-pbc-sheafification).
-/
theorem freeAbelian_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) AddCommGrpCat.{w + 1}).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1})).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  sorry

/-- Injective abelian sheaves have hypercover-section cohomology equal to their base
sections in degree zero and zero in positive degrees.
Source: Stacks Project, Hypercoverings, Tag 01GW.
(blueprint: lem-weil-pbc-hypercover-free-resolution)

Proof: Step (4) of the node. By the sheafification adjunction and
lem-weil-pbc-free-yoneda-presheaf-module at ℤ, Hom(ℤ[V], I) is I(V).
Apply Hom(-, I) to the exact augmented complex from steps (1)--(3) above.
The defining extension property of injectivity (def-sp-injective-resolutions)
makes this exact; its augmented degree-zero exactness identifies H⁰ with I(X)
through the augmentation, and positive cohomology vanishes. The complex uses
the alternating-coface construction of def-weil-pbc-finite-split-hypercover,
without requiring finiteness of the hypercover.
-/
theorem injective_abelian_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

/-- The same augmented free-sheaf resolution over every constant commutative ring.
Source: Stacks Project, Hypercoverings, Tags 01GC, 01GD and 01GE, with free R-modules.
(blueprint: lem-weil-pbc-hypercover-free-resolution)

Proof: Repeat steps (1)--(3) of freeAbelian_augmentation_quasiIso with free R-modules.
The Čech-nerve and coskeleton-comparison lemmas are stated over every commutative
ring; their contractions and the exactness of sheafification apply directly.
Thus no tensor-exactness or flatness hypothesis on R is required.
-/
theorem freeModule_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R] :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) (ModuleCat.{w + 1} R)).obj
            (ModuleCat.free R) ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{w + 1} R))).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  sorry

/-- Injective sheaves of modules over a constant ring have the same section-cohomology
assertion, as R-modules.
Source: Stacks Project, Hypercoverings, Tag 01GW, with constant commutative coefficients.
(blueprint: lem-weil-pbc-hypercover-free-resolution)

Proof: Step (4) of the node over R. The free-presheaf Yoneda equivalence
(lem-weil-pbc-free-yoneda-presheaf-module) and the sheafification adjunction identify
Hom(R[V], I) with I(V). Apply Hom(-, I) to the module resolution from steps (1)--(3).
Injectivity gives exactness, hence H⁰ = I(X) through the augmentation and Hᵖ = 0 for p > 0.
-/
theorem injective_module_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
