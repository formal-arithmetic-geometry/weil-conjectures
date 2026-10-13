/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # The refinement comparison square

Source: Stacks Project, Tag 01FD.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Refinement pullback commutes with the canonical comparison for arbitrary covers.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1, specialized to the
adjunction unit F → f_* f^* F
(blueprint: lem-sc-cech-refinement-comparison-square).

Proof: resolve F by J on X and f^* F by I on X'. Resolve f_* I by J' and lift
J to J' over the unit and the augmentation. Form B = Cech(U,J), B' = Cech(U,J'),
B'' = Cech(U,f_* I), and A = Cech(U',I). The specified tuple formula defines
B'' → A. The augmentation pentagon commutes by the lift equation. The squares
with global sections commute by restriction naturality. Apply homology and invert
the global-sections comparison quasi-isomorphisms. The outer diagram is the stated
square: the horizontal maps are fixed by IsModuleCechComparison and the vertical
map on module cohomology is the resolution definition of moduleCohomologyPullback.
No comparison from Cech cohomology is inverted, and no acyclicity of the cover is
assumed. Empty index sets are allowed only when the covering equation forces the
scheme to be empty; the same zero-complex diagram proves that case. -/
theorem cechRefinement_comparison_square (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cF' : ((cechComplexFunctor U').obj
        ((tensorPullback f).obj F).presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X'.toRingedSpace p).obj ((tensorPullback f).obj F))
    (hcF' : IsModuleCechComparison U' ((tensorPullback f).obj F) p cF')
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
 :
    cechRefinementHomology gamma p ≫ (forget₂ _ AddCommGrpCat).map cF' =
      (forget₂ _ AddCommGrpCat).map cF ≫ moduleCohomologyPullback f F p := by sorry

end
end AlgebraicGeometry.Scheme.Modules
