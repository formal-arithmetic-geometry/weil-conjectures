/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechRefinementCochainMap
public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Paper.CechRefinementResolutionBeta

/-! # Refinement on resolution total cohomology

Source: Stacks Project, Tag 01FD, the resolution double-complex diagram.
(blueprint: lem-sc-cech-refinement-resolution-diagram)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The two squares of the resolution diagram, before introducing either canonical
Cech comparison. The map `r` is the global-sections map calculated directly from
`D.β`, `D.lambda`, and `D.a`; no module-cohomology comparison occurs in the conclusion.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1, the double-complex diagram.
(blueprint: lem-sc-cech-refinement-resolution-diagram)

Proof: form B = Cech(U,D.J), B' = Cech(U,D.K), B'' = Cech(U,f_*D.I),
and A = Cech(U',D.I). Applying the Cech functor to D.β and D.lambda gives
B -> B' <- B''. Pullback of sections followed by restriction, in each tuple,
gives B'' -> A. These maps preserve both differentials: D.β and D.lambda
are chain maps and coefficient maps commute with restriction. With resolution
as the first degree, all these maps preserve the total-complex signs.
The map B'' -> B' is a quasi-isomorphism on each resolution-direction column:
sections of D.lambda over every intersection are quasi-isomorphisms because
pushforwards of injectives are section-acyclic and D.K is termwise injective.
The first-quadrant total comparison theorem therefore makes its total a
quasi-isomorphism. Define t on homology by the B -> B' map, the inverse of
B'' -> B', and the B'' -> A map, transporting the forgetful homology isomorphisms.
D.compatible gives the augmentation pentagon; evaluating each component on a
section gives precisely hgamma, so its homology equation is the beta square.
Restriction naturality gives both global-section squares, and D.sections gives
the square between global sections of D.I and of its pushforward. Passing to
homology and cancelling the invertible sections map of D.lambda gives the
alpha square, with the displayed r. None of these cancellations inverts a
Cech-to-cohomology comparison or requires U' to cover. The source covering
ensures H(alpha for B) is invertible and consequently determines t uniquely
from the alpha equation. Products and finite sums in each total degree also
handle empty families and zero modules. -/
theorem exists_cechRefinement_resolution_diagram (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) [F.IsQuasicoherent]
    [EnoughInjectives X.Modules] [EnoughInjectives X'.Modules]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor X'.toRingedSpace).Additive] (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (D : ModuleCohomologyFMapData f F ((tensorPullback f).obj F)
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)) :
    let r := (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).inv ≫
      HomologicalComplex.homologyMap
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) p ≫
      inv (I := D.invertible p) (HomologicalComplex.homologyMap (D.a.hom ≫
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) p) ≫
      (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).hom
    ∃ t : (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).obj
        (((moduleCechDouble U D.J).total (ComplexShape.up ℕ)).homology p) ⟶
      (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).obj
        (((moduleCechDouble U' D.I).total (ComplexShape.up ℕ)).homology p),
      (forget₂ _ AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechBeta U D.J) p) ≫ t =
        cechRefinementHomology gamma p ≫ (forget₂ _ AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechBeta U' D.I) p) ∧
      (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechAlpha U D.J) p) ≫ t =
        r ≫ (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p) := by
  intro r
  let := moduleCechAlpha_isIso U hU D.J p
  let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat
  let a := HomologicalComplex.homologyMap (moduleCechAlpha U D.J) p
  let a' := (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
    (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p)
  refine ⟨e.map (inv a) ≫ r ≫ a', ?_, ?_⟩
  · exact cechRefinement_resolution_canonical_beta X X' f U hU U' refine hrefine
      F p gamma hgamma D
  · exact e.map_hom_inv_assoc a (r ≫ a')

end
end AlgebraicGeometry.Scheme.Modules
