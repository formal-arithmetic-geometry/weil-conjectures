/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.CechComparisonMapNaturality
public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.EtaleTensorSections

/-! # Cech cup products and pullback

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
The comparison maps, refinement cochain map and both bilinear cup products are
characterized by their constructions. The equalities hold for every covering;
isomorphisms are required only to identify the products through inverse comparisons.
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

/-- Refinement pullback and the signed Cech cup product commute with the canonical
Cech-to-module-cohomology comparisons. If these comparisons are isomorphisms, the
products identify through them. Coefficient and pullback naturality are stated below.
Source: Stacks Project, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).

Proof:
1. Tag 01FD constructs gamma by pulling back tuple sections and restricting to the
refined intersections. Resolve F by J and f-star F by I, resolve f-star I pushed
forward by J-prime, and lift J to J-prime over the adjunction unit. With the four
Cech double complexes B=Cech(U,J), B-prime=Cech(U,J-prime),
B-double-prime=Cech(U,f-star I pushed forward), and A=Cech(U-prime,I), the refinement
formula defines B-double-prime to A. The pentagon commutes by the lift equation and
the other squares by restriction. Inverting the global-sections-to-total alpha
quasi-isomorphisms gives the refinement equality. The canonical comparisons are
those of lem-sc-cech-comparison-map-naturality, characterized by alpha and beta.
2. Tag 07MB restricts the front and back factors to the common intersection and
inserts the total-complex signs. Expanding the alternating differential cancels
adjacent omitted-vertex terms, giving Leibniz and the product on cohomology.
3. Tag 0FKV, for F and G in degree zero, gives the commuting derived square with
RGamma and its cup map mu, followed by RGamma of the map from derived tensor to
ordinary tensor (def-pc-tensor-complex-sheaves supplies the signs). Its proof uses
Godement resolutions, where global sections, total Cech, and RGamma agree, and
reduces to the naive signed pairing. The horizontal comparisons are exactly those
of lem-sc-cech-comparison-map-naturality. Taking classes gives the cup equality.
When the comparisons are isomorphisms, apply their inverses for the final clause.
4. Pullback of a tensor section is the tensor of the two pulled-back sections.
Restrictions, coefficient maps and composition of refinements preserve these
formulas, giving the naturality statements below.
-/
theorem cechCupPullbackCompat (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
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
    (cG : ((cechComplexFunctor U).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison U G q cG)
    (cFG : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcFG : IsModuleCechComparison U (F ⊗ G) (p + q) cFG)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q))
    (hcup : IsCechCupProduct U F G p q cup)
    (sheafCup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hsheafCup : IsModuleCupProduct F G p q sheafCup) :
    (cechRefinementHomology gamma p ≫ (forget₂ _ AddCommGrpCat).map cF' =
      (forget₂ _ AddCommGrpCat).map cF ≫ moduleCohomologyPullback f F p) ∧
    (∀ a b, cFG (cup a b) = sheafCup (cF a) (cG b)) ∧
    (∀ (hF : IsIso cF) (hG : IsIso cG) (hFG : IsIso cFG) a b,
      cup (inv (I := hF) cF a) (inv (I := hG) cG b) =
        inv (I := hFG) cFG (sheafCup a b)) := by
  sorry

/-- The sheaf cup product is natural in both coefficient sheaves.
Source: Stacks Project, Tags 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: coefficient maps commute with restriction and the section tensor pairing.
Apply them to the Godement-resolution pairing in Step 3 of cechCupPullbackCompat;
the derived tensor map and its augmentation are natural. Taking cohomology gives
the displayed equality, as asserted in Step 4 of the node's proof. -/
theorem moduleCup_coefficient_naturality (X : Scheme.{v})
    (F G F₁ G₁ : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F₁.IsQuasicoherent] [G₁.IsQuasicoherent] (φ : F ⟶ F₁) (ψ : G ⟶ G₁) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup₁ : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F₁ →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G₁ →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F₁ ⊗ G₁)))
    (hc₁ : IsModuleCupProduct F₁ G₁ p q cup₁) :
    ∀ a b, (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).map
        (@id (F ⊗ G ⟶ F₁ ⊗ G₁) (φ ⊗ₘ ψ)) (cup a b) =
      cup₁ ((RingedSpace.moduleCohomology X.toRingedSpace p).map φ a)
        ((RingedSpace.moduleCohomology X.toRingedSpace q).map ψ b) := by
  sorry

/-- Pullback carries the sheaf cup product to the product of pulled-back classes,
using the canonical tensor-pullback comparison on the coefficient sheaves.
Source: Stacks Project, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on each refined intersection pullback of a tensor is the tensor of pullbacks;
the total sign depends only on the degrees (Step 4). For acyclic Godement models this
commutes with the derived cup map mu and with the map to the ordinary tensor.
Apply the cohomology comparisons of Step 3 and the pullback comparison of Step 1.
The tensor coefficient comparison is lem-weil-pbc-module-pullback-tensor, normalized
on section tensors, so its cohomology map gives precisely the displayed equality. -/
theorem moduleCup_pullback_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup' : (RingedSpace.moduleCohomology X'.toRingedSpace p).obj
        ((tensorPullback f).obj F) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace q).obj
        ((tensorPullback f).obj G) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).obj
        (@id X'.Modules ((tensorPullback f).obj F ⊗ (tensorPullback f).obj G)))
    (hc' : IsModuleCupProduct ((tensorPullback f).obj F) ((tensorPullback f).obj G)
      p q cup') :
    ∀ a b, (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).map
        ((Classical.choose (module_pullback_tensor f)) F G).hom
        (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) (p + q) (cup a b)) =
      cup' (moduleCohomologyPullback f F p a) (moduleCohomologyPullback f G q b) := by
  sorry

/-- Refinement of Cech cochains is natural in the coefficient module.
Source: Stacks Project, Tag 01FD
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on each tuple, the tensor-pullback unit is natural in the module map, and
module morphisms commute with restriction. Apply these two identities to the tuple
formula defining gamma (Steps 1 and 4). The equality holds in every degree, hence
also after taking cohomology and the comparison maps of Step 1. -/
theorem cechRefinement_coefficient_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F F₁ : X.Modules) [F.IsQuasicoherent] [F₁.IsQuasicoherent] (φ : F ⟶ F₁)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (gamma₁ : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F₁.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F₁).presheafModuleCat))
    (hgamma₁ : IsCechRefinementMap f U U' refine hrefine F₁ gamma₁) :
    ∀ (n : ℕ) (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n),
      gamma₁.f n (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)).f n a) =
        ((cechComplexFunctor U').map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((tensorPullback f).map φ).val)).f n (gamma.f n a) := by
  sorry

/-- The Cech cup product is natural in both coefficient sheaves.
Source: Stacks Project, Tags 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: the two coefficient maps commute with restriction and send a tensor of two
sections to the tensor of their images. Apply this on each intersection to the
front/back cup formula of Step 2. This gives the equality on cocycles and therefore
on their classes. Combining with comparison-map naturality in Step 3 proves that
the cup comparison square is natural, as asserted by Step 4. -/
theorem cechCup_coefficient_naturality (X : Scheme.{v}) {ι : Type v} (U : ι → X.Opens)
    (F G F₁ G₁ : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F₁.IsQuasicoherent] [G₁.IsQuasicoherent] (φ : F ⟶ F₁) (ψ : G ⟶ G₁) (p q : ℕ)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q))
    (hc : IsCechCupProduct U F G p q cup)
    (cup₁ : ((cechComplexFunctor U).obj F₁.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G₁.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F₁ ⊗ G₁).presheafModuleCat).homology (p + q))
    (hc₁ : IsCechCupProduct U F₁ G₁ p q cup₁) :
    ∀ a b, HomologicalComplex.homologyMap ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (φ ⊗ₘ ψ).val)) (p + q) (cup a b) =
      cup₁ (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)) p a)
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ψ.val)) q b) := by
  sorry

/-- Successive specified refinements compose after the canonical coefficient identification.
The last two equalities give the composite comparison square and functoriality of the
usual cohomology pullback, respectively.
Source: Stacks Project, Tag 01FD; Step 4 of the node's proof
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on a tuple of indices, successive restrictions compose and pullback of sections
through the two adjunction units is pullback through their composite unit. The existing
unit-normalized tensorSectionsComp identifies this unit with the unit for f₁ ≫ f.
Thus the degree maps agree for the composite index function, giving the cochain equality.
Apply homology and its canonical forgetful comparisons, then the Tag 01FD comparison
square, to obtain the second equality. Finally, compose the two resolution diagrams
for the units defining moduleCohomologyPullback. Under tensorSectionsComp the composite
unit is the unit for f₁ ≫ f; resolution independence yields the third equality. This
argument uses no comparison isomorphism and applies to every open covering. -/
theorem cechRefinement_composition_naturality
    (X X' X'' : Scheme.{v}) (f : X' ⟶ X) (f₁ : X'' ⟶ X')
    {ι ι' ι'' : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (U'' : ι'' → X''.Opens) (hU'' : iSup U'' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (refine₁ : ι'' → ι') (hrefine₁ : ∀ i, U'' i ≤ f₁ ⁻¹ᵁ U' (refine₁ i))
    (hrefineComp : ∀ i, U'' i ≤ (f₁ ≫ f) ⁻¹ᵁ U ((refine ∘ refine₁) i))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj
          (F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U').obj
          ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (gamma₁ : ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U').obj
          ((tensorPullback f).obj F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U'').obj
          ((tensorPullback f₁).obj ((tensorPullback f).obj F)).presheafModuleCat))
    (hgamma₁ : IsCechRefinementMap f₁ U' U'' refine₁ hrefine₁ ((tensorPullback f).obj F) gamma₁)
    (gammaComp : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj
          (F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U'').obj
          ((tensorPullback (f₁ ≫ f)).obj F).presheafModuleCat))
    (hgammaComp : IsCechRefinementMap (f₁ ≫ f) U U'' (refine ∘ refine₁) hrefineComp F gammaComp)
    (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hc : IsModuleCechComparison U F p c)
    (cComp : ((cechComplexFunctor U'').obj
        ((tensorPullback (f₁ ≫ f)).obj F).presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X''.toRingedSpace p).obj
        ((tensorPullback (f₁ ≫ f)).obj F))
    (hcComp : IsModuleCechComparison U'' ((tensorPullback (f₁ ≫ f)).obj F) p cComp) :
    (gamma ≫ gamma₁ ≫
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          ((cechComplexFunctor U'').map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              ((tensorSectionsComp f₁ f).hom.app F).val)) = gammaComp) ∧
    (cechRefinementHomology gamma p ≫ cechRefinementHomology gamma₁ p ≫
      (forget₂ _ AddCommGrpCat).map
        (HomologicalComplex.homologyMap ((cechComplexFunctor U'').map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((tensorSectionsComp f₁ f).hom.app F).val)) p) ≫
      (forget₂ _ AddCommGrpCat).map cComp =
        (forget₂ _ AddCommGrpCat).map c ≫ moduleCohomologyPullback (f₁ ≫ f) F p) ∧
    (moduleCohomologyPullback f F p ≫
      moduleCohomologyPullback f₁ ((tensorPullback f).obj F) p ≫
      (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology X''.toRingedSpace p).map
          ((tensorSectionsComp f₁ f).hom.app F)) =
      moduleCohomologyPullback (f₁ ≫ f) F p) := by
  sorry

/-- The specified refinement carries the Cech cup cochain to the cup of the refined
cochains, after the canonical tensor-pullback coefficient identification.
Source: Stacks Project, Tags 01FD and 07MB; Step 4 of the node's proof
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: evaluate on a tuple of refined indices. The front and back tuples commute
with the specified index function. Pullback of sections commutes with restriction,
and the section-normalized module_pullback_tensor sends the pullback of a tensor
to the tensor of the pullbacks. These identities identify each tuple component of
the two sides. The product projections then give the cochain equality. Together
with Leibniz this descends to cohomology and makes the cup comparison square
natural under refinement and pullback, without any comparison isomorphism. -/
theorem cechCup_refinement_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (gammaF : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgammaF : IsCechRefinementMap f U U' refine hrefine F gammaF)
    (gammaG : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj G.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj G).presheafModuleCat))
    (hgammaG : IsCechRefinementMap f U U' refine hrefine G gammaG)
    (gammaFG : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj (F ⊗ G)).presheafModuleCat))
    (hgammaFG : IsCechRefinementMap f U U' refine hrefine (F ⊗ G) gammaFG)
    : ∀ (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
      (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q),
      (((cechComplexFunctor U').map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (((Classical.choose (module_pullback_tensor f)) F G).hom).val)).f (p + q))
        (gammaFG.f (p + q) (cechCupCochain U F G p q a b)) =
      cechCupCochain U' ((tensorPullback f).obj F) ((tensorPullback f).obj G) p q
        (gammaF.f p a) (gammaG.f q b) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
