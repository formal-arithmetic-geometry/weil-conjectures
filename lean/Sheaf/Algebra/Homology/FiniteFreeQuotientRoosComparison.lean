/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Cochain comparisons for finite free principal quotient towers

Source: Stacks Project, sites-cohomology.tex, Tags 06YT and 0941, and the
balanced quotient calculation in lem-pur-finite-free-completion-exchange.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory.PrincipalQuotientCompletion

attribute [local irreducible] quotientTower

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]

/-- Cochain data for scalar extension of principal quotient towers. No derived
completion functor occurs here. Naturality is required for all cochain maps.
Source: the balanced quotient calculation and additive cone construction in steps
1--5 of lem-pur-finite-free-completion-exchange
(blueprint: lem-pur-finite-free-quotient-roos-comparison). -/
structure QuotientRoosExchange
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections) (e : ℕ) where
  exact_limits : PreservesFiniteLimits F.E
  exact_colimits : PreservesFiniteColimits F.E
  β : ∀ P, ((quotientTower R t).obj P).asFunctor ⋙
      F.E.mapHomologicalComplex (.up ℤ) ≅
    index e ⋙ ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor
  c : ∀ P, (F.E.mapHomologicalComplex (.up ℤ)).obj
      (roosP ((quotientTower R t).obj P)) ⟶
    roosP ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  product_formula : ∀ P (n : ℕ),
    c P ≫ Pi.π _ n = (F.E.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun k : ℕ ↦ ((quotientTower R t).obj P).asFunctor.obj (op k)) n) ≫
        (β P).hom.app (op n)
  quotient_formula : ∀ P (n : ℕ),
    (F.E.mapHomologicalComplex (.up ℤ)).map (quotientMap R t P n) ≫
      (β P).hom.app (op n) = quotientMap S vS
        ((F.E.mapHomologicalComplex (.up ℤ)).obj P) (e * (n + 1) - 1)
  δ : ∀ P, (F.E.mapHomologicalComplex (.up ℤ)).obj ((quotientRoos R t).obj P) ≅
    roosF.obj ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  cone_formula : ∀ P (p : ℤ),
    (δ P).hom.f (p + 1) ≫ (roosχ ((complexRestriction _ e).obj
      ((quotientTower S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P))) p).hom =
    biprod.lift
      (F.E.map ((roosχ ((quotientTower R t).obj P) p).hom ≫ biprod.fst) ≫ (c P).f p)
      (F.E.map ((roosχ ((quotientTower R t).obj P) p).hom ≫ biprod.snd) ≫
        (c P).f (p + 1))
  a : ∀ P, (quotientRoos S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶
    roosF.obj ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  arithmetic_quasiIso : ∀ P, QuasiIso (a P)
  arithmetic_formula : ∀ P (p : ℤ),
    (a P).f (p + 1) ≫ (roosχ ((complexRestriction _ e).obj
      ((quotientTower S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P))) p).hom =
    (roosχ ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)) p).hom ≫
      biprod.map
        ((block e ((quotientTower S vS).obj
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor).f p)
        ((selection e ((quotientTower S vS).obj
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor).f (p + 1))
  delta_natural : ∀ {P P'} (f : P ⟶ P'),
    (F.E.mapHomologicalComplex (.up ℤ)).map ((quotientRoos R t).map f) ≫ (δ P').hom =
      (δ P).hom ≫ roosF.map ((complexRestriction _ e).map
        ((quotientTower S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f)))
  arithmetic_natural : ∀ {P P'} (f : P ⟶ P'),
    (quotientRoos S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f) ≫ a P' =
      a P ≫ roosF.map ((complexRestriction _ e).map
        ((quotientTower S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f)))

/-- Finite free scalar extension gives the balanced comparison of strict quotient
Roos complexes, natural before localization.

Source: Stacks Project, sites-cohomology.tex, Tags 06YT and 0941; the explicit
finite-basis, balancing and arithmetic calculations in steps 1--5 of
lem-pur-finite-free-completion-exchange
(blueprint: lem-pur-finite-free-quotient-roos-comparison).

Proof: After restriction of scalars, scalar extension is tensor with the underlying
finite free R-module S, hence a finite direct sum of the identity. Faithful exact
forgetting detects exactness and invertibility of its canonical countable-product
comparison. The equality φ(t)^n = u^n v^(en), with u^n invertible, identifies
the cokernels of multiplication by these sections after extension. Balancing gives
β_n on pure local tensors, and the inverse sends a quotient lift s to 1 tensor s;
changing the lift by v^(en) changes the tensor by zero. These formulas commute with
restrictions, differentials, quotient transitions, and maps of the input complex.
Apply the additive Roos comparison to the canonical product comparison followed
by β; its two cone coordinates are exactly the displayed formula for δ. The
selection/block square gives a, which is a quasi-isomorphism by arithmetic
restriction and exact products. Its two coordinates are the selection and block
maps, and their formulas give naturality. The construction also works in rank
zero; positive e ensures that the arithmetic subsequence is cofinal. -/
theorem finiteFreeQuotientRoosComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (he : 1 ≤ e)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))] :
    Nonempty (QuotientRoosExchange F t vS e) := by sorry

end CategoryTheory.PrincipalQuotientCompletion
