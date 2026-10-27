/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.Algebra.Homology.ArithmeticRoosMap
public import Sheaf.Algebra.Homology.RoosRepresentativeComposition
public import Sheaf.Algebra.Homology.ScalarTensorSection

/-! # Strict horizontal coherence for principal quotient Roos comparisons

Source: Stacks Tags 03EK and 0941, and the product/cone and arithmetic part of
`lem-pur-finite-free-completion-exchange-coherence`.
No derived completion functor occurs in this cochain statement.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wV x y xA xB xD yA yB yD
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
open scoped ChangeOfRings

namespace CategoryTheory.PrincipalQuotientCompletion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{wV}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]

attribute [local irreducible] quotientTower SheafOfModules.monoidalCategory
  strictRoosMapOfSquare

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Horizontal coherence of principal quotient Roos comparisons, before localization.

Source: Stacks Project, sites-modules.tex, Tag 03EK (balanced tensor products),
and sites-cohomology.tex, Tag 0941 (the product-cone calculation).
(blueprint: lem-pur-finite-free-quotient-roos-horizontal-coherence).

Proof: a finite basis of V over S identifies extension followed by restriction
with a finite power. Restriction preserves products and reflects isomorphisms,
so extension preserves countable products, including in rank zero. Reindex rb
along index e. The equality f*(e*(n+1)-1+1)-1=(e*f)*(n+1)-1 identifies its
new target. The canonical additive Roos comparison gives restricted and its
selected quotient maps. The associator obeys the balanced tensor formula.
Quotient maps are epimorphisms: each is a tensor image
of a cokernel projection preceded by the tensor-unit isomorphism. Postcompose
these projections with the proposed quotient comparisons. The quotient formulas,
naturality of ordinary and naturality of quotient augmentation give the same map.
Cancel these epimorphisms. Product universality and the two signed cone
coordinates then give the horizontal cochain identity. Selection commutes with
comparison by projection to a selected factor. Block maps commute by additivity
and naturality of each transition. Thus the two cone coordinates give the
arithmetic square. Finally expand the iterated blocks, compose transitions and
regroup the finite sums to obtain the interval of length ef; the selection
indices satisfy the same identity. Cone coordinates give arithmetic composition.
Naturality of selection and each transition sum gives the last arithmetic
square with the coefficient associator. The constructions include zero quotient
objects and empty finite bases. -/
theorem finiteFreeQuotientRoosHorizontalCoherence
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b))
    (ordinary : Fa.E ⋙ Fb.E ≅ Fba.E)
    (balanced : ∀ M (U : Cᵒᵖ) (s : S.obj.obj U) (q : V.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (scalarTensorSection Fb (Fa.E.obj M) U q (scalarTensorSection Fa M U s x)) =
          scalarTensorSection Fba M U (b.hom.app U s * q) x)
    (hfreeV : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J V)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (w : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)).sections)
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (ra : RepresentativeRoosComparison Fa.E (sourceTower t P) (targetTower Fa vS P) e)
    (rb : RepresentativeRoosComparison Fb.E (targetTower Fa vS P)
      (targetTower Fb w ((extendedComplex Fa).obj P)) f)
    (rba : RepresentativeRoosComparison Fba.E (sourceTower t P) (targetTower Fba w P) (e * f))
    (hqa : ∀ n : ℕ, (extendedComplex Fa).map (quotientMap R t P n) ≫
      ra.β.hom.app (op n) = quotientMap S vS ((extendedComplex Fa).obj P)
        (e * (n + 1) - 1))
    (hqb : ∀ n : ℕ, (extendedComplex Fb).map
      (quotientMap S vS ((extendedComplex Fa).obj P) n) ≫ rb.β.hom.app (op n) =
      quotientMap V w ((extendedComplex Fb).obj ((extendedComplex Fa).obj P))
        (f * (n + 1) - 1))
    (hqba : ∀ n : ℕ, (extendedComplex Fba).map (quotientMap R t P n) ≫
      rba.β.hom.app (op n) = quotientMap V w ((extendedComplex Fba).obj P)
        ((e * f) * (n + 1) - 1)) :
    ∃ d : RepresentativeComposition ordinary
        (sourceTower t P) (targetTower Fa vS P)
        (targetTower Fb w ((extendedComplex Fa).obj P)) (targetTower Fba w P)
        ((quotientTower V w).map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P))
        e f he ra rb rba,
      roosF.map ((quotientTower V w).map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)) ≫ rba.a =
        d.restricted.a ≫ roosF.map ((complexRestriction _ (e * f)).map
          ((quotientTower V w).map
            ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P))) := by
  sorry

end CategoryTheory.PrincipalQuotientCompletion
