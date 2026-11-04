/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexProjections

import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import all WeilConjectures.Algebra.Homology.HomComplex

/-!
# Internal Hom out of locally finite projective coefficient modules

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation/lem-sf-hom-finite-projective;
Stacks Project, sites-cohomology.tex, Tag 08JJ
(blueprint: lem-sf-hom-finite-projective).

The predicates express the degree-zero cases of the recorded site-perfect local
models. Rational splittings are taken after localization; common-stage objects may
have any isomorphic finite-stage representative. All arrows are the published
normalized evaluation transposes of the given six-functor datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v r w a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

namespace FiniteProjectiveOrdinaryDual

variable {T : Type c} [Category.{v} T] {J : GrothendieckTopology T}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The modules over the recorded coefficient ring, with independent site universes.
Source: Stacks 08JJ, proof step 1 (blueprint: lem-sf-hom-finite-projective). -/
abbrev Modules (R : Sheaf J CommRingCat.{max c v r}) := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- Ordinary sheaf dual, using the declaration of def-pur-sheaf-hom.
Source: Stacks 08JJ, proof steps 2--5 (blueprint: lem-sf-hom-finite-projective). -/
abbrev dual (P : Modules.{c, v, r} R) :=
  SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) P (SheafOfModules.unit _)

set_option linter.unusedSectionVars false in
/-- Evaluation uniquely determines the ordinary bidual map on every slice.
The equal-universe upstream SheafOfModules.bidual has this same formula; here
site objects and morphisms retain their independent universes.
Source: Stacks 08JJ, proof steps 2--3 (blueprint: lem-sf-hom-finite-projective).
Proof: send x to the local functional phi |-> phi(x). Restriction of x to each
slice and evaluation at its identity object commute with further restriction.
Linearity in phi and x follows from the module-map laws. These formulas give a
module-sheaf map. Extensionality on all slice sections proves uniqueness. -/
theorem bidual_existsUnique (P : Modules.{c, v, r} R) :
    ∃! d : P ⟶ dual.{c, v, r} R (dual.{c, v, r} R P),
      ∀ (U : Tᵒᵖ) (x : P.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (dual.{c, v, r} R P).val.obj (op W.unop.left)),
        (((d.val.app U).hom x).app W).hom φ =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (P.val.map W.unop.hom.op x) := by
  refine ⟨ringedSiteSheafBidual.{c, v, r} J R P (SheafOfModules.unit _), ?_, ?_⟩
  · intro U x W φ
    rfl
  · intro d hd
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact hd U x W φ

set_option linter.unusedSectionVars false in
variable [HasDerivedCategory.{w} (Modules.{c, v, r} R)]

end FiniteProjectiveOrdinaryDual

end WeilConjectures
