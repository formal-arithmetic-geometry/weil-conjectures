/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SmoothPurity.RationalWeilPurity.RationalWeilPurityNaturalityMate
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusCompactIntegralNormalization

/-! # Normalization of the rational compactification exchange

Source: the compact-support transport in Step 2 of
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md` in the current blueprint.
(blueprint: lem-pur-frobenius-compact-rational-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem transported_app_heq {C T : Type*} [Category* C] [Category* T]
    {F G F' G' : C ⥤ T} (hF : F = F') (hG : G = G') (τ : F ⟶ G) (K : C) :
    HEq (((eqToIso hF).inv ≫ τ ≫ (eqToIso hG).hom).app K) (τ.app K) := by
  subst hF
  subst hG
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Category.id_comp,
    Category.comp_id]
  rfl

/-- The localized proper/open exchange is the normalized rational compact-support
exchange used in the purity counit square, before conjugation by an exceptional
coefficient system.
Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, Step 2.
(blueprint: lem-pur-frobenius-compact-rational-normalization).

Proof: expand the compact branch into the proper mate and inverse open mate at
its retained geometric compactification. The coefficient-normalized pullback
compositors identify these with the proper and open factors of
zlCompactSupportFrobenius. The comparison from completed to ordinary pullback
and the compact-support realization conjugate this composite to integralExchange.
The two intervening realization comparisons cancel. Localization carries this
identity to the rational category, with precisely modelRationalSource_eq and
modelRationalTarget_eq as its endpoint transports. The defining normalization
of rationalExchange identifies its hom with the localization of integralExchange.
Combining the two equalities gives the heterogeneous equality below. The argument
uses the whole quotient tower and its actual transitions, so applies also to
empty schemes and to the identity compactification. -/
theorem frobeniusCompactRational_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    HEq ((FrobeniusExchange.frobeniusRational D l hl E f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K)
      (RationalWeilPurity.rationalExchange D l hl f₀ E c₀ K).hom := by
  have hr :=
    (RationalWeilPurity.rationalExchange_existsUnique D l hl f₀ E c₀ K).exists.choose_spec
  apply HEq.trans ?_ hr.symm
  have hi := frobeniusCompactIntegral_normalization D l hl f₀ E c₀ K.obj
  unfold FrobeniusExchange.frobeniusRational FrobeniusExchange.modelRationalExchange
  refine (transported_app_heq _ _ _ K).trans ?_
  delta FrobeniusExchange.modelSource FrobeniusExchange.modelTarget
    FrobeniusExchange.modelFunctor
  unfold FrobeniusExchange.localizedTransformation FrobeniusExchange.modelExchange
    FrobeniusExchange.frobeniusCompactModel
  change HEq ((sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).map
    ((FrobeniusExchange.frobeniusCompactIntegral D l hl E f₀ c₀).app K.obj)) _
  exact heq_of_eq (congrArg
    (sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).map
    (eq_of_heq hi))

end WeilConjectures
