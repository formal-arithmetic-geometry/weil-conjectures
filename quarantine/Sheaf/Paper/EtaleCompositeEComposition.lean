/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Composite normalized etale comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
thm-pur-composition-coherence.proof.md, Step 1.
(blueprint: lem-pur-etale-composite-e-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open FiniteEtaleNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- The normalized E comparison for a composite etale source is the canonical
exceptional compositor followed by the two normalized source comparisons.
Source: thm-pur-composition-coherence.proof.md, Step 1, composition law for rho
and naturality of rho_H; this is the strict partial step used by the tower theorem.
Proof: Expand E_HJ,q as exceptional composition followed by rho_HJ at omega_q.
Pass compact-support composition associativity through adjunction conjugation
using mate pasting. This identifies the two exceptional compositors for the
triple (H,J,q), with the displayed associativity congruence. Substitute the
normalization composition law for rho_HJ. Naturality of rho_H at the exceptional
compositor for (J,q) replaces its exceptional pullback by its ordinary pullback.
Cancel the pullback compositor and its inverse, and regroup the remaining factors
as E_H,Jq and H-pullback of E_J,q. Postcompose with the inverse pullback compositor
to obtain exactly the equation below. This uses neither smoothness nor a square;
identity arrows and empty schemes are included in the same coherence laws.
(blueprint: lem-pur-etale-composite-e-composition). -/
theorem etale_composite_e_composition
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B A R W : Scheme.{u}}
    [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    [A.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of P.field.k))]
    [QuasiCompact (A ↘ Spec (.of P.field.k))]
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    (q : A ⟶ B) [q.IsOver (Spec (.of P.field.k))]
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (J : R ⟶ A) [J.IsOver (Spec (.of P.field.k))]
    [IsSeparated J] [LocallyOfFiniteType J] [QuasiCompact J]
    (H : W ⟶ R) [H.IsOver (Spec (.of P.field.k))]
    [IsSeparated H] [LocallyOfFiniteType H] [QuasiCompact H]
    [Etale J] [Etale H] :
    (sourceEtale P (H ≫ J) q).hom =
      (FiniteEtaleNormalization.congr P ((H ≫ J) ≫ q)
        (H ≫ J ≫ q) (Category.assoc H J q)).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
      (sourceEtale P H (J ≫ q)).hom ≫
      (pull P H).map (sourceEtale P J q).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
        (omega P q) := by sorry

end AlgebraicGeometry.ProEtale
