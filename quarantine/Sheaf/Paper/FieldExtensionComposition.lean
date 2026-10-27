/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.FieldExtensionRationalComparisons

/-! # FieldExtensionComposition

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-composition).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace CategoryTheory

/-- The component equation for composing three scalar comparison isomorphisms,
with the prescribed source and target tensor associators. Naming this common expression
avoids re-elaborating its categorical operations in every coefficient realization.
Source: clause (2), coefficient-composition equation
(blueprint: def-sp-field-extension-composition). -/
def FieldScalarCompositionLaw
    {A B C A' B' C' : Type a}
    [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Category.{v} A'] [Category.{v} B'] [Category.{v} C']
    (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
    (S₁ : A ⥤ B) (S₂ : B ⥤ C) (S₃ : A ⥤ C)
    (T₁ : A' ⥤ B') (T₂ : B' ⥤ C') (T₃ : A' ⥤ C')
    (s : S₁ ⋙ S₂ ≅ S₃) (t : T₁ ⋙ T₂ ≅ T₃)
    (i : F ⋙ T₁ ≅ S₁ ⋙ G) (j : G ⋙ T₂ ≅ S₂ ⋙ H)
    (k : F ⋙ T₃ ≅ S₃ ⋙ H) : Prop :=
  ∀ M : A,
    T₂.map (i.hom.app M) ≫ j.hom.app (S₁.obj M) ≫ H.map (s.hom.app M) =
      t.hom.app (F.obj M) ≫ k.hom.app M

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- Successive integral comparisons agree under the published tensor associators.
Source: clause (2), coefficient-composition equation
(blueprint: def-sp-field-extension-composition). -/
structure IntegralComposition (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (mL : IntegralModel P D L j p d)
    (i : IntegralComparison P D j p d E F h mE mF)
    (i' : IntegralComparison P D j p d F L k mF mL)
    (i'' : IntegralComparison P D j p d E L (h.trans k) mE mL) : Prop where
  left : FieldScalarCompositionLaw
    (support P D j p d mE) (support P D j p d mF) (support P D j p d mL)
    (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
    (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
    (scalarAssoc P h k X) (scalarAssoc P h k Y)
    i.comparison.left i'.comparison.left i''.comparison.left
  right : FieldScalarCompositionLaw
    (exceptional P D j p d mE) (exceptional P D j p d mF) (exceptional P D j p d mL)
    (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
    (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
    (scalarAssoc P h k Y) (scalarAssoc P h k X)
    i.comparison.right i'.comparison.right i''.comparison.right
  source : FieldScalarCompositionLaw
    (puritySource P D j p d mE) (puritySource P D j p d mF) (puritySource P D j p d mL)
    (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
    (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
    (scalarAssoc P h k Y) (scalarAssoc P h k X)
    i.sourceComparison i'.sourceComparison i''.sourceComparison

/-- Successive rational comparisons obey exactly the same tensor-associator equations.
Source: clause (3), coefficient-composition compatibility
(blueprint: def-sp-field-extension-composition). -/
structure RationalComposition (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (mL : IntegralModel P D L j p d)
    (i : IntegralComparison P D j p d E F h mE mF)
    (i' : IntegralComparison P D j p d F L k mF mL)
    (i'' : IntegralComparison P D j p d E L (h.trans k) mE mL)
    (rE : RationalModel P D j p d E mE) (rF : RationalModel P D j p d F mF)
    (rL : RationalModel P D j p d L mL)
    (r : RationalComparison P D j p d E F h mE mF i rE rF)
    (r' : RationalComparison P D j p d F L k mF mL i' rF rL)
    (r'' : RationalComparison P D j p d E L (h.trans k) mE mL i'' rE rL) : Prop where
  left : FieldScalarCompositionLaw
    rE.support.functor rF.support.functor rL.support.functor
    (rationalScalar P h X) (rationalScalar P k X) (rationalScalar P (h.trans k) X)
    (rationalScalar P h Y) (rationalScalar P k Y) (rationalScalar P (h.trans k) Y)
    (rationalScalarAssoc P h k X) (rationalScalarAssoc P h k Y)
    r.comparison.left r'.comparison.left r''.comparison.left
  right : FieldScalarCompositionLaw
    rE.exceptional.functor rF.exceptional.functor rL.exceptional.functor
    (rationalScalar P h Y) (rationalScalar P k Y) (rationalScalar P (h.trans k) Y)
    (rationalScalar P h X) (rationalScalar P k X) (rationalScalar P (h.trans k) X)
    (rationalScalarAssoc P h k Y) (rationalScalarAssoc P h k X)
    r.comparison.right r'.comparison.right r''.comparison.right
  source : FieldScalarCompositionLaw
    rE.source.functor rF.source.functor rL.source.functor
    (rationalScalar P h Y) (rationalScalar P k Y) (rationalScalar P (h.trans k) Y)
    (rationalScalar P h X) (rationalScalar P k X) (rationalScalar P (h.trans k) X)
    (rationalScalarAssoc P h k Y) (rationalScalarAssoc P h k X)
    r.source r'.source r''.source

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
