/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalFormulaComparison
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalPairingData

/-! # Quotient transport of finite projection--trace pairings -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

/-- The explicit finite dual comparison preserves an equality of uncurried pairings,
provided the absolute structural traces have their quotient compatibility square.

Source: current blueprint lem-coef-finite-exceptional, proof paragraph 2; finite Hom
preservation of evaluation and compact-support coefficient preservation of projection.
(blueprint: lem-sf-finite-exceptional-pairing-quotient).

Proof: express all tensor presentations on simultaneous K-flat representatives and use
their signed Hom-complex evaluation normalization. The evaluation equation for the
finite Hom comparison identifies dualQuotientMap's transpose with reduced evaluation
followed by dualizingQuotientMap. The normalized quotient/pullback associator gives the
inner comparison; evaluation naturality cancels its inverse in formulaQuotientIso.
The scalar tensor comparison respects the descended Koszul swap. Apply the proper/open
projection coefficient-change square to move quotient tensor past the projection word.
Insert the assumed trace square to identify its final trace. This makes the entire new
trace pairing equal to reduced old trace pairing, precomposed with the tensor comparison
and the inverse Y-duality comparison. Apply the same evaluation equation on Y to the
right side of the supplied old pairing equality. Naturality moves the support scalar
comparison through g. Its restriction is exactly qMap, so its inverse is the displayed
q.inv component. Both common precomposition factors are isomorphisms: the scalar tensor
comparison and the Y duality comparison are invertible on the finite-Tor domain. Cancel
them. This proves the displayed equality for arbitrary v and g, without using an
exceptional adjunction or the assertion that its coefficient mate is invertible.
Identity quotients reduce to the unit normalizations; zero and empty inputs give zero
maps. Only K and L are assumed finite-Tor constructible, and no quotient is assumed flat. -/
theorem tracePairing_quotient {m n : ℕ} (h : n ≤ m)
    (aXm : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X m))
    (aZm : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z m))
    (aYm : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y m))
    (aXn : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZn : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aYn : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sXm : IntegralVerdier.SignedSymmetry X _ aXm)
    (sXn : IntegralVerdier.SignedSymmetry X _ aXn)
    (hTrace :
      (reduction l E Y h).map (CoefDualFormulaScalarTranspose.finiteTrace D l E f c m) ≫
          dualizingQuotientMap l E D hl Y h =
        (supportMap l E f c h).app (integralDualizingFiniteTerm l E D X m) ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
            (dualizingQuotientMap l E D hl X h) ≫
          CoefDualFormulaScalarTranspose.finiteTrace D l E f c n)
    (K : (domain l E X m).FullSubcategory)
    (L : (domain l E Y m).FullSubcategory)
    (v : K.obj ⟶ (H l E D f m).obj L.obj)
    (g : ((F l E D hl f c m).obj K).obj ⟶ L.obj)
    (hp : tracePairing l E D f c m aXm aZm aYm sXm K L v =
      evaluationPairing l E D m aYm _ L
        ((PurCompactSupport.finiteImageIso l E m c).hom.app K.obj ≫ g)) :
    tracePairing l E D f c n aXn aZn aYn sXn
        ((Q l E X h).obj K) ((Q l E Y h).obj L)
        ((reduction l E X h).map v ≫ (formulaQuotientIso l E D hl f h L).hom) =
      evaluationPairing l E D n aYn _ ((Q l E Y h).obj L)
        ((PurCompactSupport.finiteImageIso l E n c).hom.app ((Q l E X h).obj K).obj ≫
          ((q l E D hl f c h).inv.app K).hom ≫ (reduction l E Y h).map g) := by
  sorry

end WeilConjectures.FiniteExceptional
