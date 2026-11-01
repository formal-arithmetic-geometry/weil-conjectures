/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPairingData

/-! # Integral trace and formula pairing data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The two concrete evaluation words are perfect pairings, and the trace word
is contravariantly natural in its constructible argument.
Source: blueprint lem-coef-rational-operations, proof paragraph 8, Steps 2--3 and 11
(blueprint: lem-coef-dual-formula-pairing-perfect).
Proof: resolve the three tensor presentations simultaneously by K-flat complexes.
At each positive quotient use the ordinary pullback/direct-image adjunction and
absolute trace exchange to curry the displayed projection--trace word. Finite
Verdier biduality identifies its inverse with evaluation followed by inverse
biduality. The proper/open projection and structural trace equations show that
these are inverse Hom maps and commute with precomposition. Choose the quotient
resolutions and all restriction units on the same coefficient system. Their
cocycle-compatible mapping-system equivalence descends through derived reduction
and total limit; constructibility supplies the common Tor bounds. Ordinary
internal-Hom evaluation and integral biduality give the second bijection. The
normalized natural Koszul swap and naturality of projection and evaluation give
the last equation before descent, hence after descent as well. -/
theorem formulaPairing_perfect
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (t : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega)
    (ht : TraceNormalized D l hl E f c wX wY t) :
    (∀ (K : sfIntegralConstructibleCategory l E X)
        (M : sfIntegralConstructibleCategory l E Y),
      Function.Bijective (formulaTracePairing D l hl E f c wX wY aX aZ aY sX t K M)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X)
        (M : sfIntegralConstructibleCategory l E Y),
      Function.Bijective (formulaEvaluationPairing D l hl E wY aY
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K.obj) M)) ∧
    (∀ (K K' : sfIntegralConstructibleCategory l E X)
        (M : sfIntegralConstructibleCategory l E Y) (v : K ⟶ K')
        (h : K'.obj ⟶ formulaObject D l hl E f wX wY M),
      formulaTracePairing D l hl E f c wX wY aX aZ aY sX t K M (v.hom ≫ h) =
        aY.tensor.map (Prod.mkHom
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).map v.hom)
          (𝟙 ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
        formulaTracePairing D l hl E f c wX wY aX aZ aY sX t K' M h) := by
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose
