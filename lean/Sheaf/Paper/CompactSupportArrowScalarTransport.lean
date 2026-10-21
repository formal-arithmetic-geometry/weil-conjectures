/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfIntegralConstructible

/-! # Tower coherence for scalar transport of compact-support arrows

Source: Weil blueprint, thm-pur-rational-and-qbar-purity, coefficient-extension
transport; sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-arrow-scalar-transport).

The comparisons are the specified natural comparisons on the recorded integral
compact-support functors. The action on the tensor associator is written using their
normalized proper/open realization, so no extra preservation assumption is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E₀ : Type u) [Field E₀] [Algebra ℚ_[l] E₀] [FiniteDimensional ℚ_[l] E₀]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E₀ →ₐ[ℚ_[l]] E) (j : E →ₐ[ℚ_[l]] F)

/-- The natural tensor associator for the actual completed coefficient inclusions.
It is fixed by the tensor-unit normalized scalar adjunctions, not chosen arbitrarily.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-arrow-scalar-transport). -/
def compactSupportScalarAssociator (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E₀ E i W) ⋙
        pbcDerivedExtend (completedCoefficientMap l E F j W) ≅
      pbcDerivedExtend (completedCoefficientMap l E₀ F (j.comp i) W) :=
  tensorComposition _ _ _ (completedMap_composition l E₀ E i F j W)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Transport an arbitrary compact-support arrow by the inverse of the specified
coefficient comparison. The target is an ambient derived object; in particular it
need not be a coefficient unit or a twist.
Source: blueprint thm-pur-rational-and-qbar-purity, coefficient-extension transport
(blueprint: lem-pur-compact-support-arrow-scalar-transport). -/
def compactSupportArrowScalarTransport
    (M : finiteTorConstructibleIntegralCategory l E₀ X)
    (V : DerivedCategory (scalarReductionSource l E₀ Y))
    (t : (recordedSupport l E₀ D hl f c).obj M ⟶ V) :
    (recordedSupport l E D hl f c).obj ((scalarFiniteTor l E₀ E i D hl f c).obj M) ⟶
      (pbcDerivedExtend (completedCoefficientMap l E₀ E i Y)).obj V :=
  (recordedComparisonIso l E₀ E i D hl f c).inv.app M ≫
    (pbcDerivedExtend (completedCoefficientMap l E₀ E i Y)).map t

/-- The action of recorded compact support on the tensor associator, expressed in
its canonical ambient realization. Both endpoint identifications are precisely the
Roos-projection normalized `recordedIdentification`; this is the same functor's
arrow, without requiring an extension of its constructible domain.
Source: blueprint sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-arrow-scalar-transport). -/
def compactSupportScalarAssociatorImage
    (M : finiteTorConstructibleIntegralCategory l E₀ X)
    (hA : finiteTorConstructibleIntegral l E X
      ((pbcDerivedExtend (completedCoefficientMap l E₀ E i X)).obj M.obj)) :
    (recordedSupport l F D hl f c).obj
        ((scalarFiniteTor l E F j D hl f c).obj
          ⟨(pbcDerivedExtend (completedCoefficientMap l E₀ E i X)).obj M.obj, hA⟩) ⟶
      (recordedSupport l F D hl f c).obj
        ((scalarFiniteTor l E₀ F (j.comp i) D hl f c).obj M) :=
  (recordedIdentification l F D hl f c).inv.app
      ((scalarFiniteTor l E F j D hl f c).obj
        ⟨(pbcDerivedExtend (completedCoefficientMap l E₀ E i X)).obj M.obj, hA⟩) ≫
    (image (completed l F) c).map ((compactSupportScalarAssociator l E₀ E F i j X).hom.app
      M.obj) ≫
    (recordedIdentification l F D hl f c).hom.app
      ((scalarFiniteTor l E₀ F (j.comp i) D hl f c).obj M)

/-- Scalar transport of an arbitrary arrow is coherent through a coefficient tower.
Source: blueprint thm-pur-rational-and-qbar-purity, coefficient-extension transport;
sk-thm-purity-transport, Step 3
(blueprint: lem-pur-compact-support-arrow-scalar-transport).

Proof: apply `comparison_composition` to the completed changes E₀ to E, E to F,
and E₀ to F, using `completedMap_composition`. Conjugate its endpoints by the
normalized `recordedIdentification`. The definitions of `recordedComparisonIso`
and `compactSupportScalarAssociatorImage` cancel the intervening realization maps,
giving c_D alpha_Y = P_F(alpha_X) c_B B_Y(c_A) on the recorded functors. All three
comparison components are isomorphisms on the stated finite-Tor objects, by
`integralCoefficientComparison`. Cancel c_D and B_Y(c_A) to obtain
c_D inverse P_F(alpha_X) c_B = alpha_Y B_Y(c_A inverse). Postcompose with D_Y(t).
Naturality of the ambient tensor associator at the arbitrary arrow t gives
alpha_Y D_Y(t) = B_Y(A_Y(t)) alpha_Y, in left-to-right composition order.
Functoriality of B_Y and the definition of `compactSupportArrowScalarTransport`
then give the asserted equation. No purity or coefficient-unit identification is used. -/
theorem compactSupportArrowScalarTransport_tower
    (M : finiteTorConstructibleIntegralCategory l E₀ X)
    (V : finiteTorConstructibleIntegralCategory l E₀ Y)
    (hA : finiteTorConstructibleIntegral l E X
      ((pbcDerivedExtend (completedCoefficientMap l E₀ E i X)).obj M.obj))
    (t : (recordedSupport l E₀ D hl f c).obj M ⟶ V.obj) :
    (recordedComparisonIso l E F j D hl f c).hom.app
        ⟨(pbcDerivedExtend (completedCoefficientMap l E₀ E i X)).obj M.obj, hA⟩ ≫
      compactSupportScalarAssociatorImage l E₀ E F i j D hl f c M hA ≫
      compactSupportArrowScalarTransport l E₀ F (j.comp i) D hl f c M V.obj t =
    (pbcDerivedExtend (completedCoefficientMap l E F j Y)).map
        (compactSupportArrowScalarTransport l E₀ E i D hl f c M V.obj t) ≫
      (compactSupportScalarAssociator l E₀ E F i j Y).hom.app V.obj := by
  sorry

end WeilConjectures.PurCompactSupport
