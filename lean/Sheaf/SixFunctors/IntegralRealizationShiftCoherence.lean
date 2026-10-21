/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.SynchronizedCanonicalMaps

import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.PurReductionLimitShiftAdjunction
import Sheaf.SixFunctors.GeneratorReductionStatement
import Sheaf.SixFunctors.IntegralBasicOperationShift
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.IntegralRealizationRecursion
import Sheaf.SixFunctors.OpenAdjunctionShift
import Sheaf.SixFunctors.SystemPrimitiveComparisonShift

/-! # Slotwise shift coherence of the specified integral realization

Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2
(blueprint: lem-pur-integral-realization-shift-coherence).

Input labels name occurrences. Their object values may be equal. The supplied
Realizations record is the actual comparison, with its primitive normalizations,
not a newly selected endpoint isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open Classical in
/-- The displayed realization square, including closure of its full domain under
one independently labelled input shift.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def RealizationShiftSquare (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) {I : Type u} [Finite I]
    {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
    (e : IndependentExpression _ I X W) (ge : e.val.geometric)
    (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ) : Prop :=
  ∃ h : e.val.domain l E o (Function.update K.obj i ((K.obj i)⟦r⟧)),
    (R.comparison e.val ge).hom.app ⟨Function.update K.obj i ((K.obj i)⟦r⟧), h⟩ ≫
        (e.integralShift l E K.obj i r).hom =
      (e.sourceShift l E o K.obj i r).hom ≫
        ((R.comparison e.val ge).hom.app K)⟦r⟧'

open Classical in
/-- The shift squares for the same system/integral canonical map, evaluated at
the original and shifted input families, with their actual output maps.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def CanonicalMapShiftSquares {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e t : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj K))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K)
    (sNew : e.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))) ⟶
      t.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))))
    (vNew : (e.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧)) ⟶
      (t.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧))) : Prop :=
  (coefficientSequenceLimit l E W.left).map sNew ≫
      (t.sourceShift l E o K i r).hom =
    (e.sourceShift l E o K i r).hom ≫
      ((coefficientSequenceLimit l E W.left).map s)⟦r⟧' ∧
  vNew ≫ (t.integralShift l E K i r).hom =
    (e.integralShift l E K i r).hom ≫ v⟦r⟧'

open Classical in
/-- Shift every specified canonical map by retaining its constructor and finite
outer expression contexts. Existence covers every old canonical map; the universal
clause covers every evaluation of the same formal construction at the shifted inputs.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def CanonicalMapShiftCoherence (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) {I : Type u} [Finite I]
    {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
    (e t : IndependentExpression _ I X W) (K : (e.val.domain l E o).FullSubcategory)
    (i : I) (r : ℤ) : Prop :=
  ∀ (s : e.val.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj K.obj))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K.obj),
    CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
      R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e.val t.val s v →
    (∃ sNew vNew,
      SynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
          R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj
          ((inputReduction l E X).obj (Function.update K.obj i ((K.obj i)⟦r⟧)))
          (Function.update K.obj i ((K.obj i)⟦r⟧)) e.val t.val s v sNew vNew) ∧
      ∀ sNew vNew,
        SynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
          R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj
          ((inputReduction l E X).obj (Function.update K.obj i ((K.obj i)⟦r⟧)))
          (Function.update K.obj i ((K.obj i)⟦r⟧)) e.val t.val s v sNew vNew →
        CanonicalMapShiftSquares l E o e t K.obj i r s v sNew vNew

/-- The actual canonical integral realization commutes with a shift in any one
independent leaf, naturally in all input objects, and with every specified
canonical map and every finite expression context.
Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2
(blueprint: lem-pur-integral-realization-shift-coherence).

Proof: the exact cochain and right-derived shift comparisons commute with their
adjunction units and counits. Reduction uses the mate through the fixed reconstruction
adjunction, so both its unit and counit commute with these shifts. On K-flat tensor
models use coefficient 1 in the first input and (-1)^(ri) in the second input of
a total tensor summand of first degree i. These maps commute with every quotient
transition. Products preserve the resulting reindexing. On Cone(1-s) use diagonal
coefficients (1,(-1)^r), and then the fixed [-1] comparison. The normalized limit/Roos
identity identifies this with the canonical limit shift. Applied to a representative
of S_p J_j R(K), this is precisely the actual compact-support tower and its given
integral shift normalization, rather than an isomorphic replacement tower.

Now induct on the expression tree, following the unique selected occurrence.
For a variable, c is the inverse reconstruction unit, so its square follows from
the unit shift equation. At pullback and tensor vertices insert the specified
realization-model comparison and the inverse counit used by Realizations. The
representative-normalized primitive comparison and the counit shift equation give
the square; functoriality and the induction square finish it. Proper image uses its
right-derived comparison and open extension uses its exact localized unit-normalized
comparison. The compact-support case is their prescribed composite with the same
strict tower and cone normalization just checked. Shifts preserve completeness,
constructibility, normalized transitions and compatible origins. The cohomological
and Tor intervals translate by the selected integer along its path, and remain
uniform in all positive levels. This proves domain closure as well as the first
square. The shift comparisons are natural in all inputs by shift_naturality, and
c is the supplied natural comparison, giving the required natural square.

For maps, induct on the canonical generator and context construction. Units and
counits use their shift equations; compositors use uniqueness of the normalized
derived factorization; pull/tensor and open/proper comparisons use their respective
cochain or adjunction-mate normalization. Projection and exchange are the specified
composites of these maps, so pasting their squares gives the result. The integral
basic maps are transported through the actual completion units; those units are
shift compatible by the same normalized construction. Identity and composition
paste squares. Each unary outer context preserves the square by functoriality;
each tensor context uses the selected signed input comparison. Simultaneously the
same induction constructs the synchronized shifted map and all intermediate domain
witnesses, so every original canonical map is covered. The construction also proves
the square for every synchronized witness, without choosing unrelated maps at the
two families. This proves the second clause, including arbitrary finite contexts. -/
theorem integralRealizationShiftCoherence (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o) :
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ),
      RealizationShiftSquare l E D o R e ge K i r) ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e t : IndependentExpression _ I X W)
      (_ge : e.val.geometric) (_gt : t.val.geometric)
      (K : (e.val.domain l E o).FullSubcategory) (_ht : t.val.domain l E o K.obj)
      (i : I) (r : ℤ), CanonicalMapShiftCoherence l E D o R e t K i r) := by
  sorry

end WeilConjectures.IntegralSystemRealization
