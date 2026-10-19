/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

import Sheaf.Paper.WeaklyContractibleUnitProjective
import Sheaf.Paper.CompleteResidueCohomologyBounds
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Removing the top residue cell

Source: Stacks Project, proetale.tex, Tag 09C3, top-degree lifting and cone
calculation (blueprint: lem-sf-complete-residue-top-cell).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Remove one top-degree free cell from a complete complex. Its cone is complete
and has a shorter bounded finite-free residue model; at length zero it vanishes.

Source: Stacks Project, proetale.tex, Tag 09C3, induction step; Tag 09C2 for
cohomological bounds; sites-cohomology.tex, Tag 0946 for exact evaluation
(blueprint: lem-sf-complete-residue-top-cell).

Proof:
1. The flat completed coefficient sheaf has quotient by the uniformizer equal
to the constant residue sheaf. Its two-term uniformizer complex is a K-flat
resolution. The epimorphic quotient tower proves that the regular module and
its finite powers and shifts are derived complete.
2. Use the supplied bounded zero-differential finite-free residue model R.
Its explicit termwise bounds place it in [a,a+d]. On the weakly contractible
affine, evaluation is exact, and finite powers of the regular module are projective.
3. Pull R back to any site object. Exact restriction preserves its bounds,
and preserves its finite free terms by the unit and finite-product comparisons.
The bounded flat model tensor calculation gives the same Tor interval there,
for every test module and every resolution. The complete-residue cohomological
bounds therefore give H^(a+d+1)(K)=0. The
uniformizer triangle makes H^(a+d)(K) to H^(a+d)(K_1) epimorphic. Exact
evaluation lifts the top basis through this epimorphism and then to cycles.
These cycles define a map from the single free sheaf in degree a+d into K.
Use that single complex for P and complete the map to the triangle T.
4. Reduction of that map, in the zero-differential residue model, is precisely
the top summand inclusion: bounded projective complexes compute derived maps.
Its cone is the sum of the lower residue summands and a contractible identity
complex. Contract the identity summand to obtain the lower bounded finite-free
complex W and its derived isomorphism with the reduced cone. Its cohomology
stays finite free. Completeness is closed under cones.
5. If d=0 the residue cone is zero. Derived Nakayama makes the integral cone
zero. The coefficient-completion comparison transports this assertion from
the continuous-coefficient completion API to the quotient-tower API here.
Rank zero is permitted. On the empty scheme the zero single complex works.
This statement asserts only one cell removal, not an integral model of K. -/
theorem complete_residue_top_cell
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E S K)
    (a : ℤ) (d : ℕ)
    (hTor : HasProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K) a (a + d))
    (R : CochainComplex
      (proEtaleRingModules S (proEtaleConstantRing S
        (Padic.coefficientExtensionRing l E 1))) ℤ)
    (hR : ∀ i j : ℤ, R.d i j = 0)
    (hRfree : ∀ q : ℤ, ∃ N : ℕ, Nonempty
      (R.X q ≅ ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit.{u, u + 1, u + 1}
        (integralCoefficientSheaf.{u, u} l E S 0)))
    (hRbound : ∀ q : ℤ, q < a ∨ a + d < q → IsZero (R.X q))
    (eR : Nonempty (((scalarReductionDerivedExtension.{u, u} l E S 0).obj K) ≅
      DerivedCategory.Q.obj R)) :
    ∃ T : CategoryTheory.Pretriangulated.Triangle
        (DerivedCategory (integralTowerModules.{u, u} l E S)),
      T ∈ distTriang _ ∧
      Nonempty (T.obj₂ ≅ K) ∧
      (∃ P : CochainComplex (integralTowerModules.{u, u} l E S) ℤ,
        P.IsStrictlyGE (a + d) ∧ P.IsStrictlyLE (a + d) ∧
        (∀ r : ℤ, ∃ N : ℕ, Nonempty
          (P.X r ≅ ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit.{u, u + 1, u + 1}
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E S))) ∧
        Nonempty (T.obj₁ ≅ DerivedCategory.Q.obj P)) ∧
      IsDerivedCompleteUnrestricted.{u, u} l E S T.obj₃ ∧
      (d = 0 → IsZero T.obj₃) ∧
      (∀ d' : ℕ, d = d' + 1 →
        ∃ W : CochainComplex
            (proEtaleRingModules S (proEtaleConstantRing S
              (Padic.coefficientExtensionRing l E 1))) ℤ,
          W.IsStrictlyGE a ∧ W.IsStrictlyLE (a + d') ∧
          (∀ i j : ℤ, W.d i j = 0) ∧
          (∀ q : ℤ, ∃ N : ℕ, Nonempty
            (W.X q ≅ ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit.{u, u + 1, u + 1}
              (integralCoefficientSheaf.{u, u} l E S 0))) ∧
          Nonempty (((scalarReductionDerivedExtension.{u, u} l E S 0).obj T.obj₃) ≅
            DerivedCategory.Q.obj W)) := by
  sorry

end WeilConjectures
