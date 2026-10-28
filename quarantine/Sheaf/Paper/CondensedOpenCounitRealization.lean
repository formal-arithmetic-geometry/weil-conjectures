module

public import Sheaf.Paper.CondensedOpenCounitUnits
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.CondensedTateRealization
public import Sheaf.Paper.ExceptionalRealizationNormalization
public import Sheaf.Paper.CompactSupportRealizationFactorNormalization
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import Sheaf.Paper.CondensedOpenCoefficientModels
import Sheaf.Paper.CondensedOpenUnitComparison

/-! # Condensed realization of the specified open counit theorem

Source: current blueprint, sec-smooth-purity, sk-thm-purity-transport, proof Steps 2--3;
agent-formulated normalization of the ordinary completed open adjunction
(blueprint: lem-pur-condensed-open-counit-realization).

## Main statements

- `condensed_open_counit_realization`: the specified counit equation and Tate-unit square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open CondensedERealization CompactSupportCondensedRealization
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

open CondensedExceptionalReconstruction

/-- Condensed realization preserves the specified completed open counit and the
specified degree-zero Tate units, with no extra geometric hypotheses.
Source: current blueprint sec-smooth-purity, sk-thm-purity-transport, Steps 2--3;
agent-formulated normalization (blueprint: lem-pur-condensed-open-counit-realization).

Proof:
1. Finite type over k implies noetherianity and finite dimension; distinct primes
make l invertible. Apply integral compact-support preservation to (j,id) and the
completed-pullback realization theorem to j. Thus the ordinary open operations
preserve the recorded integral category. Restrict their actual adjunction.
2. The section-derived open-adjunction normalization identifies the specified
internal and ringed-site adjunctions, including their actual Hom bijections and
counits. J is actual derived scalar extension. Successive scalar-extension
associativity and K-flat pullback identify scalarRestriction with the stipulated s.
3. Use the compact-support factorization with the trivial compactification.
Naturality of the actual reconstruction unit and alpha R(q)=r show that
(d L(alpha) u) q = 1, so the specified integralIdentification is q inverse.
Substituting the factorization of a and removing identity proper factors cancel
J(q inverse) J(t inverse). The resulting b is the composite of the two
unit-normalized open scalar comparisons, first to E and then to Omega.
4. For either scalar extension F, transpose the two maps from j_! F j^* K to F K
under the actual open Hom bijection. The unit-adjunct normalization and the two
triangle identities make both transposes s_K. Injectivity gives counit
compatibility. Apply this twice, use naturality of the second open comparison,
and cancel the intervening coefficient factors to obtain CounitNormalized.
5. The open reduction comparison gives the same identity already in the derived
strict-system category, SystemCounitNormalized. The actual reconstruction unit
transports it to the integral counit used above; evaluations do not select a lift.
6. At d=0 the Tate comparison is coefficient multiplication. Its ordinary
transpose is the actual coefficient inclusion on every section, exactly ScalarUnit.
Restriction sends a
scalar tensor to the same restricted tensor, so multiplication commutes with s.
The lower side is precisely the inverse monoidal pullback unit. This gives
UnitNormalized. All arguments include zero objects, empty opens and j=id. -/
theorem condensed_open_counit_realization :
    ∃ (C : Models l k) (units : ∀ T : Base k, ScalarUnit l k C.coefficient T),
      FactorNormalized l k C ∧ SystemCounitNormalized l k C ∧ UnitNormalized l k C units ∧
      ∀ (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
        [j.IsOver (Spec (.of k))], ∃ h : Preserves l k U Y j,
        (∀ M : Integral l (Field.{u} l) U.scheme,
          IsIso (integralIdentification l k C U Y j h M) ∧
          IsIso (extensionComparison l k C U Y j h M)) ∧
        CounitNormalized l k C U Y j h := by
  obtain ⟨C, units, hfactor, hsystem, hunit⟩ := condensed_open_coefficient_models l k
  refine ⟨C, units, hfactor, hsystem, hunit, ?_⟩
  intro U Y j _ _
  exact condensed_open_unit_comparison l k C hfactor U Y j


end WeilConjectures.CondensedOpenCounitRealization
