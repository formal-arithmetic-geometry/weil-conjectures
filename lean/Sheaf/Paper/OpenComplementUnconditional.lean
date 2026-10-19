/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInput
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Sheaf.AlgebraicGeometry.OpenComplementKnown
import Sheaf.Paper.FiniteFieldFiber
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Unconditional bounds for open complements

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
node thm-pur-open-complement-unconditional, statement and proof Steps 1-8
(blueprint: thm-pur-open-complement-unconditional).

## Main statements

* `hasOpenComplementCondition_of_isSepClosed`: bound `2 * d` for every finite
  prime-power-torsion coefficient ring, fixed after the geometric dimension bound.
* `hasOpenComplementCondition_finiteStage`: the same bound at every finite coefficient stage.
* `hasOpenComplementCondition_affineChart`: the chart bound and dimension inequality.
* `hasOpenComplementCondition_emptyChart`: the bound zero when the chart base is empty.

The dimension-zero and curve computations named in the source are independent earlier
computations, not hypotheses of these assertions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The open-complement condition holds with one geometric bound for every finite
prime-power-torsion coefficient ring away from the characteristic.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Steps 1-4
(blueprint: thm-pur-open-complement-unconditional).

Proof:
1. A quasi-compact open immersion is finite type by
   lem-weil-pbc-qc-open-immersion-finite-type. A finite affine cover of T and the
   quasi-compactness of j give a finite affine cover of V
   (lem-pqf-finite-affine-cover-qc-open). The coordinate algebras are finite type by
   lem-weil-pbc-lft-affine-pairs. Thus V is finite type over k. The open embedding gives
   dim V <= dim T <= d by lem-weil-pbc-open-subspace-dimension-monotone.
2. Choose r >= 1 killing A and apply thm-exc-direct-image-input-holds with N = ell^r,
   invertible in k. Its first clause gives constructibility in nonnegative degrees.
   For negative degrees use lem-weil-pbc-derived-functor-negative-vanishing for j_*,
   additive and left exact by def-weil-pbc-direct-image; its module-sheaf categories
   are Grothendieck abelian by lem-weil-pbc-module-sheaves-grothendieck-abelian.
   The zero sheaf is constructible using the constant finite zero module.
3. Apply lem-kun-relative-torsion-direct-image-dimension-bound with X = V, Y = T,
   f = j and the composite structure map of V. The ring A is additively torsion, and
   dim V <= d. This gives vanishing above 2d for all module sheaves, including those
   which are not constructible.
4. These are exactly the two conjuncts of def-exc-open-complement-bound. The natural
   number d is fixed before A, so the bound is independent of coefficients. A bound
   depending only on T exists by lem-kun-dimension-finite-type; for empty T use d = 0.
-/
theorem hasOpenComplementCondition_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    {T V : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)
    (hkill : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0) :
    HasOpenComplementCondition A j (2 * d) := by
  sorry

/-- Every positive finite coefficient stage in the purity conventions has the same
open-complement bound. The existential finite instance records finiteness of the actual
coefficient quotient, rather than requiring it as an extra hypothesis.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Step 5
(blueprint: thm-pur-open-complement-unconditional).

Proof: In the fixed finite-field datum k is algebraically closed of characteristic p.
The coefficient prime ell is different from p. By def-weil-l-adic-coefficient-extension,
A_{E,n} is finite. The absolute value extends the ell-adic absolute value, so
|ell| = ell^(-1) < 1 by def-weil-l-adic-numbers. Thus ell lies in the maximal ideal
(varpi_E), and ell^n lies in (varpi_E^n), killing A_{E,n}. Apply Steps 1-4 above to the
standard ULift of this quotient. The bound 2d contains neither E nor n. This concerns
ordinary small-etale cohomology and uses no pro-etale comparison.
-/
theorem hasOpenComplementCondition_finiteStage
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {T V : Scheme.{u}} [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j] :
    ∃ hA : Finite P.Coefficient,
      @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA V T j
        inferInstance inferInstance (2 * d) := by
  sorry

/-- A nonempty affine chart base B in a finite-type k-scheme Y gives the dimension
inequality m + dim B <= m + dim Y and the bound 2(m + dim B), uniformly at finite stages.
Here b names the natural-number dimension of the nonempty base. Taking a closed chart
inside affine space gives exactly the complements used in thm-pur-general-admissibility.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Steps 6-7
(blueprint: thm-pur-open-complement-unconditional).

Proof: The affine open B has a finite-type coordinate algebra R by
lem-weil-pbc-lft-affine-pairs. The ambient scheme is Spec R[x_1,...,x_m] by
 def-sbc-affine-space. Both rings are Noetherian by lem-wf-affine-noetherian-components.
The polynomial dimension formula lem-sf-noetherian-polynomial-dimension and
lem-weil-pbc-spec-topological-krull-dimension-ring give dim A^m_B = m + b.
The open-subspace dimension inequality gives b <= dim Y. Noetherianity makes the
complement inclusion quasi-compact. Apply the finite-stage assertion with d = m + b.
Every closed affine chart in the separated finite-type assembly has this form; no
preservation or admissibility conclusion of that assembly is used.
-/
theorem hasOpenComplementCondition_affineChart
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (B : Y.Opens) (hB : IsAffineOpen B) [Nonempty B]
    (m b : ℕ) (hb : topologicalKrullDim B.toScheme = (b : WithBot ℕ∞))
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin m)) B.toScheme)
    [IsClosedImmersion i] :
    ((m + b : ℕ) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) + topologicalKrullDim Y ∧
      ∃ hj : QuasiCompact i.openComplement.ι,
        ∃ hA : Finite P.Coefficient,
          @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA
            i.openComplement.toScheme (AffineSpace (ULift.{u} (Fin m)) B.toScheme)
            i.openComplement.ι inferInstance hj (2 * (m + b)) := by
  sorry

/-- An empty affine chart base may be retained: its ambient affine space and complement
are empty, and the open-complement bound is zero at every finite stage.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-open-complement-unconditional, Step 7, empty-chart clause
(blueprint: thm-pur-open-complement-unconditional).

Proof: Affine space over the empty scheme is empty, being a fibre product over it.
Its open complement is empty too. All coefficient sheaves on the empty small-etale
site are zero by the empty covering axiom. Hence all higher direct images vanish and
are constructible, for the bound zero. Finite-stage coefficients are finite by
 def-weil-l-adic-coefficient-extension, as in Step 5. Step 8 of the source only compares
these assertions with the independent dimension-zero and curve computations.
-/
theorem hasOpenComplementCondition_emptyChart
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (B : Y.Opens) (hB : IsAffineOpen B) [IsEmpty B] (m : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin m)) B.toScheme)
    [IsClosedImmersion i] :
    IsEmpty (AffineSpace (ULift.{u} (Fin m)) B.toScheme) ∧
      IsEmpty i.openComplement.toScheme ∧
      ∃ hj : QuasiCompact i.openComplement.ι,
        ∃ hA : Finite P.Coefficient,
          @HasOpenComplementCondition P.Coefficient P.coefficientCommRing hA
            i.openComplement.toScheme (AffineSpace (ULift.{u} (Fin m)) B.toScheme)
            i.openComplement.ι inferInstance hj 0 := by
  sorry

end AlgebraicGeometry.Scheme
