/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.SixFunctors.FiniteExceptional
public import Sheaf.SixFunctors.CompactCoefficientComposition
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteReductionRootCharts
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange

/-!
# Finite coefficient reduction preserves the canonical exceptional mates

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 2 and 4
(blueprint: lem-pur-finite-adjoint-mate-compatibility).

The first three clauses are written in the canonical etale-origin coordinates of
`def-pur-co-smoothness`. Every bounded constructible pro-etale object has such an
origin. Comparison is fully faithful there, preserves the Tor interval, and identifies
pullback, tensor, compact supports and the constructible exceptional adjunction.
Consequently these are equations of the specified pro-etale maps for every input,
independently of its origin witness. The last clause uses the recorded intrinsic
pro-etale finite-Tor subcategories and their normalized adjunction directly.

## Main statements

* `PurityFiniteSetting.finite_adjoint_mate_tensor`: the canonical tensor-map square.
* `PurityFiniteSetting.finite_adjoint_mate_composition`: the exceptional compositor square.
* `PurityFiniteSetting.finite_adjoint_mate_baseChange`: every Cartesian extraordinary square.
* `FiniteExceptional.finite_adjoint_mate_transpose`: the transpose of every morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (m : ℕ+) (hmn : (m : ℕ) ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The tensor-map square, with its actual scalar, pullback, tensor and coefficient-unit
identifications. TensorCompatibility uses the source order f^*K tensor omega and the
canonical counit/projection mate, as in clause 2 of def-pur-co-smoothness.
Source: reduction proof Step 2, tensor formula
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateTensorClause (K : Etale.DerivedCategoryModule P.Coefficient Y) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  Etale.ExceptionalCoefficients.TensorCompatibility
    (RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)) f K

/-- The composition square, with both exceptional coefficient maps and the functorial
image of the second one. Compactifications here are the standing Nagata choices.
Source: reduction proof Step 2, exceptional composition
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateCompositionClause {Z : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (g : Y ⟶ Z) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : Etale.DerivedCategoryModule P.Coefficient Z) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI := hasCompactification_of_finiteType_over_field P.field.k Y Z g
  letI := hasCompactification_of_finiteType_over_field P.field.k X Z (f ≫ g)
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  (Etale.scalarExtension φ X).map ((finiteExceptionalComposition P.Coefficient f g).hom.app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) g).obj K) ≫
      (Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) f).map
        (Etale.ExceptionalCoefficients.mateMap φ g K) =
    Etale.ExceptionalCoefficients.mateMap φ (f ≫ g) K ≫
      (finiteExceptionalComposition
        (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
        f g).hom.app ((Etale.scalarExtension φ Z).obj K)

/-- The extraordinary square for an arbitrary Cartesian square, on any input K.
The coefficient-object comparison is its component at the coefficient unit, followed
by the canonical pullback-unit isomorphism, exactly as in def-pur-co-smoothness.
Source: reduction proof Step 2, inverse-exchange counit mate
(blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
def finiteAdjointMateBaseChangeClause {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : IsPullback u' f' f v) (K : Etale.DerivedCategoryModule P.Coefficient Y) : Prop :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  letI : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  letI := hasCompactification_of_finiteType_over_field P.field.k X' Y' f'
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  (Etale.scalarExtension φ X').map
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app K) ≫
      Etale.ExceptionalCoefficients.mateMap φ f'
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj K) ≫
      (Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) f').map
        ((Etale.scalarPullbackIso φ v).inv.app K) =
    (Etale.scalarPullbackIso φ u').inv.app
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing P.coefficients.l P.extension m))) u').leftDerivedFunctor.map
        (Etale.ExceptionalCoefficients.mateMap φ f K) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap
        (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
        sq).app ((Etale.scalarExtension φ Y).obj K)

variable [Xsep : IsSeparated (X ↘ Spec (.of P.field.k))]
variable [Ysep : IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [fbase : f.IsOver (Spec (.of P.field.k))]

include Xsep Ysep fbase

include P m hmn in
/-- Finite reduction preserves theta, including the coefficient-unit identification.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: (1) use the finite pullback and tensor comparisons of
lem-fix-operation-reduction; (2) express theta as the transpose of inverse projection
followed by the coefficient-unit counit; (3) lem-fix-compact-support-coefficient-change
identifies projection, hence its inverse, under reduction; (4) use the counit equation
of lem-coef-finite-exceptional and the canonical symmetry and unit constraints;
(5) its unit equation identifies the two transposes. The etale-origin comparison
transports this equality to every pro-etale Dctf input. No flat quotient is assumed. -/
theorem finite_adjoint_mate_tensor (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y K) :
    P.finiteAdjointMateTensorClause m hmn f K := by
  sorry

/-- Reduction preserves c_{g,f}, the canonical comparison for exceptional composition.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: (1) lem-sf-compact-coefficient-composition identifies the two pasted left-adjoint
coefficient squares; (2) the counit equation of lem-coef-finite-exceptional identifies
b as the right mate of inverse q; (3) def-weil-pbc-composite-adjunction gives the
successive Hom transposes; (4) lem-weil-pbc-mate-pasting identifies the mate of the
pasted square as b_f followed by f_B^!(b_g); (5) conjugating by the compact-support
compositor replaces its right mate by the specified c. This gives the displayed
square, and full faithful etale-origin comparison gives the pro-etale equation. -/
theorem finite_adjoint_mate_composition {Z : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (K : Etale.DerivedCategoryModule P.Coefficient Z)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Z K) :
    P.finiteAdjointMateCompositionClause m hmn f g K := by
  sorry

/-- Reduction preserves the extraordinary comparison for every Cartesian square.
At the coefficient unit these are precisely the dualizing-object comparisons.
Source: reduction proof Step 2 (blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: (1) expand compact-support exchange as proper exchange followed by open
extension base change (def-exchange-projection); (2) the operation-reduction and
compact-support coefficient comparisons identify both constituents; (3) every input
has etale origin by lem-sf-proetale-constructible-origin, so
thm-cbc-finite-level-proetale inverts this exchange for arbitrary v; (4) transpose
inverse exchange followed by the pulled-back counit; (5) the counit and transpose
identities of lem-coef-finite-exceptional identify the two reductions. At K=A_Y,
apply the canonical pullback-unit and coefficient-unit comparisons. This is the
coefficient-object map of def-pur-co-smoothness, with no flatness condition on v. -/
theorem finite_adjoint_mate_baseChange {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (sq : IsPullback u' f' f v) (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y K) :
    P.finiteAdjointMateBaseChangeClause m hmn f u' f' v sq K := by
  sorry

end PurityFiniteSetting

namespace FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
variable {T U : Scheme.{u}}
  [T.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [IsSeparated (T ↘ Spec (.of D.k))] [IsSeparated (U ↘ Spec (.of D.k))]
variable (h : T ⟶ U) [h.IsOver (Spec (.of D.k))]
  [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (c : Compactification h)

/-- Reduction identifies the actual adjoint transpose for every separated finite-type h.
The indices r and s are predecessors: the coefficient exponents are r+1 and s+1.
Source: reduction proof Step 2, unit calculation for an arbitrary morphism a
(blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: (1) expand the A-transpose as eta followed by G_A(a);
(2) naturality of b at a moves Q(G_A(a)) across b;
(3) the unit normalization of lem-coef-finite-exceptional replaces Q(eta_A)
followed by b and G_B(q) with eta_B; (4) compose with G_B(q inverse) and
G_B(Q(a)), and use functoriality. The result is the B-transpose of
q inverse followed by Q(a). This is precisely def-weil-pbc-adjunction-mate
specialized to a morphism. The domain is the recorded intrinsic small-pro-etale
finite-Tor constructible subcategory, without a smoothness hypothesis on h. -/
theorem finite_adjoint_mate_transpose {r s : ℕ} (hsr : s ≤ r)
    (M : (domain l E T r).FullSubcategory)
    (L : (domain l E U r).FullSubcategory)
    (a : (F l E D hl h c r).obj M ⟶ L) :
    (Q l E T hsr).map
        ((adjunction l E D hl h c r).unit.app M ≫ (G l E D hl h c r).map a) ≫
        (b l E D hl h c hsr).app L =
      (adjunction l E D hl h c s).unit.app ((Q l E T hsr).obj M) ≫
        (G l E D hl h c s).map
          ((q l E D hl h c hsr).inv.app M ≫ (Q l E U hsr).map a) := by
  sorry

end FiniteExceptional
end WeilConjectures
