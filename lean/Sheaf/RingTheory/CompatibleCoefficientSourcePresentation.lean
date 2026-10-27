module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Algebra.Algebra.Rat
import WeilConjectures.RingTheory.CoefficientResidueSection
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Compatible coefficient fields and a source Cohen presentation

Source: Stacks Project, algebra.tex, Tag 032A, characteristic-zero coefficient fields
and the final presentation paragraph; more-algebra.tex, Tag 07NJ; varieties.tex,
Tag 0C52, final paragraph
(blueprint: lem-trf-compatible-coefficient-source-presentation).

The quotient equivalence is specified on every series. Its scalar compatibility
follows from this equation and the prescribed values of `q` on constants. Its
maximal ideal is the inverse image of the maximal ideal of `A`; completeness is
stated for this ideal, so no auxiliary choice of a local-ring structure is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace IsLocalRing

/-- Compatible residue-field sections and a continuous source power-series presentation.
Source: Stacks Project, Tags 032A, 07NJ and 0C52, with the compatible-section refinement
in the DAG (blueprint: lem-trf-compatible-coefficient-source-presentation).

Proof:
1. Use `lem-weil-pbc-coefficient-residue-section` to choose a section `a` of the
residue map of `A`. The composite `f.comp a` gives `B` its residue-compatible
`ResidueField A`-algebra structure.
2. The arbitrary characteristic-zero residue-field extension is formally smooth by
`lem-weil-pbc-char-zero-field-extension-formally-smooth`. Apply
`lem-weil-pbc-fs-adic-lift-into-complete` with source ideal zero, target `B`,
`I = J = maximalIdeal B` and `r = t = 1`. The residue identity lifts to a section
`b`, whose scalar compatibility is `b.comp (ResidueField.map f) = f.comp a`.
3. Noetherianity supplies a finite generating tuple `x` for `maximalIdeal A`,
possibly empty. Apply `lem-trf-coefficient-field-generator-presentation` to the
fixed section `a` and this tuple. It gives continuous surjective `q`, with the
specified constants and variables and inverse image of the maximal ideal equal
to the variable ideal.
4. By `lem-weil-pbc-power-series-local-ring` the series ring is local. Its maximal
ideal is the variable ideal: group each nonconstant monomial by its first variable
with positive exponent to express a zero-constant series as a sum of `X i * F i`.
Thus `q` is local and its kernel lies in that ideal.
5. Surjectivity gives the induced quotient ring equivalence `E`. Its value on a
class of a series is `q` of that series, hence it respects the coefficient section.
Since `q` maps the variable ideal onto `maximalIdeal A`, it maps every power onto
the corresponding power. The equivalence therefore identifies the maximal ideals,
all adic quotients and both adic topologies. Completeness transports from `A` to
the quotient. This is an isomorphism of complete local algebras over the residue
field, with the algebra structure on `A` supplied by `a`. -/
theorem exists_compatible_coefficient_source_presentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra ℚ A] [Algebra ℚ B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (a : ResidueField A →+* A) (b : ResidueField B →+* B),
      (residue A).comp a = RingHom.id (ResidueField A) ∧
      (residue B).comp b = RingHom.id (ResidueField B) ∧
      b.comp (ResidueField.map f) = f.comp a ∧
      ∃ (e : ℕ) (x : Fin e → A)
        (q : MvPowerSeries (Fin e) (ResidueField A) →+* A),
        (∀ i : Fin e, x i ∈ maximalIdeal A) ∧
        Ideal.span (Set.range x) = maximalIdeal A ∧
        Function.Surjective q ∧ IsLocalHom q ∧
        @Continuous _ A
          (Ideal.span (Set.range
            (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) (ResidueField A)))).adicTopology
          (maximalIdeal A).adicTopology q ∧
        (∀ c : ResidueField A, q (MvPowerSeries.C c) = a c) ∧
        (∀ i : Fin e, q (MvPowerSeries.X i) = x i) ∧
        RingHom.ker q ≤ Ideal.span (Set.range
          (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) (ResidueField A))) ∧
        ∃ E : (MvPowerSeries (Fin e) (ResidueField A) ⧸ RingHom.ker q) ≃+* A,
          (∀ F : MvPowerSeries (Fin e) (ResidueField A),
            E (Ideal.Quotient.mk (RingHom.ker q) F) = q F) ∧
          IsAdicComplete ((maximalIdeal A).comap E.toRingHom)
            (MvPowerSeries (Fin e) (ResidueField A) ⧸ RingHom.ker q) := by
  sorry

end IsLocalRing
