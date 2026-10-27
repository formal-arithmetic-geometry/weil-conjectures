module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.FieldCohenPowerSeriesFormallySmooth
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.FiniteOverCompleteRing

/-!+# Compatible coefficient DVRs in the complete Epp construction

Source: Stacks Project, More on Algebra, Tag 09F9, proof of `theorem-epp`,
the final two coefficient-ring preparation paragraphs
(blueprint: lem-sfb-epp-compatible-coefficient-dvrs).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsDiscreteValuationRing

/-- A complete local inclusion admits the compatible coefficient-DVR square used in Epp's
theorem. Residue identifications are specified ring equivalences; the finite-dimensional
fraction-field conclusion uses the canonical extension of the upper inclusion. In equal
characteristic, the power-series identification respects constants and the chosen parameter.

Source: Stacks Project, More on Algebra, Tag 09F9, proof of `theorem-epp`, final two
coefficient-ring preparation paragraphs
(blueprint: lem-sfb-epp-compatible-coefficient-dvrs).

Proof:
1. Use lem-weil-pbc-cohen-rings-exist and
   lem-weil-pbc-cohen-ring-lift-complete-local to lift a Cohen ring with residue k into A.
   This map is local. In characteristic zero it is injective, since a nonzero element is
   a unit times a power of p. In characteristic p it factors through k, giving a residue
   section k to A.
2. In equal characteristic set A0 = k[[t]] and D = l[[t]]. The power-series completeness
   theorem lem-weil-pbc-power-series-field-cohen-regular-complete and
   lem-sc-principal-ideal-dvr make them complete DVRs. Evaluate t at the fixed uniformizer
   using lem-weil-pbc-power-series-adic-evaluation. Recursive extraction of residue digits
   proves surjectivity onto A; the first nonzero coefficient proves injectivity. Map
   k[[t]] into l[[t]] by coefficient inclusion, preserving t and the residue inclusion.
3. In characteristic zero take A0 to be the Cohen ring from step 1 and choose a Cohen
   ring D for l. The zero-variable case of
   lem-weil-pbc-field-cohen-power-series-formally-smooth and
   lem-weil-pbc-fs-adic-lift-into-complete lift A0 to D with the prescribed residue map.
   It sends p to p, so is injective and local and extends the maximal ideal to that of D.
4. Algebraic closedness makes k perfect. The separating transcendence bases supplied by
   lem-weil-pbc-perfect-field-separating-basis for every finitely generated subextension
   show separability in the sense of def-weil-pbc-separable-field-extension, without
   finite generation of l/k. Apply lem-sfb-dvr-index-one-adic-formal-smoothness to A0 to D.
5. Regard B as an A0-algebra through A. Apply lem-weil-pbc-fs-adic-lift-into-complete to
   D, B, and the maximal ideal of B to lift the residue identity. This gives D to B
   commuting with the given map from A0. Its residue map is an isomorphism, hence it is
   local. The common parameter maps to p, or to the image of the fixed uniformizer of A;
   this is nonzero, proving injectivity by unit-times-parameter-power factorization.
6. If q is the parameter of D and beta that of B, write b(q) = unit * beta^e, e positive.
   Residue digit extraction shows that 1, beta, ..., beta^(e-1) span B/qB over D/qD.
   The q-adic filtration on B is separated since qB is a positive power of its maximal
   ideal. Apply lem-weil-pbc-finite-over-complete-ring to conclude that B is finite over D.
7. Localizing B at the nonzero elements of D gives a finite-dimensional domain over
   Frac(D). Multiplication by a nonzero element is injective, hence surjective, so this
   domain is a field. It contains B inside Frac(B), hence equals Frac(B). This proves
   the stated fraction-field finiteness with the canonical scalar map. All residue
   identifications, the commutative square, and the specified parameter are preserved.
-/
theorem exists_epp_compatible_coefficient_dvrs
    (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f)
    [CharP (IsLocalRing.ResidueField A) p] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hcore : Set.range (IsLocalRing.ResidueField.map f) =
      ⋂ n : ℕ, Set.range (fun x : IsLocalRing.ResidueField B ↦ x ^ (p ^ n)))
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) :
    ∃ (A₀ : Type u) (D : Type v) (_ : CommRing A₀) (_ : CommRing D)
      (_ : IsDomain A₀) (_ : IsDomain D)
      (_ : IsDiscreteValuationRing A₀) (_ : IsDiscreteValuationRing D)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal D) D)
      (a : A₀ →+* A) (h : A₀ →+* D) (b : D →+* B)
      (_ : IsLocalHom a) (_ : IsLocalHom h) (_ : IsLocalHom b)
      (_ : Function.Injective a) (_ : Function.Injective h) (hb : Function.Injective b)
      (eA : IsLocalRing.ResidueField A₀ ≃+* IsLocalRing.ResidueField A)
      (eD : IsLocalRing.ResidueField D ≃+* IsLocalRing.ResidueField B),
      b.comp h = f.comp a ∧
      IsLocalRing.ResidueField.map a = eA.toRingHom ∧
      IsLocalRing.ResidueField.map b = eD.toRingHom ∧
      eD.toRingHom.comp (IsLocalRing.ResidueField.map h) =
        (IsLocalRing.ResidueField.map f).comp eA.toRingHom ∧
      Ideal.map h (IsLocalRing.maximalIdeal A₀) = IsLocalRing.maximalIdeal D ∧
      @Module.Finite D B _ _ b.toAlgebra.toModule ∧
      @FiniteDimensional (FractionRing D) (FractionRing B) _ _
        (IsFractionRing.map (K := FractionRing D) (L := FractionRing B) hb).toAlgebra.toModule ∧
      (CharP (FractionRing A) p →
        ∃ e : PowerSeries (IsLocalRing.ResidueField A) ≃+* A₀,
          a (e PowerSeries.X) = π ∧ Function.Bijective a ∧
          ∀ c : IsLocalRing.ResidueField A,
            eA (IsLocalRing.residue A₀ (e (PowerSeries.C c))) = c) ∧
      (CharZero (FractionRing A) → IsCohenRing p A₀ ∧ IsCohenRing p D) := by
  sorry

end IsDiscreteValuationRing
