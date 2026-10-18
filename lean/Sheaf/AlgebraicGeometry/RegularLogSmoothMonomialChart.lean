/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.TraceFormula.FsFaceSharpening
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Monomial etale charts over a canonically logged trait

Source: ILO, Expose XVI, Proposition 3.6.5 and its proof, printed p.253;
Definition 3.6.1 and Proposition 3.6.3, printed p.252
(blueprint: lem-per-regular-log-smooth-monomial-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The coordinate ring of the monomial hypersurface, with the single relation
`product(T_i^e_i) - pi`. This is the literal quotient, with no existence choice.
Source: ILO XVI Definition 3.5.11 and Proposition 3.6.5, pp.251,253
(blueprint: lem-per-regular-log-smooth-monomial-chart). -/
abbrev monomialTraitAlgebra (R : Type u) [CommRing R] (π : R) (n : ℕ) (e : Fin n → ℕ) :=
  MvPolynomial (Fin n) R ⧸
    Ideal.span {(∏ i : Fin n, MvPolynomial.X i ^ e i) - MvPolynomial.C π}

/-- The canonical coefficient homomorphism into the monomial hypersurface ring.
Source: ILO XVI Definition 3.5.11 and Proposition 3.6.5, pp.251,253
(blueprint: lem-per-regular-log-smooth-monomial-chart). -/
noncomputable def monomialTraitAlgebraMap
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (e : Fin n → ℕ) :
    R →+* monomialTraitAlgebra R π n e :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

/-- Every regular Noetherian fs log-smooth scheme over a canonically logged trait has,
at each point and for any prescribed uniformizer, a regular affine Noetherian etale
neighbourhood with an etale map over the trait to a monomial hypersurface.

The canonical log structure is specified by an isomorphism, respecting its structural
map, with the actual divisorial presheaf for the generic open `D(pi)`. Thus no arbitrary
log structure is substituted. In the chart hypothesis `Multiplicative (ULift ℕ)` is
exactly the additive monoid of nonnegative integers, in the scheme's universe. The
formula on `chartY` makes each base chart the chart `1 ↦ π₀` of some uniformizer `π₀`
of `R`, chosen chart by chart and independent of the uniformizer `π` of the
conclusion; XVI 3.6.3 (proof Step 2) supplies the charts for `π`. The group map
is injective, and its cokernel may have finite nonzero invertible torsion.

Source: ILO XVI 3.6.5, printed p.253, using XVI 3.6.1--3.6.3, printed p.252
(blueprint: lem-per-regular-log-smooth-monomial-chart).

Proof:
1. The canonical log structure makes the trait log regular: its closed stratum is
its residue field and its characteristic has rank one; at its generic point the log
structure is trivial. Log-smooth preservation makes the source log regular.
2. Choose a geometric point over the given ordinary point. The fixed-uniformizer
chart theorem XVI 3.6.3 gives an etale neighbourhood with a torsion-free fs monoid
and an etale comparison to the toric base change. It is locally Noetherian.
3. The neighbourhood is strict etale over the source. Its characteristic monoids
are therefore those of the source. The regularity/free-characteristic criterion
ILO VI 1.7 and log-smooth preservation VI 1.8 make it regular and log regular.
4. Localize the chart at the face of elements invertible at the chosen geometric
point, after shrinking to invert finitely many face generators. This is an fs
monoid with unit group the group completion of that face. The new toric model is
an open of the old model, and its comparison remains etale by cancellation.
5. The quotient of this localized monoid by its units is its characteristic monoid.
Regularity and log regularity identify it with a finite free monoid N^r.
6. Lift its standard generators. Cancellation shows that the chart is N^r plus its
unit group. This group is finite free, being finitely generated and torsion-free.
Choose signs of a basis so the coordinates of the uniformizer in the unit group
are nonnegative. Injectivity of N into the chart excludes the zero exponent tuple.
7. On monomial bases the monoid ring is a polynomial/Laurent polynomial ring.
Base change to the trait imposes precisely the relation product(T_i^e_i) = pi.
The torus factors specify an open of the advertised polynomial hypersurface;
composing the etale comparison with that open immersion is etale over the trait.
8. Shrink the neighbourhood to a regular affine open about the chosen point.
It is Noetherian; both maps stay etale, the point stays above the given point,
and the exponent tuple has positive length and is not identically zero.
-/
theorem regular_logSmooth_monomial_chart
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (M : EtaleLogStructure (Spec (.of R))) (hfs : M.IsFineSaturated)
    (hcanonical : ∃ e : M.monoidSheaf.obj ≅ divisorialLogPresheaf
        ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)).ι,
      e.hom ≫ divisorialStructuralMap
        ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv π)).ι = M.alpha)
    (X : FineSaturatedLogScheme.{u}) (hregular : IsRegularScheme X.scheme)
    [IsNoetherian X.scheme] (x : X.scheme)
    (f : EtaleLogHom X ⟨Spec (.of R), inferInstance, M, hfs⟩)
    (hcharts : ∀ y : X.scheme, ∃ c : FSLogChart f,
      y ∈ Set.range c.V.hom ∧
      ∃ e : c.P ≃* Multiplicative (ULift.{u} ℕ),
        (∃ π₀ : R, IsLocalRing.maximalIdeal R = Ideal.span {π₀} ∧
          ∀ p : c.P, M.alpha.app (op c.W) (c.chartY p) =
            c.W.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv π₀) ^ (e p).toAdd.down) ∧
        Function.Injective c.groupMap ∧ Finite (CommGroup.torsion c.cokernel) ∧
        (∀ v : c.V.left,
          IsUnit (Nat.card (CommGroup.torsion c.cokernel) : c.V.left.presheaf.stalk v)) ∧
        Smooth c.comparison) :
    ∃ (U : Scheme.{u}) (a : U ⟶ X.scheme) (v : U),
      IsAffine U ∧ IsRegularScheme U ∧ IsNoetherian U ∧ Etale a ∧ a v = x ∧
      ∃ (n : ℕ) (e : Fin n → ℕ), 0 < n ∧ (∃ i, e i ≠ 0) ∧
        ∃ b : U ⟶ Spec (.of (monomialTraitAlgebra R π n e)), Etale b ∧
          b ≫ Spec.map (CommRingCat.ofHom (monomialTraitAlgebraMap R π n e)) =
            a ≫ f.base := by
  sorry

end AlgebraicGeometry
