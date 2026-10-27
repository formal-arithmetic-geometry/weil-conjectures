module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Fraction-algebra charts of a binomial blowup

Source: Stacks Project, Divisors, Tag 0804, and the explicit binomial calculations
extracted from the nodal-chart blowup calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras).
- Chart indices `0,1,2` mean the `x,a,y` charts.
- The two coordinates mean `x,t`, `r,s`, and `y,h`, respectively.
- All abbreviations below specialize existing polynomial, quotient and chart constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.BinomialBlowup

/-- The displayed binomial presentation, Stacks 0804, explicit chart calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
abbrev Ring (R : Type u) [CommRing R] (c : R) :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c}

/-- Coordinate classes in the displayed binomial presentation, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def coord (R : Type u) [CommRing R] (c : R) (j : Fin 2) : Ring R c :=
  Ideal.Quotient.mk _ (MvPolynomial.X j)

/-- The original affine ring `R[x,y]/(xy-a^n)`, Stacks 0804, binomial calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
abbrev Base (R : Type u) [CommRing R] (a : R) (n : ℕ) := Ring R (a ^ n)

/-- The ordered generators `x,a,y` of the centre, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def generator (R : Type u) [CommRing R] (a : R) (n : ℕ) :
    Fin 3 → Base R a n :=
  ![coord R (a ^ n) 0, algebraMap R (Base R a n) a, coord R (a ^ n) 1]

/-- The actual centre ideal, Stacks 0804, binomial calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def center (R : Type u) [CommRing R] (a : R) (n : ℕ) : Ideal (Base R a n) :=
  Ideal.span (Set.range (generator R a n))

/-- The published fraction-subalgebra chart, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable abbrev Chart (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :=
  AffineBlowup.chartRing (center R a n) (generator R a n i)

/-- The relation parameters `a,a^(n-2),a`, Stacks 0804, binomial calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
def parameter (R : Type u) [CommRing R] (a : R) (n : ℕ) : Fin 3 → R :=
  ![a, a ^ (n - 2), a]

/-- The standard Rees basic open at the indicated generator, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def chartOpen (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    (AffineBlowup (center R a n)).Opens :=
  Proj.basicOpen (reesGrading (center R a n))
    (reesX (center R a n) (generator R a n i) (Ideal.subset_span ⟨i, rfl⟩))

/-- The canonical chart map, using the published homogeneous-fraction identification theta;
Stacks 0804 (blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def chartMap (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    Spec (.of (Chart R a n i)) ⟶ AffineBlowup (center R a n) :=
  Spec.map (CommRingCat.ofHom
    (AffineBlowup.homogeneousAwayEquivChart (center R a n)
      (Ideal.subset_span ⟨i, rfl⟩)).toRingHom) ≫
    AffineBlowup.chart (center R a n) _
      (reesX_mem (center R a n) _ (Ideal.subset_span ⟨i, rfl⟩))

/-- The coefficient map on a chart, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def coeff (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    R →+* Chart R a n i :=
  (algebraMap (Base R a n) (Chart R a n i)).comp (algebraMap R (Base R a n))

/-- The extended centre on an affine chart, Stacks 0804 and Schemes 01JU
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def extended (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    Ideal (Chart R a n i) :=
  (center R a n).map (algebraMap (Base R a n) (Chart R a n i))

/-- Coordinate ring of the closed inverse image of the centre on a chart; Stacks 01JU
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable abbrev Exceptional (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :=
  Chart R a n i ⧸ extended R a n i

/-- Quotient map to the exceptional chart, Stacks 01JU
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def exceptionalMk (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    Chart R a n i →+* Exceptional R a n i := Ideal.Quotient.mk _

/-- Closed-chart map into the blowup, Stacks 01JU
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def exceptionalMap (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    Spec (.of (Exceptional R a n i)) ⟶ AffineBlowup (center R a n) :=
  Spec.map (CommRingCat.ofHom (exceptionalMk R a n i)) ≫ chartMap R a n i

/-- The residue coefficient ring `R/(a)`, Stacks 0804, exceptional chart calculation
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
abbrev Residue (R : Type u) [CommRing R] (a : R) := R ⧸ Ideal.span {a}

/-- The exceptional middle-chart relation, including the case `n=2`, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
def epsilon (R : Type u) [CommRing R] (a : R) (n : ℕ) : Residue R a :=
  if n = 2 then 1 else 0

/-- The common ambient rational-function field used in the chart calculation, Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
abbrev Ambient (R : Type u) [CommRing R] [IsDomain R] := RatFunc (FractionRing R)

/-- The actual localization of a chart at a ratio, Stacks 01M4
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable abbrev Overlap (R : Type u) [CommRing R] (a : R) (n : ℕ)
    (z : (i j : Fin 3) → Chart R a n i) (i j : Fin 3) := Localization.Away (z i j)

/-- Coordinates transported through the three presentation isomorphisms; Stacks 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def chartVariable (R : Type u) [CommRing R] (a : R) (n : ℕ)
    (e : (i : Fin 3) → Ring R (parameter R a n i) ≃+* Chart R a n i)
    (i : Fin 3) (j : Fin 2) : Chart R a n i :=
  e i (coord R (parameter R a n i) j)

/-- A coordinate in an overlap localization, Stacks 01M4
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def overlapVariable (R : Type u) [CommRing R] (a : R) (n : ℕ)
    (e : (i : Fin 3) → Ring R (parameter R a n i) ≃+* Chart R a n i)
    (z : (i j : Fin 3) → Chart R a n i) (i j : Fin 3) (k : Fin 2) :
    Overlap R a n z i j :=
  algebraMap _ _ (chartVariable R a n e i k)

/-- The actual overlap map to the blowup, Stacks 01M4
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def overlapMap (R : Type u) [CommRing R] (a : R) (n : ℕ)
    (z : (i j : Fin 3) → Chart R a n i) (i j : Fin 3) :
    Spec (.of (Overlap R a n z i j)) ⟶ AffineBlowup (center R a n) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ chartMap R a n i

/-- A coordinate on the exceptional fibre, Stacks 01JU and 0804
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def exceptionalVariable (R : Type u) [CommRing R] (a : R) (n : ℕ)
    (e : (i : Fin 3) → Ring R (parameter R a n i) ≃+* Chart R a n i)
    (i : Fin 3) (j : Fin 2) : Exceptional R a n i :=
  exceptionalMk R a n i (chartVariable R a n e i j)

/-- The point set of an exceptional chart in the blowup, Stacks 0804 and 01JU
(blueprint: lem-sfb-binomial-blowup-chart-algebras). -/
noncomputable def exceptionalImage (R : Type u) [CommRing R] (a : R) (n : ℕ) (i : Fin 3) :
    Set (AffineBlowup (center R a n)) := Set.range (exceptionalMap R a n i)

/-- Fraction-algebra presentations, standard opens, transition functions and the closed
inverse image of the centre for the blowup of `xy=a^n` at `(x,a,y)`.
Source: Stacks Project, Tag 0804; Algebra Tag 052Q; Constructions Tags 01M4, 01MA;
Schemes Tag 01JU (blueprint: lem-sfb-binomial-blowup-chart-algebras).

Proof plan:
1. Apply `lem-sfb-binomial-laurent-normal-form` to `a^n,a,a^(n-2),a`. Embed the
   base and the three presentations in `Frac(R)(x)`; for the middle and last chart
   substitute `U=x/a` and `V=a^n/x`, with inverses `x=aU` and `x=a^n/V`.
2. The published `AffineBlowup.chartRing` is generated by the ratios of the three
   centre generators. In the first chart `y=x^(n-1)t^n` and `y/x=x^(n-2)t^n`;
   in the middle `x=ar,y=as`; exchange `x,y` for the last chart. Injectivity from
   step 1 identifies these fraction subalgebras with the displayed quotients.
3. Use `prop-nagata-affine-blowup-chart`, its chart map and theta, then
   `prop-nagata-affine-blowup-chart-cover` for the three-generator cover.
4. Apply `lem-weil-pbc-proj-basic-open-intersection` to `bT,cT`, both degree one;
   theta identifies the resulting homogeneous fraction with `c/b`, also if `b=c`.
5. On the first--middle overlap invert `t` and `r`. Then `r=t^-1` and
   `s=x^(n-2)t^(n-1)`; the inverse has `x=ar`. Localization uniqueness
   (`lem-weil-pbc-localization-away-universal-property`) gives inverse ring maps.
   Exchange the two outer charts for the second adjacent overlap.
6. On the outer overlap put `q=x^(n-2)t^n`; then `y=xq,h=t/q`. The reverse
   formulas use `q'=y^(n-2)h^n`; substitution sends `q'` to `q^-1`. The composites
   fix the generators, so localization uniqueness gives inverse transitions.
7. `lem-pc-ideal-sheaf-comap-affine-extension` gives the extended ideals generated
   by the three centre images. They equal `(x),(a),(y)`. Quotient the presentations:
   the outer rings become `(R/(a))[t]` and `(R/(a))[h]`; the middle relation becomes
   `rs=1` for `n=2` and `rs=0` otherwise. The maps fix the displayed variables and
   reduce coefficients modulo `a`, giving inverse quotient homomorphisms.
8. Reduce the transitions. At `n=2`, `r,s` are units, the middle is both adjacent
   overlaps, and `D(t^2)=D(t)` with `h=t^-1`. At `n>2`, `q` reduces to zero,
   so the outer intersection is empty, while the middle overlaps lie on `s=0`
   and `r=0`. Prime ideal arguments work over nonreduced `R/(a)` too. If `a`
   is a unit, all exceptional charts are empty.
-/
theorem binomial_blowup_chart_algebras
    (R : Type u) [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (baseEmbedding : Base R a n →ₐ[R] Ambient R)
      (e : (i : Fin 3) → Ring R (parameter R a n i) ≃+* Chart R a n i)
      (embedding : (i : Fin 3) → Chart R a n i →+* Ambient R)
      (z : (i j : Fin 3) → Chart R a n i),
      Function.Injective baseEmbedding ∧
      baseEmbedding (coord R (a ^ n) 0) = RatFunc.X ∧
      baseEmbedding (coord R (a ^ n) 1) = algebraMap R (Ambient R) a ^ n / RatFunc.X ∧
      (∀ i, Function.Injective (embedding i)) ∧
      (∀ i b, embedding i (algebraMap (Base R a n) (Chart R a n i) b) =
        baseEmbedding b) ∧
      (∀ i c, e i (algebraMap R (Ring R (parameter R a n i)) c) = coeff R a n i c) ∧
      embedding 0 (chartVariable R a n e 0 0) = RatFunc.X ∧
      embedding 0 (chartVariable R a n e 0 1) = algebraMap R (Ambient R) a / RatFunc.X ∧
      embedding 1 (chartVariable R a n e 1 0) = RatFunc.X / algebraMap R (Ambient R) a ∧
      embedding 1 (chartVariable R a n e 1 1) =
        (algebraMap R (Ambient R) a ^ n / RatFunc.X) / algebraMap R (Ambient R) a ∧
      embedding 2 (chartVariable R a n e 2 0) = algebraMap R (Ambient R) a ^ n / RatFunc.X ∧
      embedding 2 (chartVariable R a n e 2 1) =
        algebraMap R (Ambient R) a / (algebraMap R (Ambient R) a ^ n / RatFunc.X) ∧
      (∀ i j, (z i j : Localization.Away (generator R a n i)) =
        AffineBlowup.chartFraction (generator R a n i) 1 (generator R a n j)) ∧
      (∀ i j, chartMap R a n i ⁻¹ᵁ chartOpen R a n j = PrimeSpectrum.basicOpen (z i j)) ∧
      (⨆ i : Fin 3, chartOpen R a n i) = ⊤ ∧
      (∀ i, Set.range (chartMap R a n i) = (chartOpen R a n i : Set _)) ∧
      z 0 1 = chartVariable R a n e 0 1 ∧
      z 1 0 = chartVariable R a n e 1 0 ∧
      z 2 1 = chartVariable R a n e 2 1 ∧
      z 1 2 = chartVariable R a n e 1 1 ∧
      algebraMap (Base R a n) (Chart R a n 0) (coord R (a ^ n) 1) =
        chartVariable R a n e 0 0 ^ (n - 1) * chartVariable R a n e 0 1 ^ n ∧
      z 0 2 = chartVariable R a n e 0 0 ^ (n - 2) * chartVariable R a n e 0 1 ^ n ∧
      algebraMap (Base R a n) (Chart R a n 2) (coord R (a ^ n) 0) =
        chartVariable R a n e 2 0 ^ (n - 1) * chartVariable R a n e 2 1 ^ n ∧
      z 2 0 = chartVariable R a n e 2 0 ^ (n - 2) * chartVariable R a n e 2 1 ^ n ∧
      algebraMap (Base R a n) (Chart R a n 1) (coord R (a ^ n) 0) =
        coeff R a n 1 a * chartVariable R a n e 1 0 ∧
      algebraMap (Base R a n) (Chart R a n 1) (coord R (a ^ n) 1) =
        coeff R a n 1 a * chartVariable R a n e 1 1 ∧
      (∃ (f : Overlap R a n z 1 0 ≃+* Overlap R a n z 0 1)
         (g : Overlap R a n z 1 2 ≃+* Overlap R a n z 2 1)
         (h : Overlap R a n z 2 0 ≃+* Overlap R a n z 0 2),
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫ overlapMap R a n z 1 0 =
          overlapMap R a n z 0 1 ∧
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ overlapMap R a n z 1 2 =
          overlapMap R a n z 2 1 ∧
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ overlapMap R a n z 2 0 =
          overlapMap R a n z 0 2 ∧
        f (overlapVariable R a n e z 1 0 0) = IsLocalization.Away.invSelf (z 0 1) ∧
        f (overlapVariable R a n e z 1 0 1) =
          overlapVariable R a n e z 0 1 0 ^ (n - 2) *
            overlapVariable R a n e z 0 1 1 ^ (n - 1) ∧
        g (overlapVariable R a n e z 1 2 1) = IsLocalization.Away.invSelf (z 2 1) ∧
        g (overlapVariable R a n e z 1 2 0) =
          overlapVariable R a n e z 2 1 0 ^ (n - 2) *
            overlapVariable R a n e z 2 1 1 ^ (n - 1) ∧
        h (overlapVariable R a n e z 2 0 0) =
          overlapVariable R a n e z 0 2 0 ^ (n - 1) *
            overlapVariable R a n e z 0 2 1 ^ n ∧
        h (overlapVariable R a n e z 2 0 1) =
          overlapVariable R a n e z 0 2 1 * IsLocalization.Away.invSelf (z 0 2) ∧
        h.symm (overlapVariable R a n e z 0 2 0) =
          overlapVariable R a n e z 2 0 0 ^ (n - 1) *
            overlapVariable R a n e z 2 0 1 ^ n ∧
        h.symm (overlapVariable R a n e z 0 2 1) =
          overlapVariable R a n e z 2 0 1 * IsLocalization.Away.invSelf (z 2 0)) ∧
      extended R a n 0 = Ideal.span {chartVariable R a n e 0 0} ∧
      extended R a n 1 = Ideal.span {coeff R a n 1 a} ∧
      extended R a n 2 = Ideal.span {chartVariable R a n e 2 0} ∧
      (∃ (q₀ : Exceptional R a n 0 ≃+* Polynomial (Residue R a))
         (q₁ : Exceptional R a n 1 ≃+* Ring (Residue R a) (epsilon R a n))
         (q₂ : Exceptional R a n 2 ≃+* Polynomial (Residue R a)),
        q₀ (exceptionalVariable R a n e 0 1) = Polynomial.X ∧
        q₂ (exceptionalVariable R a n e 2 1) = Polynomial.X ∧
        (∀ j, q₁ (exceptionalVariable R a n e 1 j) =
          coord (Residue R a) (epsilon R a n) j) ∧
        (∀ c, q₀ (exceptionalMk R a n 0 (coeff R a n 0 c)) =
          Polynomial.C (Ideal.Quotient.mk _ c)) ∧
        (∀ c, q₂ (exceptionalMk R a n 2 (coeff R a n 2 c)) =
          Polynomial.C (Ideal.Quotient.mk _ c)) ∧
        (∀ c, q₁ (exceptionalMk R a n 1 (coeff R a n 1 c)) =
          algebraMap (Residue R a) _ (Ideal.Quotient.mk _ c))) ∧
      (∀ i j, (exceptionalMap R a n i) ⁻¹' exceptionalImage R a n j =
        ((PrimeSpectrum.basicOpen (exceptionalMk R a n i (z i j))).carrier)) ∧
      (n = 2 →
        exceptionalImage R a n 1 =
          exceptionalImage R a n 0 ∩ exceptionalImage R a n 2 ∧
        ∃ (f : Exceptional R a n 1 ≃+*
            Localization.Away (exceptionalVariable R a n e 0 1))
          (g : Exceptional R a n 2 →+*
            Localization.Away (exceptionalVariable R a n e 0 1)),
          f (exceptionalVariable R a n e 1 0) =
            IsLocalization.Away.invSelf (exceptionalVariable R a n e 0 1) ∧
          f (exceptionalVariable R a n e 1 1) =
            algebraMap _ _ (exceptionalVariable R a n e 0 1) ∧
          g (exceptionalVariable R a n e 2 1) =
            IsLocalization.Away.invSelf (exceptionalVariable R a n e 0 1) ∧
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ exceptionalMap R a n 1 =
            Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ exceptionalMap R a n 0 ∧
          Spec.map (CommRingCat.ofHom g) ≫ exceptionalMap R a n 2 =
            Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ exceptionalMap R a n 0) ∧
      (2 < n →
        exceptionalImage R a n 0 ∩ exceptionalImage R a n 2 = ∅ ∧
        (∀ p : Spec (.of (Exceptional R a n 1)),
          exceptionalMap R a n 1 p ∈ exceptionalImage R a n 0 →
            exceptionalVariable R a n e 1 1 ∈ p.asIdeal) ∧
        (∀ p : Spec (.of (Exceptional R a n 1)),
          exceptionalMap R a n 1 p ∈ exceptionalImage R a n 2 →
            exceptionalVariable R a n e 1 0 ∈ p.asIdeal)) := by
  sorry

end AlgebraicGeometry.BinomialBlowup
