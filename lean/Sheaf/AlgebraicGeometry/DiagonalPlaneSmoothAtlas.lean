/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Sheaf.AlgebraicGeometry.Modules.ZeroLocusPullback
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints

/-! # Standard smooth atlas of a diagonal plane hypersurface

Source: Stacks Project, curves.tex, Tag 0BYA; algebra.tex, Tags 00T6 and 00T7,
with unit coefficients over an arbitrary base scheme.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.DiagonalPlaneCurve

noncomputable section

/-- The homogeneous equation with the three specified coefficients, as a section of
O(1) tensor-powered n times. Source: Stacks 0BYA, relative unit-coefficient equation.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def equation (S : Scheme.{u}) (n : ℕ) (a : Fin 3 → Γ(S, ⊤)) :
    𝟙_ (ProjectiveSpace (ULift.{u} (Fin 3)) S).Modules ⟶
      (ProjectiveSpace.twist (ULift.{u} (Fin 3)) S 1).tensorPow n :=
  Scheme.Modules.homOfGlobalSection _
    (∑ i : Fin 3,
      (ProjectiveSpace (ULift.{u} (Fin 3)) S ↘ S).appTop (a i) •
        Scheme.Modules.tensorPowSectionOne
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin 3)) S ⟨i⟩) n ⊤)

/-- The zero scheme of the displayed homogeneous equation, retaining its scheme structure.
Source: Stacks 0BYA and the zero-scheme construction of def-pc-zero-scheme.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def curve (S : Scheme.{u}) (n : ℕ) (a : Fin 3 → Γ(S, ⊤)) : Scheme.{u} :=
  (equation S n a).zeroLocus.subscheme

/-- The specified closed embedding in the projective plane. Source: Stacks 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def ι (S : Scheme.{u}) (n : ℕ) (a : Fin 3 → Γ(S, ⊤)) :
    curve S n a ⟶ ProjectiveSpace (ULift.{u} (Fin 3)) S :=
  (equation S n a).zeroLocus.subschemeι

/-- The structural morphism of the diagonal plane hypersurface. Source: Stacks 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def π (S : Scheme.{u}) (n : ℕ) (a : Fin 3 → Γ(S, ⊤)) : curve S n a ⟶ S :=
  ι S n a ≫ ProjectiveSpace (ULift.{u} (Fin 3)) S ↘ S

/-- The affine equation lambda s^n + mu t^n + nu. Source: Stacks 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def affinePolynomial {R : Type u} [CommRing R] (n : ℕ) (b : Fin 3 → R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.C (b 0) * MvPolynomial.X 0 ^ n +
    MvPolynomial.C (b 1) * MvPolynomial.X 1 ^ n + MvPolynomial.C (b 2)

/-- The actual quotient coordinate ring of one diagonal chart. Source: Stacks 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
abbrev ChartRing {R : Type u} [CommRing R] (n : ℕ) (b : Fin 3 → R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span {affinePolynomial n b}

/-- The class of an affine coordinate s or t. Source: Stacks 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def coordinate {R : Type u} [CommRing R] (n : ℕ) (b : Fin 3 → R) (i : Fin 2) :
    ChartRing n b :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Relations in the order (s,z,t), or (t,z,s). The selected coordinate is first,
and z is its inverse. Source: Stacks 00T6, 00T7 and the calculation in 0BYA.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def localizedRelations {R : Type u} [CommRing R] (n : ℕ) (b : Fin 3 → R)
    (i : Fin 2) : Fin 2 → MvPolynomial (Fin 3) R :=
  ![MvPolynomial.C (b i.castSucc) * MvPolynomial.X 0 ^ n +
      MvPolynomial.C (b (1 - i).castSucc) * MvPolynomial.X 2 ^ n + MvPolynomial.C (b 2),
    MvPolynomial.X 0 * MvPolynomial.X 1 - 1]

/-- The full affine atlas assertion: principal-open cover, the two specified presentations
of the localized rings, and their ordered Jacobian determinants.
Source: Stacks 0BYA and 00T6--00T7, unit-coefficient version.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def HasChartAtlas {R : Type u} [CommRing R] (n : ℕ) (b : Fin 3 → R) : Prop :=
  PrimeSpectrum.basicOpen (coordinate n b 0) ⊔ PrimeSpectrum.basicOpen (coordinate n b 1) = ⊤ ∧
  ∀ i : Fin 2,
    ∃ P : Algebra.SubmersivePresentation R
        (Localization.Away (coordinate n b i)) (Fin 3) (Fin 2),
      P.map = Fin.castLE (by decide : 2 ≤ 3) ∧
      P.relation = localizedRelations n b i ∧
      P.val 0 = algebraMap (ChartRing n b) _ (coordinate n b i) ∧
      P.val 2 = algebraMap (ChartRing n b) _ (coordinate n b (1 - i)) ∧
      P.val 0 * P.val 1 = 1 ∧
      P.jacobian = algebraMap R _ (b i.castSucc * (n : R)) * P.val 0 ^ n

/-- Restrict the base coefficients and reorder them, with e(2) as distinguished coordinate.
Source: Stacks 0BYA, the three standard charts and their permutations.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def chartCoefficients (S : Scheme.{u}) (a : Fin 3 → Γ(S, ⊤)) (V : S.Opens)
    (e : Equiv.Perm (Fin 3)) : Fin 3 → Γ(S, V) :=
  fun j ↦ S.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a (e j))

/-- The intersection of the hypersurface's standard projective chart with an affine base open.
Source: Stacks 0BYA and 01NG.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension) -/
def chartOpen (S : Scheme.{u}) (n : ℕ) (a : Fin 3 → Γ(S, ⊤)) (V : S.Opens)
    (e : Equiv.Perm (Fin 3)) : (curve S n a).Opens :=
  (ι S n a) ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) S ⟨e 2⟩ ⊓
    (π S n a) ⁻¹ᵁ V

/-- A diagonal plane hypersurface with unit coefficients and invertible positive degree
has the asserted standard smooth atlas, is smooth of relative dimension one and H-projective.
Source: Stacks 0BYA, 00T6--00T7 and 02G2, relative unit-coefficient version.
(blueprint: lem-sfb-binomial-chart-smooth-relative-dimension)

Proof:
1. Use lem-weil-pbc-projective-space-standard-charts and the local formula of
   lem-pc-zero-scheme-properties: dividing the equation by the distinguished coordinate to
   the nth power gives precisely affinePolynomial, with the prescribed coordinate ratios.
2. In its quotient, 1 = s*(-nu^(-1)*lambda*s^(n-1)) +
   t*(-nu^(-1)*mu*t^(n-1)). Thus D(s) and D(t) cover, including n=1 and the zero ring.
3. By lem-weil-pbc-principal-localization-open-immersion and
   lem-weil-pbc-ring-localization-universal-property, adjoining z with sz=1 (or tz=1)
   gives the actual principal-open coordinate ring; both inverse maps fix the generators.
4. The first two variable derivatives form [[lambda*n*s^(n-1),z],[0,s]], or the
   analogous matrix for t. Its determinant is lambda*n*s^n (respectively mu*n*t^n),
   with inverse lambda^(-1)*n^(-1)*z^n (respectively mu^(-1)*n^(-1)*z^n).
   These are submersive presentations with three variables and two relations.
5. Apply lem-weil-pbc-standard-smooth-base-change: coefficientwise scalar extension
   preserves relations, determinant and its inverse, with no flatness hypothesis.
   The quotient tensor comparison sends each coordinate to its primed coordinate.
   lem-pc-zero-scheme-pullback identifies these with the actual base-changed charts.
6. By lem-weil-pbc-standard-smooth-is-smooth and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine these opens are smooth over the affine
   base. Apply lem-weil-pbc-smooth-restrict-open-subschemes and
   lem-weil-pbc-smooth-local-on-source to the cover of the entire hypersurface.
7. A field-valued point factors through an affine base open by
   lem-weil-pbc-morphism-factors-through-open-subscheme. The scalar-extended presentations
   have dimension 3-2=1 at every point by
   lem-weil-pbc-standard-smooth-over-field-dimension-at-points. Dimension at a point is
   invariant under open restriction: intersect open neighbourhoods with the chart and
   use lem-weil-pbc-open-subspace-dimension-monotone, or take closures of irreducible chains.
   Hence all field fibres have dimension one at every point, giving relative dimension one.
8. The given closed embedding into projective space with three coordinates proves
   H-projectivity directly by def-kun-projective.
-/
theorem smooth_atlas (S : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n)
    (a : Fin 3 → Γ(S, ⊤)) (ha : ∀ j : Fin 3, IsUnit (a j))
    (hdegree : IsUnit (n : Γ(S, ⊤))) :
    SmoothOfRelativeDimension 1 (π S n a) ∧ IsHProjective (π S n a) ∧
    (∀ (V : S.Opens) (_ : IsAffineOpen V) (e : Equiv.Perm (Fin 3)),
      IsAffineOpen (chartOpen S n a V e) ∧
      ∃ E : ChartRing n (chartCoefficients S a V e) ≃+* Γ(curve S n a, chartOpen S n a V e),
        (∀ r : Γ(S, V), E (algebraMap Γ(S, V) _ r) =
          (π S n a).appLE V (chartOpen S n a V e) inf_le_right r) ∧
        (∀ j : Fin 2, E (coordinate n (chartCoefficients S a V e) j) =
          (ι S n a).appLE
            (ProjectiveSpace.standardOpen (ULift.{u} (Fin 3)) S ⟨e 2⟩)
            (chartOpen S n a V e) inf_le_left
            (ProjectiveSpace.coordRatio (ULift.{u} (Fin 3)) S ⟨e 2⟩ ⟨e j.castSucc⟩)) ∧
        HasChartAtlas n (chartCoefficients S a V e) ∧
        (∀ (R' : Type (max u v)) [CommRing R'] [Algebra Γ(S, V) R'],
          (∃ E' : R' ⊗[Γ(S, V)] ChartRing n (chartCoefficients S a V e) ≃ₐ[R']
              ChartRing n (fun j ↦ algebraMap Γ(S, V) R' (chartCoefficients S a V e j)),
            ∀ j : Fin 2,
              E' (1 ⊗ₜ[Γ(S, V)] coordinate n (chartCoefficients S a V e) j) =
                coordinate n (fun k ↦ algebraMap Γ(S, V) R'
                  (chartCoefficients S a V e k)) j) ∧
          HasChartAtlas n (fun j ↦ algebraMap Γ(S, V) R' (chartCoefficients S a V e j)))) ∧
    ∀ (L : Type u) [Field L] (h : Spec (CommRingCat.of L) ⟶ S)
      (x : (pullback (π S n a) h : Scheme.{u})), topologicalKrullDimAt x = 1 := by
  sorry

end

end AlgebraicGeometry.DiagonalPlaneCurve
