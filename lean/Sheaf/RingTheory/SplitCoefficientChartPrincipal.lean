import WeilConjectures.Blowup.Affine.ChartAlgebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.RingTheory.FibreModuleLocalization

/-! # Principal split-coordinate ideals on affine blowup charts

Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`, chart paragraph
(blueprint: lem-trf-affine-split-coefficient-chart-principal).

The base-changed algebra is written with the chart as the left tensor factor, using the
canonical tensor interchange from the order in the source. Quotient-to-fibre and localization
maps are characterized on their generators, so the asserted maps are the natural ones.
-/

universe u v w z

set_option autoImplicit false

open scoped TensorProduct

namespace AlgebraicGeometry.AffineBlowup.SplitCoefficientChart

/-- The scalar extension of `B` to the chart `R[hC/a]`, with the chart factor first.
This is the ordinary tensor product, with no additional data or choices.
Source: Stacks Project, Tag 0810, chart paragraph
(blueprint: lem-trf-affine-split-coefficient-chart-principal). -/
abbrev baseChange (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (C : Ideal R) (h a : R) : Type (max u v) :=
  chartRing (Ideal.span {h} * C) a ⊗[R] B

/-- Split-coordinate principalization at every fibre-generic chart prime.

Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`, chart paragraph,
with the fibrewise divided-generator argument
(blueprint: lem-trf-affine-split-coefficient-chart-principal).

Proof plan, following the node:
1. The chart is a subring of `R_a`. Since `a = hc`, each of `a,h,c` is a unit in `R_a`,
   and multiplication by it is injective on the chart. Localizing the inclusion at `a`
   is injective and surjective (the image contains `R` and `1/a`), hence an isomorphism.
   The inverse of `h` there is `c/a`. This also holds when the chart is the zero ring.
2. For `d ∈ C`, the chart contains `hd/a`; multiplying this by `c` gives `d`.
   Hence `CR* = (c)`; the converse inclusion uses `c ∈ C`.
3. Flat base change (lem-weil-pbc-flat-module-base-change) gives flatness of `B*`.
   Tensoring the injective multiplication maps of step 1 gives injectivity on `B*`.
4. Base change the split maps `i,ρ`. Divide each coordinate of each generator by `c`
   using `hd/a`, and apply the base-changed retraction to obtain `gν` with `cgν = jν`.
   Injectivity of `c` on coordinates also gives `i*(gν) = vν`, the divided vector.
5. Express `c` as a finite linear combination of the original coordinates. Divide
   that identity by `c`, using step 1: the divided coordinates generate the unit ideal.
   For an empty generator list this forces the chart to be zero.
6. At a chart prime, the residue-field map from the contracted prime makes its residue
   field an extension of the original residue field
   (lem-weil-pbc-spec-residue-field-identification and
   lem-weil-pbc-prime-residue-field-algebra). Tensor associativity identifies the chart
   fibre with the original algebra tensored with that field; it is a domain by hypothesis.
7. The prime quotient of `B*` is flat over the prime quotient of the chart
   (lem-weil-pbc-flat-module-quotient-flat), hence torsion-free
   (lem-trf-flat-module-torsionfree-domain). Localization therefore embeds it in the fibre
   (lem-trf-fibre-module-localization). Thus the extended prime ideal is prime.
8. Modulo a chart prime some divided coordinate is nonzero, by step 5. Its `gν` has
   nonzero fibre image and lies outside the extended prime by step 7. It is a unit
   in the localization at that prime. Since `cgν = jν`, the two localized ideals agree.
-/
theorem principal
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (hflat : (algebraMap R B).Flat)
    (hgeom : ∀ (p : Ideal R) [p.IsPrime] (E : Type (max u v w)) [Field E]
      [Algebra R E] [Algebra p.ResidueField E] [IsScalarTower R p.ResidueField E],
      IsDomain (E ⊗[R] B))
    (A : Type z) (i : B →ₗ[R] (A →₀ R)) (ρ : (A →₀ R) →ₗ[R] B)
    (hsplit : ρ.comp i = LinearMap.id)
    (t : ℕ) (j : Fin t → B) (J : Ideal B) (hJ : J = Ideal.span (Set.range j))
    (C : Ideal R) (hC : C = Ideal.span {r : R | ∃ (ν : Fin t) (α : A), r = i (j ν) α})
    (h a c : R) (ha : a ∈ Ideal.span {h} * C) (hc : c ∈ C) (hac : a = h * c) :
    (algebraMap (chartRing (Ideal.span {h} * C) a) (baseChange R B C h a)).Flat ∧
    (∀ s ∈ ({a, h, c} : Set R),
      Function.Injective (fun x : chartRing (Ideal.span {h} * C) a ↦
        algebraMap R _ s * x) ∧
      Function.Injective (fun x : baseChange R B C h a ↦ algebraMap R _ s * x)) ∧
    C.map (algebraMap R (chartRing (Ideal.span {h} * C) a)) =
      Ideal.span {algebraMap R (chartRing (Ideal.span {h} * C) a) c} ∧
    (∃ e : Localization.Away
          (algebraMap R (chartRing (Ideal.span {h} * C) a) a) ≃+* Localization.Away a,
      (∀ x : chartRing (Ideal.span {h} * C) a,
        e (algebraMap _ _ x) = (x : Localization.Away a)) ∧
      algebraMap R (Localization.Away a) h * chartFraction a 1 c = 1) ∧
    (∀ p : PrimeSpectrum (chartRing (Ideal.span {h} * C) a),
      IsDomain (p.asIdeal.Fiber (baseChange R B C h a)) ∧
      (∃ f : (baseChange R B C h a ⧸
            p.asIdeal.map (algebraMap _ (baseChange R B C h a))) →+*
          p.asIdeal.Fiber (baseChange R B C h a),
        (∀ b : baseChange R B C h a,
          f (Ideal.Quotient.mk _ b) = TensorProduct.tmul _ 1 b) ∧ Function.Injective f) ∧
      ∃ q : PrimeSpectrum (baseChange R B C h a),
        q.asIdeal = p.asIdeal.map (algebraMap _ (baseChange R B C h a)) ∧
        J.map ((algebraMap (baseChange R B C h a) (Localization.AtPrime q.asIdeal)).comp
            (Algebra.TensorProduct.includeRight : B →ₐ[R] baseChange R B C h a).toRingHom) =
          Ideal.span {(algebraMap (baseChange R B C h a) (Localization.AtPrime q.asIdeal))
            (algebraMap R (baseChange R B C h a) c)}) := by
  sorry

end AlgebraicGeometry.AffineBlowup.SplitCoefficientChart
