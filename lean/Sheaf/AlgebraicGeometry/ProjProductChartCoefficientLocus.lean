module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Unit locus of the product-chart homogeneous coefficient

Source: Stacks Project, Tag 01MV (lemma-principal-open), final sentences of the proof,
and Tag 01MA (lemma-standard-open-proj).
(blueprint: lem-trf-proj-product-chart-coefficient-locus)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

/-- On `D₊(ab)`, the coefficient `b^n f / a^n` is degree zero and its unit locus is
`D₊(ab) ∩ D₊(f)`. The witnesses `c`, `u`, `w` are specified by their images under the
injective map `HomogeneousLocalization.val` to the ordinary localization. `Ring.inverse`
is used only on elements asserted here to be units; thus the three displayed formulas
are precisely `c = b^n f / a^n`, `u = b^(2nα) / a^(2nβ)`, and its inverse `w`.
The element `Away.isLocalizationElem` is `f^(α+β) / (ab)^(nd)`.

Source: Stacks Project, Tag 01MV (lemma-principal-open), last two sentences of the proof;
Tag 01MA (lemma-standard-open-proj).
(blueprint: lem-trf-proj-product-chart-coefficient-locus)

Proof plan:
1. In `A[1/(ab)]`, the inverses of `a` and `b` are `b/(ab)` and `a/(ab)`.
   Hence `c = b^(2n) f / (ab)^n`, whose numerator has degree
   `2nβ + nd = n(α+β)`. The degree-zero localization definition
   (def-nagata-homogeneous-localization-degree-zero) therefore supplies `c`.
   Likewise `u = b^(2n(α+β)) / (ab)^(2nβ)` and
   `w = a^(2n(α+β)) / (ab)^(2nα)` have matching numerator and denominator degrees.
   Their product is one, including when `β = 0`.
2. The fraction `q = f^(α+β) / (ab)^(nd)` has matching degrees. The equations
   `2nα - nd = n(α+β)` and `2nβ + nd = n(α+β)` give `c^(α+β) = u*q`.
   This uses only the inverses already constructed, so cancellation of nonunits
   is unnecessary. Injectivity of `val` gives the equality in degree zero.
3. Apply the germ map to this identity and to `u*w = 1`. If the inverse of the
   germ of `c` is `t`, then the inverse of the germ of `q` is `u*t^(α+β)`.
   Conversely, if the inverse of the germ of `q` is `z`, then
   `c^(α+β-1)*w*z` is an inverse of the germ of `c`, since `α+β > 0`.
4. Apply lem-weil-pbc-proj-basic-open-intersection to `ab` and `f`, of positive
   degrees `α+β` and `nd`. It identifies the unit locus of `q` with the
   intersection of the standard opens, giving both pointwise equivalences and
   the equality of opens (def-pc-proj).
5. The formulas remain valid in the zero localization when the chart is empty.
   If `f` is zero or nilpotent, every homogeneous prime contains it, so its
   standard open is empty; the same pointwise equivalences give the empty
   coefficient unit locus. No nonzero or reduced hypothesis is used.
-/
theorem productChartCoefficientLocus
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (d n α β : ℕ) (hd : 0 < d) (hn : 0 < n) (hα : α = β + d)
    (a b f : A) (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β) (hf : f ∈ 𝒜 (n * d)) :
    0 < α + β ∧
    IsUnit (algebraMap A (Localization.Away (a * b)) a) ∧
    IsUnit (algebraMap A (Localization.Away (a * b)) b) ∧
    ∃ c u w : HomogeneousLocalization.Away 𝒜 (a * b),
      c.val = algebraMap A (Localization.Away (a * b)) b ^ n *
        algebraMap A (Localization.Away (a * b)) f *
        Ring.inverse (algebraMap A (Localization.Away (a * b)) a) ^ n ∧
      u.val = algebraMap A (Localization.Away (a * b)) b ^ (2 * n * α) *
        Ring.inverse (algebraMap A (Localization.Away (a * b)) a) ^ (2 * n * β) ∧
      w.val = algebraMap A (Localization.Away (a * b)) a ^ (2 * n * β) *
        Ring.inverse (algebraMap A (Localization.Away (a * b)) b) ^ (2 * n * α) ∧
      IsUnit u ∧ u * w = 1 ∧
      c ^ (α + β) = u *
        HomogeneousLocalization.Away.isLocalizationElem (SetLike.mul_mem_graded ha hb) hf ∧
      (∀ x : basicOpen 𝒜 (a * b),
        (IsUnit ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 (a * b)) x x.2
            (awayToSection 𝒜 (a * b) c)) ↔
          IsUnit ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 (a * b)) x x.2
            (awayToSection 𝒜 (a * b)
              (HomogeneousLocalization.Away.isLocalizationElem
                (SetLike.mul_mem_graded ha hb) hf)))) ∧
        (IsUnit ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 (a * b)) x x.2
            (awayToSection 𝒜 (a * b) c)) ↔ (x : Proj 𝒜) ∈ basicOpen 𝒜 f)) ∧
      (Proj 𝒜).basicOpen (awayToSection 𝒜 (a * b) c) =
        basicOpen 𝒜 (a * b) ⊓ basicOpen 𝒜 f := by
  sorry

end AlgebraicGeometry.Proj
