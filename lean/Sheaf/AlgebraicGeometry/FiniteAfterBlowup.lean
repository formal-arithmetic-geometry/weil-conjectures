module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
import Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisor
import Sheaf.AlgebraicGeometry.StrictTransformComposition
import Sheaf.TraceFormula.ProperFlatFiniteDenseOpen
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finite locally free strict transform after an admissible blow-up

Source: Stacks Project, `flat.tex`, Lemma 29.27.1, Tag 0B49
(blueprint: lem-trf-finite-after-blowup).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Finite locally free strict transform after an admissible blow-up** (Stacks Project,
`flat.tex`, Lemma 29.27.1, Tag 0B49, `lemma-finite-after-blowing-up`). Let `S` be qcqs,
`f : X ⟶ S` proper and `U ⊆ S` a quasi-compact open such that `X ×_S U ⟶ U` is finite
locally free. Then there is a `U`-admissible blow-up `S' ⟶ S` whose strict transform
`X' ⟶ S'` is finite locally free.

Proof (blueprint, following Tag 0B49 with the density blow-up taken first):
1. By `sk-lem-nagata-boundary-divisor` there is a `U`-admissible blow-up `b₀ : S₀ ⟶ S`
   with `U₀ = b₀⁻¹(U)` scheme-theoretically dense. `b₀` is proper
   (`lemma-nagata-blowup-proper`), hence quasi-compact and quasi-separated, so `S₀` is
   qcqs (`lem-weil-pbc-qcqs-morphism-permanence`); `U₀ ⟶ U` is an isomorphism
   (`lemma-nagata-admissible-blowup-over-open`), so `U₀` is quasi-compact.
2. For these blow-ups the strict transform is a closed subscheme of the base change, and
   its restriction over the preserved open is the original restriction: the base over the
   open is the original base, the scheme image restricts to the open
   (`lemma-nagata-scheme-image-restrict-open`, Morphisms Tag 01R8; the defining open
   immersion is quasi-compact since the center is of finite type), and over the open the
   immersion is the identity.
3. The strict transform `f₀ : X₀ ⟶ S₀` is proper (closed immersion into the base change of
   `f`, `lem-weil-pbc-proper-fp-permanence`), hence of finite type and quasi-separated;
   by step 2 it is finite locally free over `U₀`. The flattening lemma
   `lem-trf-flattening-by-admissible-blowup` (Tag 081R) gives a `U₀`-admissible blow-up
   `b₁ : S₁ ⟶ S₀` whose strict transform `f₁ : X₁ ⟶ S₁` is flat and of finite
   presentation.
4. `f₁` is proper; `U₁ = b₁⁻¹(U₀)` is scheme-theoretically dense, hence topologically
   dense (`lemma-nagata-admissible-blowup-preserves-density`); by step 2 `f₁` is finite
   over `U₁`. By `lem-trf-proper-flat-finite-dense-open` (Tag 0B48), `f₁` is finite.
5. `f₁` is finite, flat and locally of finite presentation, i.e. finite locally free
   (`def-pc-finite-locally-free`).
6. By `thm-nagata-composition-of-blowups` (Divisors Tag 080B), `b₀ ∘ b₁` is the blow-up of
   a finite-type ideal `K` on `S` with `V(K) = V(I) ∪ b₀(V(J))`, which is disjoint from `U`;
   so `b₀ ∘ b₁` is `U`-admissible. By `lem-trf-strict-transform-composition` (Divisors
   Tag 080I) `X₁` is the strict transform of `X` along it, which is therefore finite
   locally free by step 5.

(blueprint: lem-trf-finite-after-blowup) -/
theorem finiteLocallyFree_after_admissibleBlowup
    {S X : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace U.toScheme]
    [IsProper f]
    [Scheme.Hom.IsFiniteLocallyFree (Limits.pullback.snd f U.ι)] :
    ∃ B : IsAdmissible S U,
      Scheme.Hom.IsFiniteLocallyFree
        (strictTransformMap f B.I.blowupMap B.I.support.compl) := by
  sorry

end AlgebraicGeometry
