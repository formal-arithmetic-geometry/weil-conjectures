import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Split an affine étale morphism near a marked geometric fibre

Source: literature/stacks-project/etale.tex, Tags 04HM and 04HU
(blueprint: lem-trf-affine-etale-split-neighbourhood).

## Main statements

* `exists_affine_etale_split_neighbourhood` states the affine étale splitting near a
  geometric point, including the singleton fibre, the empty remainder over the marked
  point, and the resulting enumeration of geometric lifts. -/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false
set_option warn.sorry false

/--
The affine étale splitting of an affine étale morphism near a marked geometric fibre.

Source: literature/stacks-project/etale.tex, Tag 04HM, lemma-etale-etale-local-technical,
applied to all points of the finite fibre; the affine and single-`s`-fibre-point refinement is
the third paragraph of the proof of etale-cohomology.tex Tag 04HU,
lemma-points-small-etale-site; fibre structure from morphisms.tex Tag 02GL,
lemma-etale-over-field (2).
(blueprint: lem-trf-affine-etale-split-neighbourhood)

Proof (the node's steps):
1. `U` is affine, so `f` is separated (lem-weil-pbc-affine-source-morphism-separated); an
   étale morphism is unramified (def-weil-etale-morphism).
2. The fibre `U_s` is affine (lem-weil-pbc-fibre-product-affine-spectra), hence quasi-compact
   (lem-weil-pbc-affine-scheme-qcqs), and discrete
   (lem-weil-pbc-etale-fibre-discrete-separable-points); so `f⁻¹(s)` is finite. List it
   without repetitions as `x₁, …, x_r`, allowing `r = 0` (def-pc-scheme-fibre).
3. Apply lem-weil-pbc-unramified-etale-local-decomposition (Tag 04HI) to `f` and all `xᵢ`:
   an étale `T₀ → S`, a point `t` over `s`, and `U ×_S T₀ = W₀ ⊔ ∐ₐ Pₐ` with each
   `hₐ : Pₐ → T₀` a closed immersion whose image contains `t`, and `(W₀)_t = ∅`.
4. The projection `U ×_S T₀ → T₀` is étale (lem-weil-pbc-etale-scheme-base-change); the
   pieces are open in it, so every `hₐ` and `W₀ → T₀` is étale
   (lem-weil-pbc-etale-composition-cancellation).
5. A closed immersion is a monomorphism (def-weil-closed-immersion).
6. Each `hₐ` is flat, locally of finite presentation and a monomorphism, hence an open
   immersion (lem-pe-flat-lfp-monomorphism-open, Tag 025G) onto an open `Oₐ ∋ t`.
7. Choose an affine open `t ∈ T ⊆ ⋂ₐ Oₐ` (lem-weil-pbc-affine-opens-basis) and restrict
   (lem-weil-pbc-open-fibre-product): `U ×_S T ≅ W_T ⊔ ∐_{a=1}^n T` with `(W_T)_t = ∅`;
   `T → S` is étale.
8. The fibre of `T → S` over `s` is finite and discrete: `t, y₁, …, y_m`.
9. By discreteness `t ∉ closure {y_j}`; choose an affine open `V ∋ t` inside
   `T \ ⋃ⱼ closure {y_j}`. The fibre of `V → S` over `s` is the single point `v = t`, and
   `V → S` is étale.
10. Restrict the decomposition to `V`: `U ×_S V ≅ (∐_{a=1}^n V) ⊔ W` with `W → V` étale;
   a point of `W` over `s` would lie over `v`, which is excluded, so `W` has no point over `s`.
11. Lift `s̄` to `v̄ : Spec Ω → V` with image `v`
   (lem-weil-pbc-etale-cover-geometric-point-lift, Tag 03PR, for the jointly surjective
   family `{V → S, id_S}`); `(V, v̄)` is an affine pointed étale neighbourhood
   (def-weil-pbc-pointed-etale-neighbourhoods).
12. By the universal property of the fibre product, `S`-morphisms `Spec Ω → U` correspond to
   `V`-morphisms `Spec Ω → U ×_S V` over `v̄`; `Spec Ω` has one point, so each factors
   through exactly one piece, never through `W`, and exactly once through each copy of `V`.
   Projecting to `U` gives the bijection `Fin n ≃ Hom_S(Spec Ω, U)`, also for `n = 0`.
-/
theorem exists_affine_etale_split_neighbourhood
    {S U : Scheme.{u}} [IsAffine S] [IsAffine U] (f : U ⟶ S) [Etale f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (bar_s : Spec (.of Ω) ⟶ S) (s : S)
    (hs : bar_s (IsLocalRing.closedPoint Ω) = s) :
    ∃ (V : Scheme.{u}) (g : V ⟶ S) (_ : IsAffine V) (_ : Etale g),
      ∃ (bar_v : Spec (.of Ω) ⟶ V),
        bar_v ≫ g = bar_s ∧
        ∃ (n : ℕ) (W : Scheme.{u}) (w : W ⟶ V) (_ : Etale w),
          ∃ (e : pullback f g ≅ (∐ fun _ : Fin n => V) ⨿ W),
            e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w =
                pullback.snd f g ∧
            (∀ x : V, g x = s ↔ x = bar_v (IsLocalRing.closedPoint Ω)) ∧
            (∀ x : W, (w ≫ g) x ≠ s) ∧
            ∃ (a : Fin n → (Spec (.of Ω) ⟶ U)),
              (∀ i : Fin n,
                  a i = bar_v ≫ Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv ≫
                    pullback.fst f g) ∧
              ∃ (ha : ∀ i : Fin n, a i ≫ f = bar_s),
                ∃ (E : Fin n ≃
                    {q : Spec (.of Ω) ⟶ U // q ≫ f = bar_s}),
                  ∀ i : Fin n, E i = ⟨a i, ha i⟩ := by
  sorry

end AlgebraicGeometry
