import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.RingTheory.Smooth.Basic
import Sheaf.RingTheory.GRing

/-!
# Popescu's theorem reduces to a field as base

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F5 (blueprint:
lem-weil-pbc-popescu-reduce-to-field).
-/

universe u v

open CategoryTheory

/-- Assume that for every field `k` and every Noetherian ring `Λ` with a regular ring map
`k → Λ`, `Λ` is a filtered colimit of smooth `k`-algebras. Then for all Noetherian rings
`R`, `Λ` and every regular ring map `R → Λ`, `Λ` is a filtered colimit of smooth
`R`-algebras.

Fields and source rings live in universe `u`, target rings, algebras and index categories in
`max u v`, as in the Popescu siblings (lem-weil-pbc-popescu-lift-nilpotent,
lem-weil-pbc-popescu-product): the proof applies the hypothesis to the residue fields
`K_i` of `R` (universe `u`) and the fibre rings `Λ ⊗_R K_i` (universe `max u v`).

Proof (Stacks Project, Smoothing Ring Maps, Lemma Tag 07F5, lines 2003--2064):
1. For an ideal `I ⊆ R`, `R/I → Λ/IΛ` is again a regular map of Noetherian rings
   (lem-weil-pbc-regular-base-change).
2. Noetherian induction: if PT fails, choose `I` maximal with PT failing for `R/I → Λ/IΛ`
   and replace `R` by `R/I`; then `R ≠ 0` and PT holds modulo every nonzero ideal.
3. `R` is reduced: the nilradical is nilpotent, and lem-weil-pbc-popescu-lift-nilpotent
   lifts PT from `R/N`.
4. By the factorization criterion (Algebra 07C3) it suffices to factor every `R`-algebra map
   `α : A → Λ` with `A` finitely presented through a smooth `R`-algebra.
5. With `S` the nonzerodivisors, `S⁻¹R ≅ ∏ K_i` is a finite product of fields (02LX, 00FR);
   each `K_i → Λ ⊗_R K_i` is regular, so PT holds for it by hypothesis and for
   `S⁻¹R → S⁻¹Λ` by lem-weil-pbc-popescu-product.
6. Hence `S⁻¹α` factors through a smooth `S⁻¹R`-algebra `B'`.
7. Delocalize (lem-weil-pbc-popescu-delocalize-base): after replacing `A`, some `π ∈ S` is
   elementary standard, hence strictly standard, in `A` over `R`.
8. `π` is a nonzerodivisor on `R` and, by flatness, on `Λ`, so the annihilator conditions hold.
9. PT for `R/π⁸R → Λ/π⁸Λ` gives a smooth factorization modulo `π⁸`; lem-weil-pbc-popescu-lifting
   (with `π⁴`) gives `D` finitely presented and smooth at every prime, with a compatible map
   `A/π⁴A → D/π⁴D`.
10. lem-weil-pbc-popescu-desingularize-strictly-standard gives `A → B → Λ` with `H_{B/R} = B`,
    and lem-weil-pbc-popescu-final-solve factors `B → Λ` through a smooth `R`-algebra,
    contradicting step 2.

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07F5, lines 2003--2064
(blueprint: lem-weil-pbc-popescu-reduce-to-field). -/
theorem popescu_reduce_to_field
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ)) :
    ∀ (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
      [IsNoetherianRing R] [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap R Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} R ↦ Algebra.Smooth R B)
          (CommAlgCat.of R Λ) := by
  sorry
