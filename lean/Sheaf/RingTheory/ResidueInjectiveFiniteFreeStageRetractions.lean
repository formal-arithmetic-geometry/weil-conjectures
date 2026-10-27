module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong

/-!
# Retractions of residue-injective finite free maps at later colimit stages

Source: Stacks Project, `flat.tex`, Tag 05FQ, proof of
`lemma-universally-injective-local`, finite-free-stage factorization and splitting;
`algebra.tex`, Tag 00O0, finite-free residue criterion
(blueprint: lem-trf-residue-injective-finite-free-stage-retractions).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- A residue-injective map from a finite free module into a directed colimit of finite
free modules lifts to one stage, and its composites into every later stage have retractions.
The retractions need not be compatible.

Source: Stacks Project, `flat.tex`, Tag 05FQ, proof of
`lemma-universally-injective-local`; `algebra.tex`, Tag 00O0
(blueprint: lem-trf-residue-injective-finite-free-stage-retractions).

Proof:
1. Choose a finite basis of `P` (def-weil-pbc-free-module). By the elementwise colimit
   description (lem-weil-pbc-filtered-colimit-modules-elementwise), each basis image has a
   representative at a stage. Nonemptiness and directedness give a common upper bound `i`,
   including when the basis is empty. Transport the representatives there and extend them
   linearly to `vᵢ`. The cocone identities give `qᵢ ∘ vᵢ = v` on each basis vector, hence on `P`.
2. For any `j ≥ i`, write `wⱼ = tᵢⱼ ∘ vᵢ`. The cocone identity gives `qⱼ ∘ wⱼ = v`.
   Reduction modulo the maximal ideal respects composition, so injectivity of the reduction
   of `v` implies injectivity of the reduction of `wⱼ`; no injectivity of `qⱼ` is needed.
3. The local unit criterion (lem-weil-pbc-local-ring-unit-criterion) identifies the prime
   residue field at the maximal ideal with `R/𝔪`: send `a/s` to `ā/s̄` and `ā` to `a/1`.
   Finite bases identify both the quotient of a free module modulo `𝔪` and its residue-field
   tensor product with the coordinate space over `R/𝔪`. The induced maps have the same
   reduced matrix, so the residue-field base change of `wⱼ` is injective.
4. Apply lem-pc-finite-free-map-residue-localization-strong to this matrix at `𝔪`. It supplies
   `f ∉ 𝔪` and a left inverse after inverting `f`. The local unit criterion makes `f` a unit.
   Evaluation `x/fⁿ ↦ f⁻ⁿ • x` identifies each localized module with the original module and
   intertwines the localized map with `wⱼ`. Transport the left inverse through these
   identifications to obtain `sⱼ` with `sⱼ ∘ wⱼ = id`. Since `j ≥ i` was arbitrary and `i, vᵢ`
   were fixed in step 1, this proves all the clauses without asserting compatibility.
-/
theorem exists_finite_free_stage_retractions_of_residue_injective
    {R : Type u} [CommRing R] [IsLocalRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{v} R)
    [∀ i : I, Module.Finite R (F.obj i)] [∀ i : I, Module.Free R (F.obj i)]
    (c : Cocone F) (hc : IsColimit c)
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P]
    (v : P →ₗ[R] c.pt)
    (hv : Function.Injective (v.reduceModIdeal (maximalIdeal R))) :
    ∃ (i : I) (vᵢ : P →ₗ[R] F.obj i), (c.ι.app i).hom.comp vᵢ = v ∧
      ∀ (j : I) (hij : i ≤ j), ∃ sⱼ : F.obj j →ₗ[R] P,
        sⱼ.comp ((F.map (homOfLE hij)).hom.comp vᵢ) = LinearMap.id := by
  sorry

end IsLocalRing
