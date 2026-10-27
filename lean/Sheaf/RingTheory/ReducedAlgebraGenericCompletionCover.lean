module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.LocalCompletionProductFaithfullyFlat
import Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Generic localization and completion for reduced-algebra projectivity

Source: Stacks Project, flat.tex, Tag 05FS, second proof paragraph of
`lemma-fibres-irreducible-flat-projective`
(blueprint: lem-trf-reduced-algebra-generic-completion-cover).

The completed algebra is written with the completion as the first tensor factor,
so its scalar structure is Mathlib's standard left-factor algebra structure.
Tensor symmetry identifies it canonically with the source's `S ⊗[R] A`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace Algebra.ReducedGenericCompletion

/-- The principal adic completion occurring in the reduced induction, Stacks Tag 05FS.
This is an abbreviation for Mathlib's compatible-sequence completion, including its
canonical algebra structure (blueprint: lem-trf-reduced-algebra-generic-completion-cover). -/
abbrev Completion {R : Type u} [CommRing R] (f : R) :=
  AdicCompletion (Ideal.span ({f} : Set R)) R

/-- The extended principal ideal in the completion, Stacks Tag 05FS.
(blueprint: lem-trf-reduced-algebra-generic-completion-cover). -/
abbrev completionIdeal {R : Type u} [CommRing R] (f : R) : Ideal (Completion f) :=
  (Ideal.span ({f} : Set R)).map (algebraMap R (Completion f))

/-- The completed base change in Stacks Tag 05FS, with the tensor factors interchanged
by the canonical symmetry so the completion acts on the left.
(blueprint: lem-trf-reduced-algebra-generic-completion-cover). -/
abbrev CompletedAlgebra {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (f : R) := Completion f ⊗[R] S

/-- The ideal `fN` in the completed base change, Stacks Tag 05FS.
(blueprint: lem-trf-reduced-algebra-generic-completion-cover). -/
abbrev completedIdeal {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (f : R) : Ideal (CompletedAlgebra S f) :=
  (completionIdeal f).map (algebraMap (Completion f) (CompletedAlgebra S f))

end Algebra.ReducedGenericCompletion

namespace Algebra

open ReducedGenericCompletion

/-- A single nonzero element gives a free localization and the canonical faithfully flat
localization-completion cover, with finite type flat completed base change, geometrically
integral fibres, and projective reduction. The residue fields are exactly those of
`def-weil-residue-field`; compatibility of `ι` specifies the induced scalar structure.
The displayed formulas characterize both quotient isomorphisms canonically and express
compatibility with the identification of the quotient scalar rings.

Source: Stacks Project, flat.tex, Tag 05FS, second proof paragraph of
`lemma-fibres-irreducible-flat-projective`
(blueprint: lem-trf-reduced-algebra-generic-completion-cover).

Proof:
1. Choose a minimal prime `p` over zero by
   lem-weil-pbc-minimal-prime-over-proper-ideal. By
   lem-weil-pbc-noetherian-minimal-prime-associated choose `z` with annihilator `p`.
   It is nonzero since `p` is proper. Reducedness gives `z ∉ p`: otherwise `z² = 0`.
   The ring `R_z` is nonzero, and a zero product of fractions implies that one numerator
   is in `p`, hence killed by `z`; it is therefore a domain. It is Noetherian by
   lem-weil-pbc-localization-noetherian.
2. Localize a finite algebra-generating set of `S` at `z`. Apply
   lem-pur-noetherian-algebra-module-generic-freeness to this finite type algebra as
   its own cyclic module over `R_z`. Write the resulting nonzero element as `a/z^m`.
   Its numerator is outside `p`. Set `f = az`, which is nonzero. The mutually inverse
   fraction maps identify the iterated localizations with `R_f` and `S_f`, carrying
   the free basis to the asserted one. No finiteness of the basis is imposed.
3. For this same `f` let `A` be its principal adic completion. Apply
   lem-trf-local-completion-product-faithfully-flat. By
   lem-weil-pbc-adic-completion-noetherian the ring `A` is Noetherian. The principal
   ideal is finitely generated, so lem-weil-pbc-adic-completion-mod-ideal gives
   completeness and the projection-induced isomorphism `A/fA ≃ R/(f)`.
4. The tensors of a finite algebra-generating set generate the completed base change
   over `A`. Apply lem-weil-pbc-flat-module-base-change to get flatness; tensor
   symmetry identifies the result with `N = S ⊗[R] A`.
5. A prime `q` of `A` contracts to `p` in `R`. The fraction map embeds `κ(p)` in
   `κ(q)`. A field extension `L/κ(q)` is consequently an extension of `κ(p)`.
   Tensor associativity identifies `N ⊗[A] L` with `S ⊗[R] L`: the maps on pure
   tensors are `(s ⊗ a) ⊗ l ↦ s ⊗ al` and `s ⊗ l ↦ (s ⊗ 1) ⊗ l`.
   They are inverse by the tensor relations, so the original fibre hypothesis applies.
6. Define `N → S/fS` by `s ⊗ a ↦ s̅ a̅`, using the completion projection.
   Balancing holds since its composite with `R → A` is reduction modulo `f`.
   It kills `fN`. The inverse on quotients sends `s̅` to `[s ⊗ 1]`. To check the
   other composite, represent the image of `a` modulo `f` by `r ∈ R`; then
   `a - r ∈ fA`, giving `[s ⊗ a] = [rs ⊗ 1]`. These are algebra maps over the
   displayed identification of quotient scalar rings, with the asserted formula.
7. The ideal `(f)` is nonzero. The projective-reduction hypothesis and step 6 transport
   a free-module splitting from `S/fS` over `R/(f)` to `N/fN` over `A/fA`, using
   def-weil-pbc-projective-module. If `f` is a unit both quotients and the completion
   are zero; the same argument includes this case.
-/
theorem reduced_algebra_generic_completion_cover
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsReduced R] [IsNoetherianRing R]
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hflat : RingHom.Flat (algebraMap R S))
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (S ⊗[R] K))
    (hprojective : ∀ J : Ideal R, J ≠ ⊥ →
      Module.Projective (R ⧸ J) (S ⧸ J.map (algebraMap R S))) :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[R] S) ∧
      RingHom.FaithfullyFlat
        ((algebraMap R (Localization.Away f)).prod (algebraMap R (Completion f))) ∧
      IsNoetherianRing (Completion f) ∧
      IsAdicComplete (completionIdeal f) (Completion f) ∧
      RingHom.FiniteType (algebraMap (Completion f) (CompletedAlgebra S f)) ∧
      RingHom.Flat (algebraMap (Completion f) (CompletedAlgebra S f)) ∧
      (∀ (q : Spec (.of (Completion f))) (L : Type (max u v w)) [Field L]
        [Algebra (Completion f) L]
        (ι : (Spec (.of (Completion f))).residueField q →+* L),
        algebraMap (Completion f) L =
          ι.comp (((Scheme.ΓSpecIso (.of (Completion f))).inv ≫
            (Spec (.of (Completion f))).Γevaluation q).hom) →
        IsDomain (CompletedAlgebra S f ⊗[Completion f] L)) ∧
      ∃ e : (Completion f ⧸ completionIdeal f) ≃ₐ[R] R ⧸ Ideal.span ({f} : Set R),
        (∀ a : Completion f,
          e (Ideal.Quotient.mk (completionIdeal f) a) =
            AdicCompletion.evalOneₐ (Ideal.span ({f} : Set R)) a) ∧
        ∃ θ : (CompletedAlgebra S f ⧸ completedIdeal S f) ≃ₐ[R]
            S ⧸ (Ideal.span ({f} : Set R)).map (algebraMap R S),
          (∀ (a : Completion f) (s : S),
            θ (Ideal.Quotient.mk (completedIdeal S f) (a ⊗ₜ[R] s)) =
              algebraMap (R ⧸ Ideal.span ({f} : Set R))
                (S ⧸ (Ideal.span ({f} : Set R)).map (algebraMap R S))
                (e (Ideal.Quotient.mk (completionIdeal f) a)) *
                Ideal.Quotient.mk ((Ideal.span ({f} : Set R)).map (algebraMap R S)) s) ∧
          Module.Projective (Completion f ⧸ completionIdeal f)
            (CompletedAlgebra S f ⧸ completedIdeal S f) := by
  sorry

end Algebra
