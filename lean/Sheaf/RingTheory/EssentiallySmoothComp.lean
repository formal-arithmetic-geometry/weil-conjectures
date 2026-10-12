/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.EssentiallySmooth
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent

/-!
# Composition of essentially smooth ring maps

Source: Stacks Project, Smoothing Ring Maps, Lemmas 07FI and 07FJ (step 13), where
composition is used without a separate statement; the node's agent-written proof uses
Algebra, Lemmas 00CR and 0CAQ (blueprint: lem-weil-pbc-essentially-smooth-composition).
-/

@[expose] public section

universe u v w

namespace RingHom

/-- The composite of two essentially smooth homomorphisms of commutative rings is
essentially smooth. Source: Stacks Project, Smoothing Ring Maps, Lemmas 07FI and 07FJ
(step 13); agent-written argument from Algebra, Lemmas 00CR and 0CAQ
(blueprint: lem-weil-pbc-essentially-smooth-composition).

Proof (the node's five steps):
1. By `def-weil-pbc-essentially-smooth-ring-map`, present `A` as `S⁻¹P` for a smooth
   `R`-algebra `P`, and `B` as `T⁻¹Q` for a smooth `A`-algebra `Q`
   (`def-weil-pbc-smooth-ring-map`). Transport the algebra structures and multiplicative
   subsets along the presentation isomorphisms. An `A`-algebra isomorphism is also an
   `R`-algebra isomorphism for the composite structure.
2. Express `A` as the filtered colimit of `P` localized at each element of `S`, using
   `lem-weil-pbc-localization-colimit-principal-localizations` (Stacks 00CR). Descend `Q`
   to a smooth algebra `Q₀` over some principal localization `Pₛ`, with
   `Q ≅ A ⊗[Pₛ] Q₀`, by `lem-weil-pbc-smooth-algebra-filtered-colimit-descent` (0CAQ).
3. The map `R → Pₛ` is smooth by `lem-weil-pbc-smooth-ring-map-principal-localization`.
   Therefore `Q₀` is smooth over `R` by the composition clause of
   `lem-weil-pbc-smooth-ring-map-base-change-composition`.
4. Since the powers of `s` lie in `S`, the map `Pₛ → A` is localization at the image
   of `S`, by clause (2) of `lem-weil-pbc-localization-of-localization`. Base change
   by `Pₛ → Q₀` makes `Q₀ → Q₀ ⊗[Pₛ] A` a localization at the image of this subset,
   by `lem-weil-pbc-localization-base-change`. The tensor-product symmetry identifies
   this target with `Q`. The localization map `Q₀ → Q` respects the `R`-structures:
   the balancing relation identifies `1 ⊗ β(φ(p))` with `κₛ(φ(p)) ⊗ 1`, where
   `φ : P → Pₛ`, `β : Pₛ → Q₀`, and `κₛ : Pₛ → A` are the structure maps.
5. Compose the localization `Q₀ → Q` with `Q → T⁻¹Q = B` using clause (1) of
   `lem-weil-pbc-localization-of-localization`. More explicitly, if `S₁` is the
   multiplicative subset of `Q₀` from step 4 and `λ : Q₀ → Q` its localization map,
   localize `Q₀` at `{x | λ(x) = t * λ(σ) for some t ∈ T and σ ∈ S₁}`.
   This gives an `R`-algebra presentation of `B` as a localization of the smooth
   `R`-algebra `Q₀`, so `def-weil-pbc-essentially-smooth-ring-map` gives the conclusion. -/
theorem essentiallySmooth_comp {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] (f : R →+* A) (g : A →+* B)
    (hf : letI : Algebra R A := f.toAlgebra; Algebra.EssentiallySmooth R A)
    (hg : letI : Algebra A B := g.toAlgebra; Algebra.EssentiallySmooth A B) :
    letI : Algebra R B := (g.comp f).toAlgebra
    Algebra.EssentiallySmooth R B := by
  sorry

end RingHom
