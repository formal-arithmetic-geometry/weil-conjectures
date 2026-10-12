module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.Algebra.FlatTorIdealCriterion
import Sheaf.Paper.TorLongExactFirstVariable

/-! # Injectivity modulo the maximal ideal into a flat module (Noetherian local)

Source: literature/stacks-project/algebra.tex, Lemma Tag 00ME
(blueprint: lem-weil-pbc-flat-mod-injective)
-/

@[expose] public section

/--
The local injectivity criterion for a map from a finite module into a flat module.
Source: Algebra, Lemma Tag 00ME (blueprint: lem-weil-pbc-flat-mod-injective).
The proof follows the blueprint steps: induction on powers of the maximal ideal using
flat tensor exactness; Krull intersection gives injectivity; and the Tor criterion,
applied after quotienting by each ideal, gives flatness of the cokernel.
The hypothesis `hu` is injectivity of the induced map `N/𝔪N → M/𝔪M`, with `N`
an `R`-module through `φ`.
-/
theorem flat_mod_injective
    {R S N M : Type*}
    [CommRing R] [CommRing S] [AddCommGroup N] [AddCommGroup M]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S)
    (hφ : ∀ x : R, x ∈ IsLocalRing.maximalIdeal R →
      φ x ∈ IsLocalRing.maximalIdeal S)
    [Module S N] [Module R M]
    [Module.Finite S N] [Module.Flat R M]
    (u : (letI : Module R N := Module.compHom N φ; N →ₗ[R] M))
    (hu : (letI : Module R N := Module.compHom N φ;
      Function.Injective
        ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mapQ
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) u
          (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) u))))
    : (letI : Module R N := Module.compHom N φ;
      Function.Injective u ∧ Module.Flat R (M ⧸ (LinearMap.range u))) := by
  sorry
