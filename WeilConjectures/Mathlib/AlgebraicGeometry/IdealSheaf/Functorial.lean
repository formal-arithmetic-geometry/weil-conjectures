/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Kernels, dominant morphisms and factorizations through closed subschemes

We record the interaction of kernel ideal sheaves with scheme-theoretically dominant
morphisms and the resulting factorization criterion used by the valuative arguments of
the Nagata compactification proof:

- `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`:
  precomposition with a scheme-theoretically dominant morphism preserves kernels;
- the inclusion of the generic point `Spec K ⟶ Spec A` of the spectrum of a domain
  with fraction field `K` is scheme-theoretically dominant;
- `AlgebraicGeometry.IsClosedImmersion.exists_lift_of_isFractionRing`: a morphism
  `Spec A ⟶ Y` from the spectrum of a domain factors through a closed subscheme
  `Z ⟶ Y` as soon as its restriction to the generic point does (blueprint:
  `lemma:nagata-valuation-factor-closed`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X' X : Scheme.{u}}

/-- Precomposition with a scheme-theoretically dominant morphism does not change the
kernel ideal sheaf. -/
lemma Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant {T : Scheme.{u}} (d : T ⟶ X')
    (γ : X' ⟶ X) [IsSchemeTheoreticallyDominant d] : (d ≫ γ).ker = γ.ker := by
  rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]

section FractionRing

variable (A K : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The inclusion of the generic point of the spectrum of a domain is
scheme-theoretically dominant. -/
instance : IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap A K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A K)]
    exact bot_le
  exact .of_isDominant _

variable {A K} {Y Z : Scheme.{u}}

/-- **Factorization through a closed subscheme over the spectrum of a domain**
(blueprint: `lemma:nagata-valuation-factor-closed`): let `A` be a domain with fraction
field `K`, let `ι : Z ⟶ Y` be a closed immersion and `γ : Spec A ⟶ Y` a morphism whose
restriction to the generic point `Spec K` factors through `Z`. Then `γ` factors
through `Z`. -/
theorem IsClosedImmersion.exists_lift_of_isFractionRing (ι : Z ⟶ Y) [IsClosedImmersion ι]
    (γ : Spec (CommRingCat.of A) ⟶ Y) (η : Spec (CommRingCat.of K) ⟶ Z)
    (hcomm : η ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ γ) :
    ∃ l : Spec (CommRingCat.of A) ⟶ Z, l ≫ ι = γ := by
  have hker : ι.ker ≤ γ.ker := by
    refine le_trans ?_ (le_of_eq
      ((Spec.map
        (CommRingCat.ofHom (algebraMap A K))).ker_comp_of_isSchemeTheoreticallyDominant γ))
    rw [← hcomm]
    exact Scheme.Hom.le_ker_comp η ι
  exact ⟨IsClosedImmersion.lift ι γ hker, IsClosedImmersion.lift_fac ι γ hker⟩

end FractionRing

end AlgebraicGeometry
