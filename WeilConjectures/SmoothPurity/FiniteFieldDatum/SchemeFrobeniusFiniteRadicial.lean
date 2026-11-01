/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# Finiteness and radiciality of the scalar-extended scheme Frobenius

Source: Stacks Project, Tags 0CCD, 0CCB, and 0CCG in `varieties.tex`;
Tags 01WL, 0472, and 01S4 in `morphisms.tex`
(blueprint: lem-trf-scheme-frobenius-finite-radicial).

The scalar-extended q-power Frobenius of a finite-type scheme over the fixed
finite field is finite and radicial.  Radiciality is rendered by Mathlib's
`UniversallyInjective`, equivalent to the residue-field formulation in Tag 01S4.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scalar-extended q-power Frobenius is finite and radicial.
Source: Stacks Project, Tags 0CCD, 0CCB, and 0CCG in `varieties.tex`,
and Tags 01WL, 0472, and 01S4 in `morphisms.tex`
(blueprint: lem-trf-scheme-frobenius-finite-radicial).

Proof:
1. Check that the constructed model endomorphism satisfies the source library's
   `Scheme.Hom.IsFrobenius` predicate at `Nat.card D.k₀ = D.p ^ D.a`.
   Naturality follows on every open from preservation of powers by `t.app U`.
   On `Spec R`, the global-sections adjunction identifies the constructed map
   with `Spec.map φ` whenever `φ` is the cardinality-power ring map.
2. The geometric fibre is the chosen pullback. Its two projection identities
   are `relativeFrobenius_projections`. Apply the source library's
   `IsFrobenius.isFinite_of_isPullback` and
   `IsFrobenius.isUniversalHomeomorphism_of_isPullback` to this square.
3. A universal homeomorphism is universally injective. Pair this with finiteness.
   No separatedness or reducedness is used.
-/
theorem relativeFrobenius_isFinite_isRadicial
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (D.relativeFrobenius X₀) ∧
      UniversallyInjective (D.relativeFrobenius X₀) := by
  have hF : (X₀.left.iterateFrobenius D.prime
      (D.model_characteristic X₀.hom) D.a).IsFrobenius (Nat.card D.k₀) := by
    intro R t φ hφ
    have hR := D.model_characteristic (t ≫ X₀.hom)
    have hn : t ≫ X₀.left.iterateFrobenius D.prime
        (D.model_characteristic X₀.hom) D.a =
        (Spec R).iterateFrobenius D.prime hR D.a ≫ t := by
      refine Scheme.Hom.ext (f := t ≫ _) (g := _ ≫ t) rfl ?_
      intro U
      simp only [eqToHom_refl, Scheme.Hom.comp_app]
      ext s
      change t.app U (s ^ D.p ^ D.a) = (t.app U s) ^ D.p ^ D.a
      exact map_pow (t.app U).hom s (D.p ^ D.a)
    have ha : (Spec R).iterateFrobenius D.prime hR D.a = Spec.map φ := by
      apply AlgebraicGeometry.ext_to_Spec
      change (Scheme.ΓSpecIso R).inv ≫
          ((Spec R).iterateFrobenius D.prime hR D.a).appTop =
        (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop
      rw [← Scheme.ΓSpecIso_inv_naturality]
      ext x
      change ((Scheme.ΓSpecIso R).inv x) ^ D.p ^ D.a =
        (Scheme.ΓSpecIso R).inv (φ x)
      rw [hφ, map_pow, D.card_base, D.cardinality_eq]
    rw [hn, ha]
  have hp := IsPullback.of_hasPullback X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hΦ := D.relativeFrobenius_projections X₀
  have hfinite := hF.isFinite_of_isPullback hp hΦ.2 hΦ.1
  have hhomeo := hF.isUniversalHomeomorphism_of_isPullback hp hΦ.2 hΦ.1
  exact ⟨hfinite, hhomeo.toUniversallyInjective⟩

end WeilConjectures.FiniteFieldDatum
