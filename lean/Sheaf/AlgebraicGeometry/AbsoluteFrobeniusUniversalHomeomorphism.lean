/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# Absolute finite-field Frobenius is a universal homeomorphism

Source: Stacks Project, Tag 0CC8, lemma-frobenius (blueprint:
lem-pur-absolute-frobenius-universal-homeomorphism).

The theorem below specializes the absolute `p ^ a`-power Frobenius construction to the
fixed finite-field datum.  It imposes no finite-type, separatedness, or nonemptiness
condition on the scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ n = (f.app U).hom (s ^ p ^ n)
  exact (map_pow (f.app U).hom s _).symm

namespace WeilConjectures.FiniteFieldDatum

/-- For every scheme over the fixed finite field, the absolute `q`-power Frobenius is a
universal homeomorphism.

Source: Stacks Project, Tag 0CC8, lemma-frobenius, applied to the `a`-fold iterate;
Lean source: `WeilConjectures/AlgebraicGeometry/Morphisms/Frobenius.lean`,
`AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism`
(blueprint: lem-pur-absolute-frobenius-universal-homeomorphism).
The source proof checks the affine `q`-power map: it is integral, universally injective,
and surjective, and these properties are local on the target.  The construction
`Scheme.iterateFrobenius` is the identity on points and raises sections to `p ^ a = q`
powers; `model_characteristic` supplies the characteristic hypothesis for every
scheme over the finite base.  Applying the upstream `IsFrobenius` universal-homeomorphism
theorem gives the displayed conclusion, including the empty scheme.
-/
theorem absoluteFrobenius_isUniversalHomeomorphism
    (D : WeilConjectures.FiniteFieldDatum.{u}) (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of D.k₀))] :
    IsUniversalHomeomorphism
      (T.iterateFrobenius D.prime
        (D.model_characteristic (T ↘ Spec (CommRingCat.of D.k₀))) D.a) := by
  have hF : (T.iterateFrobenius D.prime
      (D.model_characteristic (T ↘ Spec (CommRingCat.of D.k₀))) D.a).IsFrobenius
        (Nat.card D.k₀) := by
    intro R t φ hφ
    have hR := D.model_characteristic (t ≫ T ↘ Spec (CommRingCat.of D.k₀))
    have hSpec : (Spec R).iterateFrobenius D.prime hR D.a = Spec.map φ := by
      apply AlgebraicGeometry.ext_to_Spec
      change (Scheme.ΓSpecIso R).inv ≫
          ((Spec R).iterateFrobenius D.prime hR D.a).appTop =
        (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop
      rw [← Scheme.ΓSpecIso_inv_naturality]
      ext x
      change ((Scheme.ΓSpecIso R).inv x) ^ D.p ^ D.a =
        (Scheme.ΓSpecIso R).inv (φ.hom x)
      rw [hφ, D.card_base, D.cardinality_eq, map_pow]
    rw [← iterateFrobenius_naturality t D.prime hR
      (D.model_characteristic (T ↘ Spec (CommRingCat.of D.k₀))) D.a, hSpec]
  exact hF.isUniversalHomeomorphism (T ↘ Spec (CommRingCat.of D.k₀))

end WeilConjectures.FiniteFieldDatum
