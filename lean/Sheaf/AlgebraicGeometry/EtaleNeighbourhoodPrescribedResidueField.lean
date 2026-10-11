/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Separable

/-!
# Étale neighbourhoods with a prescribed residue field

Source: Stacks Project, More on Morphisms, Lemma 02LF
(blueprint: lem-weil-pbc-etale-neighbourhood-prescribed-residue-field).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite separable extension of the residue field of a scheme point is realized by
an étale neighbourhood, compatibly with the induced residue-field map.
Source: Stacks Project, More on Morphisms, Lemma 02LF
(blueprint: lem-weil-pbc-etale-neighbourhood-prescribed-residue-field).

Proof:
1. Choose an affine open chart `Spec R → S` containing `s`, with corresponding prime `p`
   (`lem-weil-pbc-affine-open-spec-points`). Identify `κ(s)` with `κ(p)` using the open
   immersion's residue-field isomorphism and the affine residue-field identification
   (`lem-weil-pbc-residue-field-point-naturality`,
   `lem-weil-pbc-spec-residue-field-identification`). Call this composite `θ`.
2. Transport the extension `k/κ(s)` along `θ` to an extension `L/κ(p)`. A basis transports,
   so finiteness is preserved. The coefficientwise polynomial isomorphism transports
   minimal polynomials and preserves separability, so the extension remains separable.
3. Apply `lem-weil-pbc-etale-ring-map-prescribed-residue-field` (Stacks 00UD) to obtain an
   étale map `R → R'`, a prime `p'` over `p`, and an isomorphism `λ : κ(p') → L` compatible
   with the structure maps.
4. Set `U = Spec R'`, `u = p'`, and compose `Spec R' → Spec R → S` to obtain `φ`.
   It is étale by `lem-weil-pbc-etale-composition-cancellation` and maps `u` to `s` by
   `lem-weil-pbc-spec-map-residue-field-naturality`.
5. Residue-field maps respect composition. The same Spec naturality lemma identifies
   the map for `Spec R' → Spec R` with `κ(p) → κ(p')`. Composing `λ⁻¹` with the inverse
   affine identification for `R'` gives `e : k → κ(u)`. Compatibility of `λ` shows that
   `e` composed with the structure map of `k` equals the residue-field map of `φ`.
-/
theorem Scheme.exists_etale_neighbourhood_prescribed_residueField
    (S : Scheme.{u}) (s : S) (k : Type v) [Field k]
    [Algebra (S.residueField s) k] [FiniteDimensional (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S), Etale φ ∧
      ∃ (u : U) (h : φ u = s) (e : k ≃+* U.residueField u),
        ∀ a : S.residueField s,
          e (algebraMap (S.residueField s) k a) =
            (φ.residueFieldMap u).hom ((S.residueFieldCongr h).inv.hom a) := by
  sorry

end AlgebraicGeometry
