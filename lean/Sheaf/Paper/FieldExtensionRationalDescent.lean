/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.FieldExtensionComposition

/-! # Localization of integral coefficient comparisons

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- Rationalize a coherent family of integral adjunction comparisons on unchanged
integral representatives and scalar-localized Hom groups.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (3),
inverting ell on integral models and localized Hom groups
(blueprint: lem-sp-field-extension-rational-descent).

Proof: the actual compact-support functor is linear in constant coefficients.
Its adjunction implies that its right adjoint, unit, counit and Hom bijection
are linear: transpose multiplication by a constant and use naturality. The
pullback, Tate tensor and shift source is likewise linear. Extend these functors
on the same objects by sending c tensor f to c tensor F(f). Bilinearity and
localization's universal property give functors and preserve identities and
composition. Extend units, counits and gamma by tensoring their components with
one. Integral triangle identities give the rational adjunction. The actual tensor
completion unit identifies the localized source with rational pullback, twist and
shift; its representative formula is sourceIdentification_normalized. Apply
semilinear localization to each integral comparison; the image of the source
uniformizer is invertible in the larger coefficient field. This gives the
rational comparisons with their specified pure-tensor normalization. Functoriality
preserves the integral unit, counit, purity and three coefficient cocycle equations,
using the published localized balanced tensor associators. -/
theorem field_extension_rational_descent
    (m : ∀ E : FieldShriekSystem.Index P, IntegralModel P D E j p d)
    (i : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
      IntegralComparison P D j p d E F h (m E) (m F))
    (composition : ∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
      IntegralComposition P D j p d E F L h k (m E) (m F) (m L)
        (i E F h) (i F L k) (i E L (h.trans k))) :
    ∃ (r : ∀ E : FieldShriekSystem.Index P, RationalModel P D j p d E (m E))
      (q : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
        RationalComparison P D j p d E F h (m E) (m F) (i E F h) (r E) (r F)),
      ∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
        RationalComposition P D j p d E F L h k (m E) (m F) (m L)
          (i E F h) (i F L k) (i E L (h.trans k)) (r E) (r F) (r L)
          (q E F h) (q F L k) (q E L (h.trans k)) := by sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
