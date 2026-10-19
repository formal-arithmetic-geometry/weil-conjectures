/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization

import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection

/-!
# Relative normalization in a dense open of a normal scheme

Sources: Stacks Project, Tags 0357, 035I and 0AB1.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian normal scheme is its own relative normalization in a dense open.

Source: Stacks Project, Tags 0357 (normal components), 035I (relative normalization),
and 0AB1 (integral birational maps to normal schemes).
(blueprint: lem-sbc-normalization-dense-open)

Proof: This is local on X. On an affine open Spec A, the Noetherian normal ring A
is a finite product of integrally closed domains A_i (0357). The intersection of V
with each Spec A_i is a nonempty open, since V is dense. It therefore contains the
generic point. Its section ring embeds in Frac(A_i), by restriction to the generic
point: sections on an integral scheme are determined by their generic germ.
Every section integral over A_i then lies in A_i by integral closedness. Conversely,
every element of A_i gives an integral section. Taking the finite product shows
that the integral closure of A in the sections on V intersect Spec A is exactly A.
The relative normalization over Spec A is the spectrum of this integral closure
(035I), so its canonical map to Spec A is an isomorphism. These local assertions
show the canonical map is an isomorphism on X. Empty affine opens contribute the
zero ring; if X is empty the same assertion holds. No nonemptiness of X is needed. -/
theorem isIso_fromNormalization_denseOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (V : X.Opens) (hV : Dense (V : Set X)) :
    IsIso V.ι.fromNormalization := by
  have (z : X) : IsDomain (X.presheaf.stalk z) := (hnormal z).1
  have (z : X) : _root_.IsReduced (X.presheaf.stalk z) := inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsDominant V.ι := by
    rw [isDominant_iff, DenseRange, Opens.range_ι]
    exact hV
  have := IsSchemeTheoreticallyDominant.of_isDominant V.ι
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme)
      (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)]
  intro U
  change IsIso (V.ι.fromNormalization ∣_ U.1)
  refine (isIso_morphismRestrict_iff_isIso_app V.ι.fromNormalization U.2).mpr ?_
  let := (V.ι.app U.1).hom.toAlgebra
  rw [Hom.fromNormalization_app V.ι U.2]
  have hbij : Function.Bijective
      (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) Γ(V, V.ι ⁻¹ᵁ U.1))) := by
    refine ⟨fun a b hab ↦ V.ι.app_injective U.1 (congrArg Subtype.val hab), ?_⟩
    intro s
    obtain ⟨t, ht⟩ := exists_integral_section_denseOpen hnormal V hV U.1 U.2 s.1 s.2
    exact ⟨t, Subtype.ext ht⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (integralClosure Γ(X, U.1) Γ(V, V.ι ⁻¹ᵁ U.1)))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  infer_instance

end AlgebraicGeometry.Scheme
