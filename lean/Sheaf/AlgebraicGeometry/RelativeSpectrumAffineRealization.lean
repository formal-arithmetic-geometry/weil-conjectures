/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Existence of an affine realization of a quasi-coherent algebra

Source: Stacks Project, Constructions, Lemmas 01LP and 01LV
(blueprint: lem-weil-pbc-relative-spectrum-affine-realization).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

/-- Every quasi-coherent algebra is the direct image of the structure algebra of an
 affine scheme over the base.
Source: Stacks Project, Constructions, Lemmas 01LP and 01LV, Lemma 01LX (1), (3)
(blueprint: lem-weil-pbc-relative-spectrum-affine-realization).

Proof: For each affine open U of S take X_U = Spec A(U), with structure map to U
induced by O_S(U) → A(U). For V contained in U, the restriction A(U) → A(V)
induces a map X_V → X_U. The quasi-coherent algebra affine-inclusion lemma identifies
its image with the inverse image of V and proves the cartesian condition; functoriality
of Spec and restriction proves the identity and composition laws. Relative gluing over
the directed affine cover constructs X → S with inverse image of U isomorphic to X_U.
Thus the morphism is affine. On each affine U, the canonical ring isomorphism
A(U) ≅ Gamma(Spec A(U)) followed by the chart's map on sections gives
A(U) ≅ O_X(f⁻¹ U). These commute with restrictions by compatibility of the gluing
charts, and with the O_S(U)-structure maps because the charts are over U. Extend on
the affine basis to an algebra morphism A → f_* O_X; it is an isomorphism because
all its affine components are isomorphisms. For empty S the gluing is empty and the
same sheaf argument applies. Zero section rings give empty spectral pieces, as usual. -/
theorem exists_affine_structure_algebra (S : Scheme.{u}) (A : S.CommAlgebraSheaf)
    (hA : A.toModule.IsQuasicoherent) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S), IsAffineHom f ∧ Nonempty (A ≅ 𝒪⁎ f) := by sorry

end AlgebraicGeometry
