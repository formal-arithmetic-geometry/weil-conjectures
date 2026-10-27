/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Eventual properness of finite type algebraic spaces

Source: Stacks Project, Limits of Spaces, Situation 084W and Tag 08K1,
`lemma-eventually-proper`, with affine bases and target equal to the base
(blueprint: lem-sfb-space-finite-type-eventually-proper).

Schemes over Spec Z are retained as schemes, and their Yoneda sheaves are the existing
`schemeSpace` construction. Base changes are actual sheaf fibre products. Only local
finite type and absolute qcqs of the initial source are required.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness over an affine inverse limit descends to a stage for a locally finite type
map with qcqs source. No finite presentation or flatness is assumed.
Source: Stacks Project, Limits of Spaces, Situation 084W and Tag 08K1,
`lemma-eventually-proper` (blueprint: lem-sfb-space-finite-type-eventually-proper).

Proof:
1. Put a = i₀. Affine bases are qcqs [lem-weil-pbc-affine-scheme-qcqs]. The qcqs-source
   permanence [lem-sfb-space-qcqs-permanence] makes hₐ quasi-compact and hence finite type.
   The product Dₐ = Wₐ ×_{Tₐ} Wₐ is qcqs [lem-sfb-space-qcqs-source-products], and its
   diagonal is representable and locally finite type
   [lem-sfb-space-diagonal-locally-finite-type].
2. Sheaf pullback pasting [lem-trf-space-fibre-products-etale-covers] identifies the
   limit diagonal with the base change of this diagonal. Properness makes it closed
   [def-sfb-space-morphism-properties]. By [lem-sfb-space-descend-closed-immersion],
   the diagonal is closed at some b ≥ a, so h_b is separated.
3. Restrict to the cofinal directed tail above b; common upper bounds identify its limit
   with T. Fibre-product associativity identifies all later Wᵢ with W_b ×_{T_b} Tᵢ.
   The sources remain qcqs [lem-sfb-space-qcqs-source-products]. Local finite type and
   quasi-compactness persist [lem-sfb-stack-finite-type-calculus] and
   [lem-sfb-space-qcqs-permanence], as does separatedness
   [lem-sfb-space-separated-fp-composition]. Thus the later maps are separated finite type.
4. Weak Chow [lem-sfb-space-weak-chow] gives a qc separated scheme C_b, a proper
   universally surjective π_b : C_b → W_b, and an immersion j_b into P^n_{T_b}, for n ≥ 0.
   Base change this diagram to each stage and the limit, using
   [def-nagata-projective-space-base-change], [lem-trf-space-fibre-products-etale-covers],
   [lem-weil-pbc-immersion-base-change-lft] and [lem-sfb-space-proper-base-change].
5. At the limit C → T is proper by [lem-sfb-space-proper-composition], also as a scheme
   map by [lem-sfb-space-representable-proper-tests]. Projective space is proper and
   separated [lemma-nagata-projective-space-base-change-proper]. Consequently j is proper
   [lem-weil-pbc-proper-over-separated], hence closed since it is an immersion
   [lem-weil-pbc-proper-immersion-closed].
6. C_b is qcqs by [lem-pc-separated-quasi-separated]. Projective space over the affine
   base is qcqs [lem-weil-pbc-qcqs-morphism-permanence]. The immersion j_b is locally
   finite type [lem-weil-pbc-immersion-base-change-lft], so scheme closed-immersion descent
   [lem-weil-pbc-descend-closed-immersion] gives c ≥ b with j_c closed.
7. The composite C_c → P^n_{T_c} → T_c is proper
   [lem-weil-pbc-proper-fp-permanence] and
   [lemma-nagata-projective-space-base-change-proper], also as a space map by
   [lem-sfb-space-representable-proper-tests].
8. After every space base change B → T_c, π_B remains surjective. For a closed subset F
   of |W_c ×_{T_c} B|, continuity [lem-a1-space-point-open-calculus] makes π_B⁻¹(F)
   closed, and properness [lem-sfb-space-proper-base-change] gives its closed image in B.
   Surjectivity identifies this image with h_B(F). Thus h_c is universally closed,
   separated and finite type, exactly [def-sfb-space-morphism-properties], and c ≥ i₀. -/
theorem exists_proper_stage_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (htrans : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W₀ : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (h₀ : W₀ ⟶ schemeSpace (D.obj (op i₀)))
    (hqc : ∃ (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (a : yoneda.obj U ⟶ W₀.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : MapIsQuasiCompact (prod.lift (𝟙 W₀.obj.obj) (𝟙 W₀.obj.obj)))
    (hlft : MapIsLocally (@LocallyOfFiniteType) h₀)
    (hproper : MapIsProper (enlargedFibreProductFst
      (ObjectProperty.homMk (X := schemeSpace c.pt) (Y := schemeSpace (D.obj (op i₀)))
        ((Scheme.fppfTopology.over _).yoneda.map (c.π.app (op i₀)))) h₀)) :
    ∃ (j : I) (hj : i₀ ≤ j),
      MapIsProper (enlargedFibreProductFst
        (ObjectProperty.homMk (X := schemeSpace (D.obj (op j)))
          (Y := schemeSpace (D.obj (op i₀)))
          ((Scheme.fppfTopology.over _).yoneda.map (D.map (homOfLE hj).op))) h₀) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
