/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import Sheaf.AlgebraicGeometry.AlgebraicSpaceComposeAdmissibleBlowups
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Common admissible blowups of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 088Q
(lemma-find-common-blowups); Divisors on Spaces, Tag 086B
(blueprint: lem-sfb-space-common-admissible-blowups).

The existing blowup presentations specify the actual descended scheme blowups up to
isomorphism over the original spaces. The cartesian squares over U require the entire
inverse images of U to be the specified common open; no density is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two separated finite-type spaces with a common open have admissible blowups which
embed openly into a common separated finite-type space, agreeing on that open.
Source: Stacks Project, More on Morphisms of Spaces, Tag 088Q; Tag 086B
(blueprint: lem-sfb-space-common-admissible-blowups).

Proof:
1. Finite type over the qcqs base implies quasi-compactness; separatedness and
   lem-sfb-space-qcqs-source-products give absolute quasi-separatedness. Apply this
   to U and both X_i. By lem-sfb-space-qcqs-permanence the open immersions are
   quasi-compact. Form P = X_1 times_B X_2, using
   lem-sfb-space-four-property-fppf-descent and the finite-type and separated
   composition lemmas for its finiteness and separation properties.
2. Apply lem-sfb-space-partial-section-schematic-image to the map U to P over each
   X_i. The two smallest closed images coincide, giving C with separated finite-type
   projections to X_i which are isomorphisms over U. Use
   lem-sfb-space-closed-subspace-proper and the composition lemmas.
3. Apply lem-sfb-space-zariski-after-admissible-blowup to both projections. This
   gives admissible blowups A_i of X_i containing C_i, the blowups of C in the
   pulled-back centre ideals, as opens. Properness of the blowups from
   lem-sfb-space-blowup-chart-properties gives the required finiteness and qcqs.
4. Blow up C in the product of the two centre ideals. By
   lem-sfb-space-blowup-product-ideal-comparison the resulting T is an admissible
   blowup of each C_i. The centre ideals remain finite type and unit on U.
   lem-sfb-space-blowup-chart-properties identifies every inverse image of U with U.
5. Extend these blowups from C_i to A_i by lem-sfb-space-extend-admissible-blowup,
   giving D_i containing the same T openly. Properness and the composition lemmas
   keep D_i separated and finite type over B.
6. By lem-sfb-space-compose-admissible-blowups, D_i to X_i is a single admissible
   blowup in a finite-type ideal, with its identification over U.
7. The map T to D_1 times_B D_2 is proper by lem-sfb-space-proper-cancellation:
   its composite to X_1 times_B X_2 is proper, and the comparison of products is
   separated. Use lem-sfb-space-proper-composition and blowup properness.
8. This map is an immersion, factoring as a graph closed immersion followed by an
   open immersion. On scheme tests lem-sfb-space-immersion-affine-tests and
   lem-sfb-space-proper-base-change allow lem-weil-pbc-proper-immersion-closed.
   Hence it is representable by closed immersions.
9. Glue D_1 and D_2 along T with lem-sfb-space-glue-two-opens. The resulting W is
   finite type over B: local finite type follows from
   lem-sfb-scheme-etale-source-target-properties, and quasi-compactness from the
   finite cover by the two quasi-compact opens after every quasi-compact scheme test.
10. Check the relative diagonal on its four open parts. The same-index parts are
    the closed diagonals of D_i; the mixed parts are the closed immersion of step 8
    and its transpose. lem-sfb-space-closed-immersion-atlas-locality gives separation.
11. Transport the embeddings by the blowup isomorphisms from step 6. The complement
    isomorphism in lem-sfb-space-blowup-chart-properties identifies the full inverse
    images of U with U. Both copies pass through the same U in T, so their maps to W
    agree. This argument also applies to empty U and never assumes density. -/
theorem exists_common_admissible_blowups
    {S : Scheme.{u}} (B X₁ X₂ U : AlgebraicSpace S)
    (hBqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ B.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hBqs : IsAbsolutelyQuasiSeparated B)
    (x₁ : X₁ ⟶ B) (x₂ : X₂ ⟶ B) (v : U ⟶ B)
    (hx₁s : MapIsSeparated x₁) (hx₁ft : MapIsFiniteType x₁)
    (hx₂s : MapIsSeparated x₂) (hx₂ft : MapIsFiniteType x₂)
    (hvs : MapIsSeparated v) (hvft : MapIsFiniteType v)
    (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    (hj₁ : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j₁.hom.hom)
    (hj₂ : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j₂.hom.hom)
    (hj₁B : j₁ ≫ x₁ = v) (hj₂B : j₂ ≫ x₂ = v) :
    ∃ (I₁ : QuasiCoherentIdeal X₁) (I₂ : QuasiCoherentIdeal X₂),
      (I₁.val : X₁.Modules).IsFiniteType ∧ (I₂.val : X₂.Modules).IsFiniteType ∧
      (∀ V : X₁.EtaleSite,
        (∃ a : yoneda.obj V.obj.left ⟶ U.obj.obj, a ≫ j₁.hom.hom = V.obj.hom) →
          idealSectionImage I₁.val.arrow V = ⊤) ∧
      (∀ V : X₂.EtaleSite,
        (∃ a : yoneda.obj V.obj.left ⟶ U.obj.obj, a ≫ j₂.hom.hom = V.obj.hom) →
          idealSectionImage I₂.val.arrow V = ⊤) ∧
      ∃ (D₁ : BlowupPresentation I₁) (D₂ : BlowupPresentation I₂)
        (W : AlgebraicSpace S) (w : W ⟶ B)
        (e₁ : D₁.space ⟶ W) (e₂ : D₂.space ⟶ W),
        MapIsSeparated w ∧ MapIsFiniteType w ∧
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) e₁.hom.hom ∧
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) e₂.hom.hom ∧
        e₁ ≫ w = D₁.projection ≫ x₁ ∧ e₂ ≫ w = D₂.projection ≫ x₂ ∧
        ∃ (s₁ : U ⟶ D₁.space) (s₂ : U ⟶ D₂.space),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) s₁.hom.hom ∧
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) s₂.hom.hom ∧
          IsPullback s₁ (𝟙 U) D₁.projection j₁ ∧
          IsPullback s₂ (𝟙 U) D₂.projection j₂ ∧ s₁ ≫ e₁ = s₂ ≫ e₂ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
