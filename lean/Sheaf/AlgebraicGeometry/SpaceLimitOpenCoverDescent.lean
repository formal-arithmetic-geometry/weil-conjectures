/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of finite quasi-compact open covers of algebraic-space limits

Source: Stacks Project, Spaces and Morphisms of Spaces, Situation 084R,
Tag 0827 (lemma-descend-opens), Tag 07SR (lemma-limit-is-scheme), and Tag 086W
(lemma-limit-nonempty) (blueprint: lem-sfb-space-limit-open-cover-descent).

Quasi-compactness is written as existence of a quasi-compact surjective etale scheme atlas.
For unbundled open subfunctors, quasi-separatedness is the affine-test formula of
`IsAbsolutelyQuasiSeparated`, written out on their underlying presheaves. Equality of
subfunctors specifies descent. Covering is a union of point images, rather than the
sectionwise union of subfunctors, which need not be a sheaf. The restricted transition
is uniquely determined by its commuting square with the open inclusions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite quasi-compact open covers descend to a stage beyond any prescribed index,
with quasi-separated members and affine transitions on every subsequent inverse image.
Source: Stacks Project, Situation 084R, Tags 0827, 07SR and 086W
(blueprint: lem-sfb-space-limit-open-cover-descent).

Proof:
1. Pass to the cofinal tail above i0. By lem-trf-space-qc-finite-affine-atlas-refinement
   choose an affine surjective etale atlas U0 of X_i0. Pull it back to U_i and U.
   Lemmas lem-sfb-space-affine-locality, lem-weil-pbc-limit-affine-transition and
   lem-trf-space-fibre-products-etale-covers identify these with affine schemes and
   U with their scheme limit. Affine permanence makes X qcqs.
2. Each W_a is quasi-separated by lem-sfb-space-integral-qcqs-permanence. By
   lem-sfb-space-qcqs-source-products its atlas pullback E_a is a qcqs open of U.
   Apply pqf-lem-limit-qc-open-descends to descend each E_a to a stage.
3. Take a common upper bound k of those finitely many stages and i0, using i0 for
   the empty family. Affine base change preserves quasi-compactness of the descended
   opens, by lem-weil-pbc-affine-morphism-permanence.
4. Take the image open of E_a,k -> X_k. Lemmas lem-a1-space-etale-open-image,
   lem-weil-pbc-open-immersion-etale and lem-trf-space-chartwise-etale-permanence
   show it is quasi-compact and pulls back to W_a, using the surjective atlas.
5. Pull the union of these image opens back to U_k. Its inverse image is all U.
   By lem-weil-pbc-limit-image-contained-in-open it becomes all U_i for some i >= k.
   Surjectivity of the atlas and lem-a1-space-point-open-calculus give a covering of
   X_i. This also works for the empty family: U_i, and hence X_i, becomes empty.
6. Lemmas lem-sfb-space-integral-qcqs-permanence and lem-sfb-space-affine-locality
   give quasi-separatedness of the descended opens and qcqs of every later inverse
   image. The restricted transitions are affine by base change. The point/open
   calculus shows that these inverse images cover every later stage. -/
theorem exists_stage_finite_qc_open_cover
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hqc : ∀ i : Iᵒᵖ, ∃ (T : Over S) (a : yoneda.obj T ⟶ (D.obj i).obj.obj),
      CompactSpace T.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map f).hom.hom)
    (X : AlgebraicSpace S)
    (π : (Functor.const Iᵒᵖ).obj X.obj ⟶ D ⋙ ObjectProperty.ι IsAlgebraicSpace)
    (hlim : IsLimit (Cone.mk X.obj π)) (i₀ : I)
    {A : Type u} [Finite A] (W : A → OpenSubspace X)
    (hWqc : ∀ a : A, ∃ (T : Over S) (b : yoneda.obj T ⟶ (W a).val.toFunctor),
      CompactSpace T.left ∧ IsEtale b ∧ IsSurjective b)
    (hcover : (⋃ a : A, pointImage (W a).val.ι) = Set.univ) :
    ∃ (i : I), i₀ ≤ i ∧ ∃ V : A → OpenSubspace (D.obj (op i)),
      (∀ a : A, (V a).val.preimage (π.app (op i)).hom = (W a).val) ∧
      (∀ (j : I) (hij : i ≤ j),
        ∃ Vj : A → OpenSubspace (D.obj (op j)),
          (∀ a : A, (Vj a).val = (V a).val.preimage
            (D.map (homOfLE hij).op).hom.hom) ∧
          (∀ a : A, ∃ (T : Over S) (b : yoneda.obj T ⟶ (Vj a).val.toFunctor),
            CompactSpace T.left ∧ IsEtale b ∧ IsSurjective b) ∧
          (∀ (a : A) (U₁ U₂ : Over S)
            (b₁ : yoneda.obj U₁ ⟶ (Vj a).val.toFunctor)
            (b₂ : yoneda.obj U₂ ⟶ (Vj a).val.toFunctor),
            IsAffine U₁.left → IsAffine U₂.left →
              CompactSpace (Point (Limits.pullback b₁ b₂))) ∧
          (⋃ a : A, pointImage (Vj a).val.ι) = Set.univ) ∧
      (∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (a : A),
        ∃ q : ((V a).val.preimage
            (D.map (homOfLE (le_trans hij hjk)).op).hom.hom).toFunctor ⟶
          ((V a).val.preimage (D.map (homOfLE hij).op).hom.hom).toFunctor,
          q ≫ ((V a).val.preimage (D.map (homOfLE hij).op).hom.hom).ι =
            ((V a).val.preimage
              (D.map (homOfLE (le_trans hij hjk)).op).hom.hom).ι ≫
                (D.map (homOfLE hjk).op).hom.hom ∧
          IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) q) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
