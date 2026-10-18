/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The open image of an étale scheme map to an algebraic space

Source: Stacks Project, Properties of Spaces, Tag 06NF, `lemma-etale-image-open`,
first assertion and factorization (blueprint: lem-a1-etale-scheme-map-open-image).

The point-image equality is expanded on field-valued representatives. Membership in an
open subspace means that the representative factors through it. Membership in the image
of a scheme means that the representative lifts to the scheme after a field extension;
this is exactly equality with a scheme point over a common field extension.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale scheme map factors through its open point image as a representable,
surjective étale map. Componentwise injectivity identifies the image space as a
subfunctor; its inclusion is representable by open immersions.
Source: Stacks Project, Properties of Spaces, Tag 06NF, first assertion and factorization
(blueprint: lem-a1-etale-scheme-map-open-image).
Proof: apply `lem-a1-space-etale-open-image` to `E = h_U`, `F = X` and `q = f`.
The general theorem supplies the open subspace, its representable open inclusion, and
the representable surjective étale factorization. Its point image is the image of
`|h_U| → |X|`; the field-valued point classes of `h_U` are exactly those of `U`.
For the displayed point condition, a class is in the scheme image precisely when its
representative lifts after a field extension: restrict a scheme representative along the
common field extension in the equivalence relation. A representative of a class in an
open subspace factors through that subspace already over its original field, since the
pullback open subscheme of `Spec K` is nonempty after extension and hence is all of
`Spec K`. These observations give the final equivalence. -/
theorem etaleSchemeMap_openImage {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over S)
    (f : yoneda.obj U ⟶ X.obj.obj) (hf : IsRepresentable f) (he : IsEtale f) :
    ∃ (Xf : AlgebraicSpace S) (j : Xf ⟶ X) (ff : yoneda.obj U ⟶ Xf.obj.obj),
      (∀ T : (Over S)ᵒᵖ, Function.Injective (j.hom.hom.app T)) ∧
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom ∧
      ff ≫ j.hom.hom = f ∧
      IsRepresentable ff ∧ IsSurjective ff ∧ IsEtale ff ∧
      ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
        (x : X.obj.obj.obj (op (Over.mk s))),
        (∃ y : Xf.obj.obj.obj (op (Over.mk s)), j.hom.hom.app _ y = x) ↔
          ∃ (L : Type u) (_ : Field L) (e : K →+* L)
            (y : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U),
            f.app _ y =
              X.obj.obj.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
