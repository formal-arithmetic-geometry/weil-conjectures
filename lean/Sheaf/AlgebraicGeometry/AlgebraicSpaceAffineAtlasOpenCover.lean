/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage

/-!
# Open covers of algebraic spaces by spaces with affine étale atlases

Source: Stacks Project, Properties of Spaces, Tag 03FY,
`lemma-union-of-quasi-compact` (blueprint: lem-a1-space-affine-atlas-open-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every algebraic space has a Zariski open cover whose members admit affine surjective
étale atlases and map into affine opens of the base. The predicate `IsJointlySurjective`
expresses coverage of field-valued point classes, allowing a common field extension.
The maps to `yoneda.obj (Over.mk W.ι)` express the affine-base factorizations: on the
category `Over S`, every presheaf has a unique map to the terminal presheaf `h_S`, so
these maps automatically commute with the structural maps to `S`.

Source: Stacks Project, Properties of Spaces, Tag 03FY, including the final sentence
(blueprint: lem-a1-space-affine-atlas-open-cover).

Proof:
1. Choose a representable surjective étale scheme atlas `V → X` using
   `def-trf-algebraic-space`. For every point of `V`, choose an affine neighbourhood
   `W` of its image in `S` and an affine neighbourhood `U` inside its inverse image.
   Use `lem-weil-pbc-affine-opens-basis` twice. The index is the set of points of `V`,
   in the universe of `def-weil-size-convention`; use the empty family when `V` is empty.
   By `lem-weil-pbc-morphism-factors-through-open-subscheme`, each `U → S` factors
   through its chosen `W`.
2. Each composite `h_U → h_V → X` is representable étale. On a scheme test, paste
   the atlas pullback with the pullback of `U → V`. The latter is an open immersion
   by `lem-weil-pbc-open-immersion-base-change`, and hence étale by
   `lem-weil-pbc-etale-composition-cancellation`, which also gives étale composition.
3. Apply `lem-a1-etale-scheme-map-open-image` to obtain an open subspace `X_i` and a
   representable surjective étale factor `h_U → X_i`. For a field-valued point of `X`,
   its pullback to `V` is a nonempty scheme. A point and its residue field give an
   extension lift into some `U`, proving coverage of point classes.
4. On a scheme test `T → X_i`, every residue-field point lifts to `U` after extension,
   since `h_U → X_i` is representable surjective. Thus `T → S` has image in `W`.
   Factor it uniquely through `W` by
   `lem-weil-pbc-morphism-factors-through-open-subscheme`. Uniqueness makes these
   factorizations natural in `T`, giving the map `X_i → h_W`. -/
theorem exists_affine_atlas_open_cover {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ (I : Type u) (Xi : I → AlgebraicSpace S) (j : ∀ i : I, Xi i ⟶ X)
      (U : I → Over S) (a : ∀ i : I, yoneda.obj (U i) ⟶ (Xi i).obj.obj),
      IsJointlySurjective (fun i : I ↦ (j i).hom.hom) ∧
      ∀ i : I,
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (j i).hom.hom ∧
        IsAffine (U i).left ∧ IsEtale (a i) ∧ IsSurjective (a i) ∧
        ∃ W : S.Opens, IsAffine W.toScheme ∧
          Nonempty ((Xi i).obj.obj ⟶ yoneda.obj (Over.mk W.ι)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
