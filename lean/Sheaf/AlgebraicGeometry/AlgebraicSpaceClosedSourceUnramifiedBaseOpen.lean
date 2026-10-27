/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Universal unramified parameter open for an algebraic-space diagram

Source: Stacks Project, More on Morphisms of Spaces, Tag 05X8,
`lemma-where-unramified` (blueprint: lem-sfb-space-closed-source-unramified-base-open).

Closedness is required only of the original point map of the source to the base.
The universal property tests every algebraic-space base change. The last clause gives
an open subscheme whenever the base algebraic space is represented by a scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed, locally finite type source over the base gives a universal open on which
its map to another space over the base becomes unramified.
Source: Stacks Project, More on Morphisms of Spaces, Tag 05X8,
`lemma-where-unramified` (blueprint: lem-sfb-space-closed-source-unramified-base-open).

Proof: (1) By lem-sfb-space-lft-cancellation, u is locally of finite type. Apply
lem-sfb-space-unramified-locus-base-change to get its maximal unramified open U in A.
(2) Let D be the complement of the point image of U. It is closed by
lem-a1-space-point-open-calculus. Closedness of the point map of p makes E = p(D)
closed. By lem-a1-space-etale-open-image the complement of E corresponds to an open W
in B. This uses closedness of p itself only.
(3) For any g : B' to B, the sheaf fibre products are algebraic spaces by
lem-trf-space-fibre-products-etale-covers. The pullback A' identifies with A times_C C'
by sending (a,b') to (a,(u(a),b')). The unramified-locus base-change theorem therefore
identifies the bad locus D' in A' with the inverse image of D.
(4) The image of D' in B' equals the inverse image of E. One inclusion follows from
commutativity; the reverse follows by lifting compatible point pairs using
lem-a1-space-point-open-calculus. Thus D' is empty exactly when the image of g lies
in W. The maximal-locus property says D' is empty exactly when the induced map is
unramified. By lem-a1-space-open-factor-scheme-tests, containment of the image of g
in W is equivalent to factorization through W, giving both implications.
(5) If B is represented by T, apply the defining scheme-test condition of
 def-a1-space-open-subspace to the identity of T transported through the representing
isomorphism. It gives an open immersion V to T and an isomorphism of W with h_V
compatible with their inclusions. No flatness or stack hypothesis is used. -/
theorem exists_openSubspace_universal_unramified_of_closed_source {S : Scheme.{u}}
    (A C B : AlgebraicSpace S) (p : A ⟶ B) (q : C ⟶ B) (u : A ⟶ C)
    (w : u ≫ q = p) (hp_lft : MapIsLocally (@LocallyOfFiniteType) p)
    (hp_closed : IsClosedMap (mapPoint p.hom.hom)) :
    ∃ W : OpenSubspace B,
      (∀ (B' : AlgebraicSpace S) (g : B' ⟶ B),
        (∃ l : B'.obj.obj ⟶ W.val.toFunctor, l ≫ W.val.ι = g.hom.hom) ↔
          MapIsLocally (@AlgebraicGeometry.IsUnramified)
            (X := ⟨Limits.pullback p.hom g.hom,
              (fibreProduct_isAlgebraicSpace A B' B p g).1⟩)
            (Y := ⟨Limits.pullback q.hom g.hom,
              (fibreProduct_isAlgebraicSpace C B' B q g).1⟩)
            (ObjectProperty.homMk
              (pullback.map p.hom g.hom q.hom g.hom u.hom (𝟙 B'.obj) (𝟙 B.obj)
                (by simpa using (congrArg (fun k : A ⟶ B ↦ k.hom) w).symm)
                (by simp)))) ∧
      (∀ (T : Over S) (e : B.obj.obj ≅ yoneda.obj T),
        ∃ (V : Over S) (j : V ⟶ T), IsOpenImmersion j.left ∧
          ∃ eW : W.val.toFunctor ≅ yoneda.obj V,
            W.val.ι ≫ e.hom = eW.hom ≫ yoneda.map j) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
