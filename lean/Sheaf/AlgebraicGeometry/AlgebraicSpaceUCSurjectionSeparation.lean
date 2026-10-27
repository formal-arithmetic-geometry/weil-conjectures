/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Absolute separation descends under universally closed surjections

Source: Stacks Project, Morphisms of Spaces, Tag 05Z2, parts (1) and (2)
(blueprint: lem-sfb-space-uc-surjection-separation).

Absolute quasi-separatedness is written using the equivalent affine-pair test of
Properties of Spaces, Tag 0AHR. Absolute separatedness uses the scheme closed-immersion
form of the affine-pair test in lemma-characterize-separated of the same chapter.
The product in `prod.lift p.left q.left` is in `Scheme`, hence over Spec Z, even when
`S` is not separated. The fibre products over the algebraic space retain their
`S`-structure, and their canonical maps to the absolute scheme product are tested.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective universally closed map descends absolute quasi-separatedness and,
independently, absolute separatedness. Affine-pair tests express the absolute diagonals:
compactness of each fibre product for the first clause, and representability with its
map to the absolute scheme product a closed immersion for the second clause.
Source: Stacks, Morphisms of Spaces, Tag 05Z2(1),(2); Properties of Spaces, Tags 0AHR
and 0AHS (lemma-characterize-separated) (blueprint: lem-sfb-space-uc-surjection-separation).

Proof, following the six steps of the node:
1. Regard X and Y as spaces over Spec Z, using lem-sfb-space-change-base-to-integers.
   The same atlases give the same point topology (def-a1-space-point-topology).
   Any test over Y inherits its S-structure, so universal closedness is unchanged.
2. Put A = X x_Z X, C = Y x_Z Y. The map F = f x f factors as two base changes
   of f, hence is universally closed. The equality F Delta_X = Delta_Y f follows
   from the projections (lem-trf-space-fibre-products-etale-covers).
3. For T -> C put P = T x_C A, R = T x_C X, Q = T x_C Y. Then
   R = P x_A X = Q x_Y X. Thus R -> Q is a base change of f and is surjective
   on points (lem-a1-space-point-open-calculus), without representability of f.
4. If Delta_X is quasi-compact and T affine, P is quasi-compact by
   lem-sfb-space-universally-closed-quasicompact. Choose an affine surjective etale
   atlas U -> P (lem-sfb-qc-space-affine-etale-atlas). The source U x_A X is
   quasi-compact and maps continuously onto R and then Q. Pull back an open cover
   and choose a finite subcover. This proves quasi-compactness of Delta_Y.
5. If Delta_X is closed, it is universally closed by lem-sfb-space-closed-subspace-proper.
   Thus R -> T is universally closed. For a closed subset E of Q, its inverse image
   in R is closed; its image in T is closed and equals the image of E, by point
   surjectivity. This proves universal closedness of Delta_Y after every base change.
6. Every scheme test of Delta_Y is representable, locally of finite type and monic
   (lem-sfb-space-diagonal-scheme-tests). It is universally closed by step 5,
   quasi-compact by lem-weil-pbc-universally-closed-quasi-compact, and separated by
   lem-trf-scheme-monomorphism-separated. It is therefore proper, by
   def-weil-finite-type-morphism and def-weil-proper-morphism, and a closed immersion
   by lem-pc-proper-monomorphism-closed. The affine-pair characterizations translate
   these two diagonal conclusions into the displayed predicates. -/
theorem separation_of_surjective_universallyClosed
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y)
    (hsurj : Function.Surjective (mapPoint f.hom.hom))
    (hclosed : MapIsUniversallyClosed f) :
    ((∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
        (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
          CompactSpace (Point (Limits.pullback a b))) →
      ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y.obj.obj)
        (b : yoneda.obj V ⟶ Y.obj.obj), IsAffine U.left → IsAffine V.left →
          CompactSpace (Point (Limits.pullback a b))) ∧
    ((∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
        (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
          ∃ (W : Over S) (p : W ⟶ U) (q : W ⟶ V),
            IsPullback (yoneda.map p) (yoneda.map q) a b ∧
              IsClosedImmersion (prod.lift p.left q.left)) →
      ∀ (U V : Over S) (a : yoneda.obj U ⟶ Y.obj.obj)
        (b : yoneda.obj V ⟶ Y.obj.obj), IsAffine U.left → IsAffine V.left →
          ∃ (W : Over S) (p : W ⟶ U) (q : W ⟶ V),
            IsPullback (yoneda.map p) (yoneda.map q) a b ∧
              IsClosedImmersion (prod.lift p.left q.left)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
