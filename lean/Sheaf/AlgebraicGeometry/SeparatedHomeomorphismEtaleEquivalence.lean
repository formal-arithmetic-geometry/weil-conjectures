/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.UniversallyHomeomorphIntegral
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Étale spaces under separated universal homeomorphisms

Source: Rydh, Submersions and effective descent of étale morphisms, Theorem (5.21),
printed p.24; quasi-separated convention on printed p.4
(blueprint: lem-sfb-homeomorphism-separated-etale-equivalence).

The two full subcategories are indexed by a Boolean: `false` gives all quasi-separated
chartwise étale objects, and `true` gives their separated full subcategory. The natural
isomorphism identifies the forward equivalence, on objects and arrows, with actual sheaf
base change. Thus the equivalences are induced by pullback along the given morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullback along a separated universal homeomorphism is an equivalence on chartwise
étale quasi-separated algebraic spaces, and on their separated full subcategories.
Source: Rydh, Theorem (5.21), printed p.24, including the `E_sep` restriction
(blueprint: lem-sfb-homeomorphism-separated-etale-equivalence).

Proof:
1. Every base change of `r` is open and surjective on points. Apply
   lem-sfb-space-open-surjection-etale-descent to obtain effective étale descent.
2. The first projection of `X ×_Y X` is a homeomorphism on points. Its section `Δ_r`
   therefore also is one, and separatedness makes that section a closed immersion,
   hence a thickening. By lem-sfb-space-thickening-base-change this persists under base
   change. Scheme tests are integral, universally injective and surjective by
   lem-trf-universally-homeomorph-integral. Apply
   lem-sfb-space-integral-radicial-etale-invariance: pullback by the diagonal and all its
   base changes is fully faithful. Fibre products and point maps use
   lem-trf-space-fibre-products-etale-covers and lem-a1-space-point-open-calculus.
3. By lem-trf-space-chartwise-etale-permanence both projections pull an étale object back
   to étale objects. Their restrictions to the diagonal agree. Full faithfulness uniquely
   lifts the identity to the overlap isomorphism, whose reverse is obtained the same way.
   On the triple overlap pull back along `(x,z) ↦ (x,x,z)`, a base change of the diagonal.
   Faithfulness proves the cocycle identity, since its restriction is the identity
   followed by the overlap isomorphism. Faithfulness along the diagonal gives uniqueness.
4. Every morphism respects these data: both proposed composites restrict to that same
   morphism on the diagonal. Thus forgetting descent data is an equivalence. Compose
   this with step 1 to obtain the first pullback equivalence.
5. Separatedness is preserved by lem-weil-pbc-closed-immersion-base-change. To reflect it,
   test the relative diagonal on an arbitrary space and pull this test back along `r`.
   The resulting map is a closed immersion, hence universally closed by
   lem-sfb-space-closed-subspace-proper. The vertical point maps are homeomorphisms, so
   conjugation makes the original test closed. By lem-sfb-space-separated-diagonal-closed
   the original object is separated. Restrict the equivalence to these full subcategories.
   Its essential surjectivity gives the last assertion. -/
theorem separatedHomeomorphism_etale_equivalence
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (r : X ⟶ Y)
    (hX : IsAbsolutelyQuasiSeparated X) (hY : IsAbsolutelyQuasiSeparated Y)
    (hsep : MapIsSeparated r)
    (hr : ∀ (T : AlgebraicSpace S) (g : T ⟶ Y),
      IsHomeomorph (mapPoint (Limits.pullback.snd r.hom g.hom).hom)) :
    (∀ separated : Bool,
      ∃ e : ObjectProperty.FullSubcategory
          (fun E : Over Y ↦ IsChartwiseEtale E.hom ∧
            IsAbsolutelyQuasiSeparated E.left ∧ (separated = true → MapIsSeparated E.hom)) ≌
        ObjectProperty.FullSubcategory
          (fun E : Over X ↦ IsChartwiseEtale E.hom ∧
            IsAbsolutelyQuasiSeparated E.left ∧ (separated = true → MapIsSeparated E.hom)),
        Nonempty (e.functor ⋙ ObjectProperty.ι _ ⋙
            Over.post (ObjectProperty.ι (IsAlgebraicSpace (S := S))) ≅
          ObjectProperty.ι _ ⋙ Over.post (ObjectProperty.ι (IsAlgebraicSpace (S := S))) ⋙
            Over.pullback r.hom)) ∧
    (∀ E : Over X, IsChartwiseEtale E.hom → IsAbsolutelyQuasiSeparated E.left →
      MapIsSeparated E.hom → ∃ F : Over Y,
        IsChartwiseEtale F.hom ∧ IsAbsolutelyQuasiSeparated F.left ∧ MapIsSeparated F.hom ∧
          Nonempty (Over.mk E.hom.hom ≅
            (Over.pullback r.hom).obj (Over.mk F.hom.hom))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
