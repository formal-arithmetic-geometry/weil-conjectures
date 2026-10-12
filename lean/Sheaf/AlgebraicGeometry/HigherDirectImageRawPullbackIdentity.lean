/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Identity of raw cohomology pullback

Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-identity).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The explicit raw pullback of an identity arrow is the identity on classes.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 015F (lemma-right-derived-exact-functor), exact derived inverse image.
(blueprint: lem-sbc-higher-image-raw-pullback-identity).

Proof: Let P be inverse image along the identity scheme map and e:P iso identity
its canonical unit comparison. Apply upperStarComp_id_left separately to A.hom
followed by k and to A.hom. The first factor of raw pullback becomes the single
functor applied to e.inv at the pulled-back free sheaf, and its coefficient factor
becomes the single functor applied to e.hom at A.hom-pullback of G.
Apply e termwise to cochain complexes. Compose its localized transformation with
the exact-derived-functor factorization comparison; fullness of precomposition by
localization gives a natural comparison from D(P) to the identity. Its shift
compatibility follows termwise, descends through localization by faithfulness,
and is preserved on restriction to the fully faithful bounded-below subcategory.
Its component on a single complex is precisely the single-functor comparison
followed by the single of e: in degree zero the component is e, in every other
degree it is the unique map to a zero object. Naturality for the class z and
shift compatibility therefore replace the last four factors in the raw formula
by single(e.hom) followed by z. The first single(e.inv) cancels single(e.hom),
leaving z. This applies in every integer degree, including negative q, and for
zero sheaves, zero classes and empty schemes, without a limit or finiteness
hypothesis. All comparisons are the fixed canonical constructions. -/
theorem higherDirectImageRawOverPullback_id
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A : Over W) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q (𝟙 A) U z = z := by sorry

end AlgebraicGeometry.Etale
