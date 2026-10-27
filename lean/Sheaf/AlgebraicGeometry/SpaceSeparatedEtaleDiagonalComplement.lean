/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Clopen diagonal and degree-one criterion for étale maps of algebraic spaces

Source: Stacks Project, Spaces, Morphisms, Tags 05W1(1), 03HK(1),(3), 05W5 and 040X;
Properties of Spaces, Tags 03BX and 03BZ; Morphisms, Tag 02G7
(blueprint: lem-sfb-space-separated-etale-diagonal-complement).

All diagonals and geometric fibres are sheaf fibre products, written on their underlying
presheaves. The complement is an algebraic space with an open and closed inclusion, whose
point image is exactly the complement of the diagonal's point image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated representable étale map has an open and closed diagonal and an open and
closed complementary subspace. If it is surjective on point classes and each geometric
fibre has exactly one point, it is an isomorphism.
Source: Stacks, Tags 05W1(1), 03HK, 05W5, 040X, 03BX, 03BZ and 02G7
(blueprint: lem-sfb-space-separated-etale-diagonal-complement).

Proof, following the six steps of the node:
1. The diagonal is representable and monic by lem-sfb-space-diagonal-scheme-tests.
   Representable étale composition (lem-trf-space-representable-etale-scheme-tests)
   makes the map chartwise étale. Base change, composition and comparison in
   lem-trf-space-chartwise-etale-permanence make its diagonal chartwise étale.
   Apply lem-sfb-space-etale-monomorphism-open. Separatedness gives closedness.
2. By lem-a1-space-point-open-calculus, the diagonal's open image pulls back on every
   atlas to a clopen scheme subscheme. The atlas topology therefore makes this image
   clopen. The open-subspace correspondence in lem-a1-space-etale-open-image supplies
   its complement. On scheme tests the complementary open subscheme is also closed,
   with surjective stalk maps, so its inclusion is a closed immersion.
3. Each geometric fibre is represented by an étale scheme over an algebraically closed
   field. By lem-trf-unramified-field-fibre-decomposition it is a disjoint union of
   finite separable field spectra. Algebraic closedness makes every summand the base
   field spectrum. Exactly one point gives one summand and a unique section.
4. Extend a field representative of a point of the self-product to an algebraic
   closure. Its two projections are sections of the same geometric fibre, so agree
   by step 3. The representative thus lies in the diagonal after extension, which
   preserves its point class (def-a1-algebraic-space-point-classes).
5. The diagonal's open image has all points. The full-image clause of
   lem-a1-space-point-open-calculus makes it the whole self-product. The diagonal is
   an isomorphism; the original map is therefore monic on every scheme test.
6. Apply lem-sfb-space-etale-monomorphism-open to the original map. Its open image has
   all points by the surjectivity hypothesis, so the same full-image clause makes
   it the whole target, proving that the original map is an isomorphism. -/
theorem separated_etale_diagonal_clopen_and_isIso {S : Scheme.{u}}
    (U X : AlgebraicSpace S) (a : U ⟶ X)
    (hsep : IsSeparatedPresheafMap a.hom.hom) (het : IsEtale a.hom.hom) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
      (diagonalPresheafMap a.hom.hom) ∧
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (diagonalPresheafMap a.hom.hom) ∧
    (∃ (C : AlgebraicSpace S)
      (j : C.obj.obj ⟶ Limits.pullback a.hom.hom a.hom.hom),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j ∧
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) j ∧
      pointImage j = (pointImage (diagonalPresheafMap a.hom.hom))ᶜ) ∧
    (pointImage a.hom.hom = Set.univ →
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (CommRingCat.of Ω) ⟶ S)
        (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
        ∃ p : Point (Limits.pullback a.hom.hom x), ∀ q, q = p) →
      IsIso a) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
