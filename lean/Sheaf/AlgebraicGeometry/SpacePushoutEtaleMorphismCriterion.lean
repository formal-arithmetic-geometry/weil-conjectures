/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection

/-! # Etaleness of the morphism induced by an infinitesimal pushout triple

Source: Stacks Project, spaces-pushouts.tex, Tag 07W3,
lemma-equivalence-categories-spaces-pushout-flat, part (5), forward direction
(blueprint: lem-sfb-space-pushout-etale-morphism-criterion).

The overlap is the actual sheaf fibre product, and its identification is over `A`.
Both pushouts have algebraic-space targets. The conclusion constructs the unique map
with the prescribed restrictions and asserts its chartwise etaleness.

## Main statements

* `existsUnique_chartwiseEtale_affineThickeningPushout`: compatible etale components
  induce a chartwise etale morphism of pushouts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map from the pushout of a compatible etale triple to the base pushout is
chartwise etale. The thickening is a representable closed immersion and a homeomorphism
on the existing atlas-quotient point topologies; the other leg is representable affine.
The specified overlap isomorphism lies over `A`, as expressed by `hφ`.
No space over `Q` realizing the triple is supplied or assumed.
Source: Stacks Project, Tag 07W3 (5), forward direction, using Tags 07VX, 07W1,
07W2, 07RX (5), and 03FS
(blueprint: lem-sfb-space-pushout-etale-morphism-criterion).

Proof:
1. Choose a representable surjective etale scheme atlas C0 of C
   [def-trf-algebraic-space]. Its pullback A0 to A is a scheme because A -> C is
   affine, and A0 -> A is surjective etale by
   [lem-trf-space-representable-etale-scheme-tests]. Lift it across A -> A+ by
   [lem-sfb-space-thickening-etale-scheme-equivalence] to an etale scheme A0+ over A+.
   Both closed restrictions are thickenings by [lem-sfb-space-thickening-base-change],
   so their point homeomorphisms show A0+ -> A+ is surjective. Apply
   [lem-sfb-space-pushout-lifted-atlas] to obtain a scheme pushout Q0 and a
   representable surjective etale atlas Q0 -> Q.
2. Choose a scheme atlas X0 of X times_C C0, an algebraic space by
   [lem-trf-space-fibre-products-etale-covers]. Its composite to X is surjective
   etale by [lem-trf-space-representable-etale-scheme-tests]. The affine pullback
   U0 = X0 times_C A is a scheme. For H = Y times_A+ A0+, its closed restriction
   H0 is identified, using phi, with (X times_C C0) times_C A. Consequently
   U0 -> H0 is surjective etale. Lift it across the thickening H0 -> H by
   [lem-sfb-space-thickening-etale-scheme-equivalence]. The resulting scheme Y0
   is surjective etale over H by the point homeomorphisms, and hence over Y.
3. The two lifts identify Y0 times_A0+ A0 and Y0 times_Y U with U0.
   Thus [lem-sfb-space-pushout-lifted-atlas], applied to U -> X and U -> Y,
   gives a scheme pushout Z0 and a representable surjective etale atlas Z0 -> Z.
   Here U -> X is affine and U -> Y is a thickening by base change
   [lem-sfb-space-thickening-base-change]. The maps of the two pieces induce
   Z0 -> Q0. The universal property in [lem-sfb-space-affine-thickening-pushout]
   gives a unique p : Z -> Q, with the displayed restrictions, and shows that
   Z0 -> Q0 -> Q equals Z0 -> Z -> Q by comparing its restrictions.
4. By [lem-trf-space-chartwise-etale-permanence], X0 -> C0 and Y0 -> A0+ are
   chartwise etale. For scheme sources this is representable etaleness, hence
   ordinary scheme etaleness. Apply [lem-sfb-scheme-infinitesimal-etale-patching]
   to deduce that Z0 -> Q0 is etale. Composition with Q0 -> Q is representable
   etale by [lem-trf-space-representable-etale-scheme-tests]. Finally clause (3)
   of [lem-trf-space-etale-source-atlas-detection] makes p chartwise etale.
   Uniqueness follows from the pushout universal property, independently of etaleness.
   All lifts use arbitrary thickenings, without a finite nilpotence bound. -/
theorem existsUnique_chartwiseEtale_affineThickeningPushout {B : Scheme.{u}}
    (A A' C Q : AlgebraicSpace B) (i : A ⟶ A') (a : A ⟶ C)
    (j : C ⟶ Q) (b : A' ⟶ Q)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom))
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom)
    (hQ : IsPushout a i j b)
    (X Y : AlgebraicSpace B) (x : X ⟶ C) (y : Y ⟶ A')
    (hx : IsChartwiseEtale x) (hy : IsChartwiseEtale y)
    (φ : enlargedFibreProduct x a ≅ enlargedFibreProduct y i)
    (hφ : φ.hom.hom ≫ Limits.pullback.snd y.hom i.hom =
      Limits.pullback.snd x.hom a.hom)
    (Z : AlgebraicSpace B) (u : X ⟶ Z) (v : Y ⟶ Z)
    (hZ : IsPushout (enlargedFibreProductFst x a)
      (φ.hom ≫ enlargedFibreProductFst y i) u v) :
    ∃! p : Z ⟶ Q, u ≫ p = x ≫ j ∧ v ≫ p = y ≫ b ∧ IsChartwiseEtale p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
