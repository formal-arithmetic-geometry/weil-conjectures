/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Étale transfer of universal first-order thickenings

Source: Stacks Project, More on Morphisms of Spaces, Tags 0601 and 0605
(blueprint: lem-sfb-space-universal-thickening-etale-transfer).

The universal property uses all algebraic-space tests, over the specified target `X`.
First-order thickenings use the existing representable scheme-test predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A universal first-order thickening over `X`, with its actual structure maps.
Source: Stacks, Tag 0601, equation-universal-first-order-thickening
(blueprint: lem-sfb-space-universal-thickening-etale-transfer). -/
def IsUniversalSpaceFirstOrderThickening {S : Scheme.{u}}
    {A A' X : AlgebraicSpace S} (f : A ⟶ X) (i : A ⟶ A') (f' : A' ⟶ X) : Prop :=
  IsSpaceFirstOrderThickening i ∧ i ≫ f' = f ∧
    ∀ (T T' : AlgebraicSpace S) (j : T ⟶ T') (b : T' ⟶ X),
      IsSpaceFirstOrderThickening j → ∀ (a : T ⟶ A), a ≫ f = j ≫ b →
        ∃! a' : T' ⟶ A', j ≫ a' = a ≫ i ∧ a' ≫ f' = b

/-- Étale lifting through a universal thickening, unique over the target with fixed reduction.
Source: Stacks, Tag 0605(1), lemma-etale-morphism-of-universal-thickenings
(blueprint: lem-sfb-space-universal-thickening-etale-transfer).

Proof (node steps 1--4): A first-order immersion remains first order after base change,
since its ideal is the image of the pulled-back square-zero ideal
[lem-sfb-space-ideal-closed-subspace-correspondence]. On scheme tests it is a surjective
closed immersion, hence integral and universally injective
[lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism]; its base changes are
homeomorphisms [lem-sfb-space-thickening-base-change]. Apply topological invariance
[lem-sfb-space-integral-radicial-etale-invariance] to lift the étale object; full
faithfulness gives the unique isomorphism fixing its reduction. The lift is representable:
on a scheme test, lift the reduced étale scheme by [sbc-lem-thickening-etale-site], and
use full faithfulness again to identify that scheme with the space lift. Étaleness is
preserved by [lem-trf-space-chartwise-etale-permanence]. The reduction is cartesian and
therefore first order. For a test thickening and map to Z, first extend its composite
to Y uniquely into Y'. Then lift uniquely into Z' by representable étale infinitesimal
lifting [lem-weil-pbc-flat-unramified-formally-etale]. This affine lifting applies to
space tests by taking affine étale charts, comparing on affine charts of overlaps,
and gluing in the fppf sheaf [def-trf-algebraic-space]. Uniqueness follows first in Y'
and then along the étale map. No formal-unramifiedness assumption is used. -/
theorem universalSpaceFirstOrderThickening_etale_lift {S : Scheme.{u}}
    {Z Y X Y' : AlgebraicSpace S} (p : Z ⟶ Y) (f : Y ⟶ X)
    (j : Y ⟶ Y') (f' : Y' ⟶ X) (hp : IsEtale p.hom.hom)
    (hY : IsUniversalSpaceFirstOrderThickening f j f') :
    ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (q : Z' ⟶ Y'),
      IsEtale q.hom.hom ∧ IsPullback p i j q ∧
      IsUniversalSpaceFirstOrderThickening (p ≫ f) i (q ≫ f') ∧
      ∀ (Z'' : AlgebraicSpace S) (i' : Z ⟶ Z'') (q' : Z'' ⟶ Y'),
        IsEtale q'.hom.hom → IsPullback p i' j q' →
          ∃! e : Z' ≅ Z'', i ≫ e.hom = i' ∧ e.hom ≫ q' = q := by
  sorry

/-- The canonical extension from any universal thickening is étale and cartesian.
Source: Stacks, Tags 0601 and 0605(1)
(blueprint: lem-sfb-space-universal-thickening-etale-transfer).

Proof (node step 5): Obtain Z' from the étale lift theorem (steps 1--4). Universality
of Z' and W gives maps in both directions extending the identity of Z. Each composite
extends the identity, so uniqueness makes them inverse. The resulting isomorphism
W ≅ Z' identifies the unique extension of p with the composite W → Z' → Y'. The
extension is unique by universality of Y'. It is étale and its reduction square is
cartesian because these facts hold for Z' and are preserved under isomorphisms. -/
theorem universalSpaceFirstOrderThickening_etale_canonical {S : Scheme.{u}}
    {Z Y X Y' W : AlgebraicSpace S} (p : Z ⟶ Y) (f : Y ⟶ X)
    (j : Y ⟶ Y') (f' : Y' ⟶ X) (k : Z ⟶ W) (w : W ⟶ X)
    (hp : IsEtale p.hom.hom) (hY : IsUniversalSpaceFirstOrderThickening f j f')
    (hW : IsUniversalSpaceFirstOrderThickening (p ≫ f) k w) :
    (∃! q : W ⟶ Y', k ≫ q = p ≫ j ∧ q ≫ f' = w) ∧
      ∀ q : W ⟶ Y', k ≫ q = p ≫ j → q ≫ f' = w →
        IsEtale q.hom.hom ∧ IsPullback p k j q := by
  sorry

/-- Universality descends through a surjective étale cartesian map of thickenings.
Source: Stacks, Tag 0605(2), lemma-etale-morphism-of-universal-thickenings
(blueprint: lem-sfb-space-universal-thickening-etale-transfer).

Proof (node steps 6--8): The upper étale map is surjective since the reductions are
homeomorphisms (step 1) and p is surjective. Given T ⊂ T' and a : T → Y, pull p back
to the surjective étale cover U = T ×_Y Z of T
[lem-trf-space-fibre-products-etale-covers]. Lift it to a surjective representable
étale cover U' of T' by the construction of step 3, using
[lem-sfb-space-integral-radicial-etale-invariance] and [sbc-lem-thickening-etale-site].
Universality of Z' extends U → Z uniquely to e : U' → Z'. First prove uniqueness of
extensions to Y': two such extensions lift along q on U ⊂ U' by the space-test
étale lifting of step 2 [lem-weil-pbc-flat-unramified-formally-etale]. Both lifts
extend the same map U → Z, hence agree by universality of Z'. Their composites
agree, and the surjective cover gives equality on T'. Now on U' ×_{T'} U', the two
composites q e have the same reduction into Y. Apply the uniqueness just proved
to this first-order overlap test to equate the composites. They descend through
the fppf sheaf equalizer to an X-map T' → Y'. Its reduction is a, checked on the
cover, and uniqueness was proved already. The two overlap maps into Z need not agree;
only their composites into Y agree. This corrects the source's overlap argument. -/
theorem universalSpaceFirstOrderThickening_etale_descent {S : Scheme.{u}}
    {Z Y X Z' Y' : AlgebraicSpace S} (p : Z ⟶ Y) (f : Y ⟶ X)
    (i : Z ⟶ Z') (j : Y ⟶ Y') (q : Z' ⟶ Y') (f' : Y' ⟶ X)
    (hp : IsEtale p.hom.hom) (hs : IsSurjective p.hom.hom)
    (hq : IsEtale q.hom.hom) (hj : IsSpaceFirstOrderThickening j)
    (hcomm : j ≫ f' = f) (hcart : IsPullback p i j q)
    (hZ : IsUniversalSpaceFirstOrderThickening (p ≫ f) i (q ≫ f')) :
    IsUniversalSpaceFirstOrderThickening f j f' := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
