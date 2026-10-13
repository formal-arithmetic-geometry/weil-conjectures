/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition

/-! # Identity of varying-coefficient raw pullback

Source: Stacks Project, Tags 09Z1 and 03CB.
(blueprint: lem-sbc-abelian-raw-pullback-identity).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw pullback along an identity scheme map, with its canonical coefficient map,
is the identity on each derived-Hom group. The equality `ha` permits functor-map transports.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03CB, identity of inverse
images. (blueprint: lem-sbc-abelian-raw-pullback-identity).

Proof: Substitute ha, so a is the identity, and convert hφ to equality of morphisms.
The left unit law upperStarComp_id_left identifies the first raw factor with the single
functor applied to upperStarId.inv at h-pullback of the free sheaf of U. Let eD be the
canonical derived identity comparison upperStarIdDerivedPlus. On a single complex its
component is the single-functor comparison followed by single(upperStarId.hom): compute
on the complex concentrated in degree zero, where both maps are upperStarId.hom; in all
other degrees they are the unique map between zero objects. Apply the factorization
comparison and localization to obtain this equality in the derived category, then restrict
to D⁺ using the fully faithful inclusion. The same termwise computation shows that eD
commutes with shifts. Consequently the last three factors of the raw formula are
D(id^*).map z followed by eD.hom at the shifted single of F. Naturality of eD changes
this to eD.hom at the source single followed by z. The inverse single comparison cancels
its direct comparison. What remains is single(upperStarId.inv) followed by
single(upperStarId.hom) followed by z; functoriality and the inverse-hom identity give z.
This proof applies also for zero F, zero z, empty schemes and p = 0. -/
theorem abelianHigherDirectImageRawPullback_identity {S Y : Scheme.{v}}
    (a : Y ⟶ Y) (ha : a = 𝟙 Y) (h : Y ⟶ S) (w : a ≫ h = h) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F)
    (hφ : HEq φ ((upperStarId AddCommGrpCat.{v + 1} Y).hom.app F))
    (U : S.Etale) (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    abelianHigherDirectImageRawPullback a h h w p F F φ U z = z := by sorry

end AlgebraicGeometry.Etale
