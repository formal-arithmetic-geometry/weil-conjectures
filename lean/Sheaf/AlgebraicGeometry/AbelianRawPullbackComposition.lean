/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition

/-! # Composition of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 09Z1 and 03CB.
(blueprint: lem-sbc-abelian-raw-pullback-composition).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Two varying-coefficient raw pullbacks compose on each derived-Hom group.
The composite scheme map and coefficient map may be given with canonical transports.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03CB, composition of
inverse images. (blueprint: lem-sbc-abelian-raw-pullback-composition).

Proof: Substitute hd so d is b ≫ a, and convert hφ to equality of morphisms. Expand the
five factors of each raw pullback. Functor.map_comp distributes D(b^*) over the inner
five factors. Naturality of the single-functor comparison for b^* at the source comparison
moves that comparison to the left of the inverse single comparison. The adjacent direct
and inverse single comparisons at the intermediate source then cancel. Use naturality of
the derived composition isomorphism D((b ≫ a)^*) ≅ D(a^*) ⋙ D(b^*) at z to replace the
twice pulled-back class by the class pulled back along b ≫ a. The source factors agree
with the source factor for d by upperStarComp associativity applied to b, a, h. On single
complexes the derived composition agrees with the underived comparison by
abelianPullbackSingleComposition (specialized to b, a, b ≫ a, rfl), so its source component
moves across the single comparisons. Its shift compatibility, proved on complexes and
descended through localization, moves the target component through the two commShiftIso
factors. Naturality of the single comparison at φa moves φa past the intermediate
comparison; functoriality of single and shift combines the coefficient factors as
single(upperStarComp.hom ≫ b^*.map φa ≫ φb). This is single(φd) by hφ. Use wa, wb, wd
and associativity to identify the structure-map equalities (their proof transports are
proof-irrelevant). The five remaining factors are exactly the raw formula for d.
No invertibility of any coefficient morphism is used; zero coefficients, empty schemes,
identity maps and p = 0 obey the same calculation. -/
theorem abelianHigherDirectImageRawPullback_composition {S Y Y' Y'' : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (d : Y'' ⟶ Y) (hd : d = b ≫ a)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (wd : d ≫ h = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F'' : Sheaf Y''.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φa : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (φb : ((b)^*[AddCommGrpCat.{v + 1}]).obj F' ⟶ F'')
    (φd : ((d)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F'')
    (hφ : HEq φd ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F ≫
      ((b)^*[AddCommGrpCat.{v + 1}]).map φa ≫ φb))
    (U : S.Etale) (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    abelianHigherDirectImageRawPullback d h h'' wd p F F'' φd U z =
      abelianHigherDirectImageRawPullback b h' h'' wb p F' F'' φb U
        (abelianHigherDirectImageRawPullback a h h' wa p F F' φa U z) := by sorry

end AlgebraicGeometry.Etale
