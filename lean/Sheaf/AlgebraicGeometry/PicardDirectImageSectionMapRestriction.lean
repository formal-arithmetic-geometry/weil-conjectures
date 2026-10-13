/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap

import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Compatibility of the fixed section map with restriction

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-section-map-restriction)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The actual canonical section map commutes with successive base change.
It asserts an equality of maps and does not assert their bijectivity.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-section-map-restriction)

Proof: The two projection equations identify j with the cartesian comparison by
pullback hom-extensionality. Use the associativity law of
exists_derivedPullbackComposition on i, t and the fibre-product projections.
The definition of the base-change map is the transpose of the pulled-back counit
under the pinned derived adjunction. The unit and counit naturality laws therefore
identify the composite base-change mate with the mate for t'. The canonical
single pullback square transports the source structure-sheaf map through this
composition comparison. Apply H^0. canonicalDegreeZeroMateSquare identifies the
result with the ordinary pullback mate. The inverse mate of pushforward composition
has exactly the coefficient comparison c, by uniqueness of conjugate isomorphisms.
Evaluation of the ordinary adjunction at 1 gives its unit on the given section.
Naturality of the module morphisms lets restriction from j inverse-top to top pass
through the coefficient comparison, yielding the displayed formula. This calculation
uses no flatness, properness, invertibility, nonempty scheme or nonempty fibre. -/
theorem picardDirectImageSectionMap_restriction
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            (c.app L).inv.app ⊤
              (((Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).presheaf.map
                  (homOfLE j.preimage_top.ge).op
                    (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                      ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).val.app
                        (Opposite.op ⊤)
                          (picardDirectImageSectionMap f L W k t ξ))) =
              picardDirectImageSectionMap f L W k t'
                (picardDerivedModelRestriction E i t t' h ξ) := by sorry

end AlgebraicGeometry.Scheme
