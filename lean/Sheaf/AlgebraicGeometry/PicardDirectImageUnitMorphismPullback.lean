/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphism
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Pullback compatibility before evaluation of the canonical unit morphism

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-unit-morphism-pullback)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Pullback compatibility of the underlying module morphisms, before evaluating
on sections. No evaluation at 1 or restriction of sections is asserted here.
Source: Stacks Project, Tags 08HY and 0D5S; the morphism calculation in
lem-sc-picard-direct-image-section-map-restriction.
(blueprint: lem-sc-picard-direct-image-unit-morphism-pullback)

Proof: The projection equations identify j with the fibre-product comparison.
Expand the unit morphism as the ordinary adjoint transpose of its degree-zero
morphism. Expand the derived restriction as conjugation by derived composition.
Associativity of exists_derivedPullbackComposition identifies the two paths from
Lfibre^* Lt^* to the pullback for t'. Expand the base-change maps as transposes of
the pulled-back counit. The triangle identities and naturality of the derived
adjunction cancel the intervening unit and counit; thus successive base change
is the mate of the composite square. Apply canonicalSinglePullbackSquare to the
structure-sheaf comparison to transport its source through this equality. Apply
H^0 and canonicalDegreeZeroMateSquare to identify the resulting mate with the
ordinary one. Naturality of the degree-zero direct-image comparison transports
the coefficient morphism through H^0. Transpose by the ordinary adjunction on the
fibre product. Uniqueness of the left-adjoint comparisons identifies the tensor
coefficient map with c.inv and the source comparison with leftAdjointUniq followed
by pullbackObjUnitToUnit, giving the displayed module morphism equality. This
uses no invertibility of L or base-change map, nor any flatness, properness or
nonempty-space condition; identity maps, zero modules and empty schemes are covered. -/
theorem picardDirectImageUnitMorphism_pullback
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
            let U := SheafOfModules.unit
              (moduleRings (pullback f (t ≫ k)).toRingedSpace)
            let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
            (adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction j)).hom.app U ≫
                SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom ≫
                picardDirectImageUnitMorphism f L W k t'
                  (picardDerivedModelRestriction E i t t' h ξ) =
              (Modules.tensorPullback j).map
                (picardDirectImageUnitMorphism f L W k t ξ) ≫ (c.app L).inv := by sorry

end AlgebraicGeometry.Scheme
