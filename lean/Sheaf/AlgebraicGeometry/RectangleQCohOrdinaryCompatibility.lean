/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
import Sheaf.AlgebraicGeometry.DerivedBaseChangePasting
import Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting

/-! # Ordinary compatibility of the rectangle comparison lifts -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Ordinary base-change compatibility for the canonical comparison lifts.
Source: Stacks Project, Tag 0ATM, and Tag 08HY.
(blueprint: lem-sc-rectangle-qcoh-ordinary-compatibility)

Proof: Apply the faithful QCoh inclusion to the desired equality. Substitute the
component formulas for p.inv and b.hom, and the given formula for s.hom. The
upper-precomposition pasting law schemeDerivedBaseChange_pasting, transported
along hk₁ and hk₂, identifies the outer base-change map followed by the unit for
k and d.inv with the ordinary map for the pulled-back rectangle. To check this
transport, eliminate the two equalities, commute d.inv past the inverse upper
pullback comparison by naturality, and cancel d.hom/d.inv and the pullback
comparison/inverse. The horizontal law schemeDerivedBaseChange_horizontal_pasting
then identifies the successive inner and outer base-change maps with this
rectangle map conjugated by c(h,g) and c(t,p). The latter comparison cancels the
inverse present in s, giving the displayed equality. Reflect this equality through
the faithful inclusion. No ordinary base-change invertibility is used: the result
is the ordinary pasting step prior to inversion. The argument applies to zero
objects, empty schemes, and identity arrows without extra assumptions. -/
theorem rectangle_qcoh_ordinary_compatibility
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    let P := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g))
    let Q := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h)
    let B := qcPullback (h ≫ g)
    let H := qcPullback g ⋙ qcPullback h
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme.{u}} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a (pullback.snd (pullback.snd f g) h))
      ((a (pullback.snd f (h ≫ g))).comp (a k))
      (c k (pullback.snd f (h ≫ g)) ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hk₂))
    ∀ (s : U ⋙ L ≅ V) (hL : L.IsEquivalence) (hs : ∀ E : schemeDerivedQCohCategory X,
      (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map (s.hom.app E) =
        (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))
         (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
           eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
           (comp (pullback.fst (pullback.snd f g) h)
             (pullback.fst f g)).inv.app E.obj)),
    ∀ (p : L ⋙ Q ≅ P) (b : B ≅ H),
      (∀ D : schemeDerivedQCohCategory (pullback f (h ≫ g)),
        (schemeDerivedQCohProperty T).ι.map (p.inv.app D) =
          (schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
            ((a k).unit.app D.obj) ≫ d.inv.app ((derivedPullback k).obj D.obj)) →
      (∀ D : schemeDerivedQCohCategory Y,
        (schemeDerivedQCohProperty T).ι.map (b.hom.app D) = (c h g).inv.app D.obj) →
      ∀ E : schemeDerivedQCohCategory X,
        (qcBaseChange f (h ≫ g)).app E ≫ p.inv.app (U.obj E) ≫ Q.map (s.hom.app E) =
          b.hom.app ((qcDirectImage f).obj E) ≫
            (qcPullback h).map ((qcBaseChange f g).app E) ≫
            (@qcBaseChange _ (pullback f g) S T _
              (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
              (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
 := by sorry

end AlgebraicGeometry
