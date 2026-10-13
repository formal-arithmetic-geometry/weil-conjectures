/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Restriction of canonical rectangle comparisons -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Canonical ordinary rectangle comparisons on the quasi-coherent subcategories.
Source: Stacks Project, Tags 0D5S (pullback composition), 0ATM (pasting), and
08HY (adjunctions defining the mate).
(blueprint: lem-sc-rectangle-qcoh-comparison-lifts)

Proof: The two projection equations identify k with pullbackLeftPullbackSndIso.hom,
by the uniqueness clause for the outer pullback. Pullback along k is an equivalence:
its inverse is pullback along the inverse scheme isomorphism, with unit and counit
obtained from the pinned composition and identity comparisons. Consequently the
unit of the pinned adjunction for k is invertible. Conjugate c(k,q) followed by the
transport along hk₂ under the pinned adjunctions for q, k, and the iterated second
projection; this is d. Whisker d with pullback along k and cancel the invertible
unit to obtain an ambient isomorphism from that pullback followed by the iterated
direct image to the outer direct image. Its inverse component is exactly the
first displayed formula. Both end functors preserve quasi-coherent objects, so
full faithfulness of the QCoh inclusion lifts this isomorphism uniquely to p.
Likewise lift c(h,g).symm to b. Faithfulness gives the second component formula.
No base-change map is assumed invertible here. Empty schemes and identity maps
satisfy the same universal-property and adjunction calculations. -/
theorem rectangle_qcoh_comparison_lifts
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
    let a := fun {A B : Scheme} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a (pullback.snd (pullback.snd f g) h))
      ((a (pullback.snd f (h ≫ g))).comp (a k))
      (c k (pullback.snd f (h ≫ g)) ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hk₂))
    ∃ (p : L ⋙ Q ≅ P) (b : B ≅ H),
      (∀ D : schemeDerivedQCohCategory (pullback f (h ≫ g)),
        (schemeDerivedQCohProperty T).ι.map (p.inv.app D) =
          (schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
            ((a k).unit.app D.obj) ≫ d.inv.app ((derivedPullback k).obj D.obj)) ∧
      (∀ D : schemeDerivedQCohCategory Y,
        (schemeDerivedQCohProperty T).ι.map (b.hom.app D) = (c h g).inv.app D.obj) := by sorry

end AlgebraicGeometry
