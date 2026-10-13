/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare
import Sheaf.AlgebraicGeometry.PullbackStructureUnitSquare

/-! # Successive base change before fibre-unit normalization

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-derived-transpose-pasting)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The derived adjoint of a test morphism respects successive base change.
The source is a twice-derived pullback of O_T[0], not a module on the fibre.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-derived-transpose-pasting)

Proof: The projection equations identify j as the unique map between the two
fibre products. Their comparison maps a and a' to X_W satisfy j followed by a
 equal to a', by pullback.hom_ext. Expand both base-change maps as the pinned
 derived-adjunction transposes of the pulled-back counit. Transpose the entire
 equality under the adjunction for the new fibre projection. Naturality moves
 the adjunction unit through the coefficient maps; its composite with the
 counit cancels by the triangle identity. The remaining derived composition
 comparisons agree by the associativity clause of exists_derivedPullbackComposition,
 transported along i followed by t equal to t'. Their coefficient counits agree
 with the composite tensor comparison by their left-derived factorization;
 canonicalSinglePullbackSquare expresses this on N[0]. Thus the coefficient
 comparison is the ordinary-to-tensor left-adjoint comparison followed by the
 inverse conjugate of pushforward composition. On the source, expand the
 conjugation defining picardDerivedModelRestriction. Composition coherence and
 canonicalSinglePullbackSquare for O_W identify its normalization with the
 single-pullback comparison for i followed by pullbackObjUnitToUnit i. This
 gives the displayed equality, before applying any fibre-unit identification
 or taking H^0. Only structure-sheaf comparisons are inverted, so the assertion
 includes zero modules, identities and empty schemes without extra conditions. -/
theorem picardDirectImageDerivedTranspose_pasting
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t')
    (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k))
    (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k))
    (hj₂ : j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i)
    (ξ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) t) :
    let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
    let U := SheafOfModules.unit (moduleRings T.toRingedSpace)
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj U
    let p := pullback.snd f (t ≫ k)
    let p' := pullback.snd f (t' ≫ k)
    let D := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) p' i).hom.app A ≫
      eqToHom (congrArg (fun q ↦ (derivedPullback q).obj A) hj₂.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) j p).inv.app A
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t ≫ k)))).comp
          (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
      (Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t' ≫ k))))).symm
      (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
        Modules.pushforwardCongr hj₁)
    let d := ((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction j)).symm.app N ≪≫ (c.app L).symm
    D ≫ (derivedPullback j).map (picardDirectImageDerivedTranspose f L W k t ξ) ≫
        Modules.canonicalSinglePullbackMap j N ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0).map
            d.hom =
      (derivedPullback p').map
        (Modules.canonicalSinglePullbackMap i U ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).map
              (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)) ≫
        picardDirectImageDerivedTranspose f L W k t'
          (picardDerivedModelRestriction _ i t t' h ξ) := by sorry

end
end AlgebraicGeometry.Scheme
