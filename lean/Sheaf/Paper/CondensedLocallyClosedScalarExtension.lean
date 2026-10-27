/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.Paper.CoefficientHeartFiltration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-! # Ordinary scalar extension and canonical locally closed extension

Source: blueprint integral-models-generators proof (1), rationalization of the extensions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

section MateIdentity


variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
  {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}

private theorem push_eq_mate_pull_inv (a : T ⊣ S) (b : T' ⊣ S')
    (c : l ⊣ r) (d : l' ⊣ r') (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (TwoSquare.equivNatTrans _ _ _ _).symm.injective
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

end MateIdentity

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriek

-- The closed-support mate argument also appears in QcqsLatticeTreeReconstruction.
private theorem closed_scalar_iso
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (h : Set.range j = (Set.range i)ᶜ)
    (B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj A Z)) :
    IsIso ((CondensedRing.pushHom a i).app B) := by
  have hiA := CondensedRing.moduleCounitOfAbelian A i
    (ProEtale.abelian_closed_support i j h).1
  have hiR := CondensedRing.moduleCounitOfAbelian R i
    (ProEtale.abelian_closed_support i j h).1
  let δ := (CondensedRing.pushHom a i).app B
  apply (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl R i j
    (by rw [h]; exact isCompl_compl)).isIso_of_pairFunctor δ
  · have hzA := CondensedRing.openRestrictionPushforwardZero A i j h B
    have hzR := CondensedRing.openRestrictionPushforwardZero R i j h
      ((Mod.extendScalars (coefficientMap a Z)).obj B)
    have hz := ((Mod.extendScalars (coefficientMap a U)).map_isZero hzA).of_iso
      ((CondensedRing.pullIso a j).app ((CondensedRing.lowerStar A i).obj B)).symm
    exact hz.isIso hzR _
  · have hd : CondensedRing.pushHom a i =
        (mateEquiv (CondensedRing.upperStarLowerStarAdjunction A i)
          (CondensedRing.upperStarLowerStarAdjunction R i)
          (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv)).natTrans := by
      simpa only [CondensedRing.pushHom, CondensedRing.pullIso] using
        (push_eq_mate_pull_inv
        (Mod.extendRestrictAdjunction (coefficientMap a Z))
        (Mod.extendRestrictAdjunction (coefficientMap a X))
        (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i) (CondensedRing.comapLowerStarIso a i))
    have he : (CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B) =
        (CondensedRing.pullIso a i).inv.app ((CondensedRing.lowerStar A i).obj B) ≫
          (Mod.extendScalars (coefficientMap a Z)).map
            ((CondensedRing.upperStarLowerStarAdjunction A i).counit.app B) := by
      change (CondensedRing.upperStar R i).map ((CondensedRing.pushHom a i).app B) ≫ _ = _
      rw [hd]
      exact mateEquiv_counit (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i)
        (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv) B
    have : IsIso ((CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right ((CondensedRing.upperStar R i).map δ)
      ((CondensedRing.upperStarLowerStarAdjunction R i).counit.app _)


/-- Ordinary change of condensed coefficients commutes with locally closed extension.
No flatness or lisseness is needed for this comparison.

Source: blueprint integral-models-generators proof (1), final scalar-extension identity;
Stacks Project, Tags 03DI, 03DJ and 09BM.
(blueprint: lem-sfb-condensed-locally-closed-scalar-extension).

Proof. For an open immersion use the scalar/open-extension adjunction comparison
`CondensedRing.openImmersionShriekIso`. For the closed factor, form the scalar/direct-image
comparison as the mate of the coefficient restriction square. Its restriction to the
closed subscheme is an isomorphism, since the closed counit and the scalar/pullback
comparison are isomorphisms. On the complementary open both modules vanish: closed
extension has zero restriction, scalar extension preserves zero, and scalar extension
commutes with pullback. Open/closed detection therefore makes this comparison invertible.
Apply this to the closed inclusion of the scheme-theoretic closure and compose with the
open comparison. This identifies the actual open-then-closed functors in the statement.
Zero modules and empty immersions are included by the same restriction argument. -/
theorem condensedLocallyClosedExtension_scalar
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)) :
    Nonempty ((coefficientHeartLocallyClosedExtension B a inferInstance).obj
      ((Mod.extendScalars ((upperStarFromPoint S).map c)).obj M) ≅
        (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
          ((coefficientHeartLocallyClosedExtension A a inferInstance).obj M)) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : IsOpenImmersion a.toImage := inferInstance
  let U : X.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range a.imageι)ᶜ := U.range_ι
  have := closed_scalar_iso c U.ι a.imageι hU
    ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M)
  unfold coefficientHeartLocallyClosedExtension
  change Nonempty
    ((CondensedRing.lowerStar B a.imageι).obj
        ((CondensedRing.openImmersionLowerShriek B a.toImage).obj
          ((Mod.extendScalars ((upperStarFromPoint S).map c)).obj M)) ≅
      (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
        ((CondensedRing.lowerStar A a.imageι).obj
          ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M)))
  exact ⟨((CondensedRing.lowerStar B a.imageι).mapIso
      ((CondensedRing.openImmersionShriekIso c a.toImage).symm.app M)) ≪≫
    (asIso ((CondensedRing.pushHom c a.imageι).app
      ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M))).symm⟩

end AlgebraicGeometry.ProEtale
