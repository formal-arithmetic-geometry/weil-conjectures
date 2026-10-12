/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.AlgebraicGeometry.Curve.GenericDirectImageCounit
import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Sheaf.AlgebraicGeometry.NormalGenericConstant

/-! One prime-constant step of generic filtration. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.IsConnectedCurve

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_constant_generic_unit
    {k : Type u} [Field k] {D : Scheme.{u}}
    (g : D ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g] [IsIntegral D]
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).unit.app
        ((constantSheaf D.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) := by
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian D := {}
  have hn : IsNormalScheme D := ⟨inferInstance, fun x ↦
    ⟨inferInstance, isIntegrallyClosed_stalk_of_smooth g (IsCurve.krullDim_le_one (f := g)) x⟩⟩
  let F := (constantSheaf D.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  have hc := Etale.isIso_constantSheaf_to_generic_lowerStar D hn M
  have hu : IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (D.fromSpecResidueField (genericPoint D))).unit.app F) :=
    IsIso.of_isIso_comp_right _
      ((Etale.lowerStar AddCommGrpCat.{u + 1}
        (D.fromSpecResidueField (genericPoint D))).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (D.fromSpecResidueField (genericPoint D))).app M).hom)
  let : Field (D.presheaf.stalk (genericPoint D)) :=
    inferInstanceAs (Field D.functionField)
  have : IsIso (D.residue (genericPoint D)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ⟨(D.residue (genericPoint D)).hom.injective, IsLocalRing.residue_surjective⟩
  let r := Spec.map (D.residue (genericPoint D))
  have : IsIso r := inferInstance
  have hru : IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (r ≫ D.fromSpecFunctionField)).unit.app F) := hu
  have he := Etale.upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} r
    D.fromSpecFunctionField F
  have hh : IsIso (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).comp
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r)).unit.app F) := by
    have : IsIso (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField).comp
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r)).unit.app F ≫
        (Etale.lowerStarComp AddCommGrpCat.{u + 1} r D.fromSpecFunctionField
          (r ≫ D.fromSpecFunctionField) rfl).hom.app
          ((Etale.upperStar AddCommGrpCat.{u + 1} r).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj F))) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((Etale.lowerStarComp AddCommGrpCat.{u + 1} r D.fromSpecFunctionField
          (r ≫ D.fromSpecFunctionField) rfl).hom.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} r).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj F)))
  rw [Adjunction.comp_unit_app] at hh
  exact IsIso.of_isIso_comp_right _
    ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r).unit.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj F)))

set_option backward.isDefEq.respectTransparency false in
private theorem genericVanishing_of_isZero_upperStar
    (D : Scheme.{u}) [IsIntegral D] [QuasiSeparatedSpace D]
    (G : Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hz : IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj G))
    (V : D.Etale) (s : G.obj.obj (Opposite.op V)) :
    D.genericVanishingSieve G s ∈ D.smallEtaleTopology V := by
  let ε := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    D.fromSpecFunctionField).unit.app G
  have hε : ε = 0 := (Functor.map_isZero
    (Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField) hz).eq_of_tgt _ _
  refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W a hW ↦ ?_
  let x := G.obj.map a.op s
  let U₀ : D.NonemptyAffineOpens := Classical.arbitrary _
  let τ := Etale.unitComparison (D.functionFieldCone.π.app U₀)
    (D.affineOpensDiagramι.app U₀) D.fromSpecFunctionField
    (D.fromSpecFunctionField_eq_functionFieldCone_comp U₀) G
  have hx : τ.hom.app (Opposite.op W)
      ((D.affineOpenUnit U₀ G).hom.app (Opposite.op W) x) = 0 := by
    change ((D.affineOpenUnit U₀ G ≫ τ).hom.app (Opposite.op W)) x = 0
    rw [Etale.unit_app_comp_unitComparison]
    change ε.hom.app (Opposite.op W) x = 0
    rw [hε]
    rfl
  obtain ⟨U, f, hU⟩ := Etale.exists_unitComparison_app_eq_zero_of_isLimit
    D.affineOpensDiagram D.affineOpensDiagramι D.functionFieldCone D.fromSpecFunctionField
    D.fromSpecFunctionField_eq_functionFieldCone_comp D.isLimitFunctionFieldCone G W U₀ _ hx
  refine ⟨U, ?_⟩
  rw [← D.affineOpenUnit_comp_transition f G]
  exact hU

set_option backward.isDefEq.respectTransparency false in
private theorem genericVanishing_cokernel_lowerStar_epi
    (D : Scheme.{u}) [IsIntegral D] [QuasiSeparatedSpace D]
    {A B : Sheaf (Spec D.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : A ⟶ B) [Epi φ]
    (V : D.Etale)
    (s : (cokernel ((Etale.lowerStar AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).map φ)).obj.obj (Opposite.op V)) :
    D.genericVanishingSieve
      (cokernel ((Etale.lowerStar AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField).map φ)) s ∈ D.smallEtaleTopology V := by
  let L := Etale.upperStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField
  let R := Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} D.fromSpecFunctionField
  have : IsIso (adj.counit.app A) := Etale.isIso_generic_direct_image_counit D A
  have : IsIso (adj.counit.app B) := Etale.isIso_generic_direct_image_counit D B
  have : Epi (L.map (R.map φ) ≫ adj.counit.app B) := by
    change Epi ((R ⋙ L).map φ ≫ adj.counit.app B)
    rw [adj.counit.naturality]
    infer_instance
  have : Epi (L.map (R.map φ)) :=
    (epi_comp_iff_of_isIso (L.map (R.map φ)) (adj.counit.app B)).mp inferInstance
  have hz : IsZero (L.obj (cokernel (R.map φ))) :=
    (isZero_cokernel_of_epi (L.map (R.map φ))).of_iso (PreservesCokernel.iso L (R.map φ))
  exact genericVanishing_of_isZero_upperStar D _ hz V s

set_option backward.isDefEq.respectTransparency false in
/-- One prime-constant step of generic filtration preserves second-cohomology
vanishing, provided the corresponding prime constant sheaf on the curve has vanishing
second cohomology.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
(blueprint: lem-sc-generic-prime-filtration-step)

Proof: apply left exact generic direct image to the short exact sequence and let I be
its image in the third term. This gives a short exact sequence from the first term to
the second term to I. The cokernel Q of I in the third term has zero generic restriction:
the counit of generic pullback/pushforward is an isomorphism and inverse image is exact.
The third term is a finite constant generic sheaf, so its direct image and Q are torsion.
Continuity at the generic point makes every section of Q vanish locally on a
nonempty affine open. Thus Q has zero positive cohomology by generic acyclicity.
The long exact sequence for
I, the third direct image, and Q identifies their second cohomology. Smoothness implies
normality; normal generic constant comparison identifies the third direct image with
the curve's constant ZMod sheaf. It has vanishing H² by hconstant. Finally the long
exact sequence for the first direct image, second direct image, and I gives the result.
This argument needs no finiteness assumption on the first two terms. -/
theorem subsingleton_generic_prime_filtration_step
    {k : Type u} [Field k] [IsAlgClosed k] {D : Scheme.{u}}
    (g : D ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g] [IsAffine D] [IsIntegral D]
    (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
      AddCommGrpCat.{u + 1})) (hS : S.ShortExact) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (e : S.X₃ ≅ (Spec D.functionField).constantZMod ℓ)
    (hconstant : Subsingleton (Sheaf.H (D.constantZMod ℓ) 2))
    (hfirst : Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj S.X₁) 2)) :
    Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj S.X₂) 2) := by
  let T := Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField
  let R := S.map T
  have hR : R.Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono T).mp inferInstance S hS).1
  have : Mono R.f :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono T).mp inferInstance S hS).2
  let β := R.g
  let Q := cokernel β
  let I := Abelian.image β
  let π := cokernel.π β
  let i := Abelian.image.ι β
  let p := Abelian.factorThruImage β
  have w : R.f ≫ p = 0 := by
    apply (cancel_mono i).1
    simpa only [p, i, Category.assoc, Abelian.image.fac, zero_comp] using R.zero
  let A := ShortComplex.mk R.f p w
  let a : A ⟶ R :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := i
      comm₁₂ := by simp [A]
      comm₂₃ := by simpa only [A, p, i, Category.id_comp] using (Abelian.image.fac β).symm }
  have hA : A.ShortExact :=
    ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).mpr hR⟩
  let B := ShortComplex.mk i π (kernel.condition π)
  have hB : B.ShortExact := ⟨ShortComplex.exact_kernel π⟩
  have : Epi S.g := hS.epi_g
  have hQ : ∀ n : ℕ, Subsingleton (Sheaf.H Q (n + 1)) := fun n ↦
    IsCurve.subsingleton_H_of_genericVanishing g Q
      (genericVanishing_cokernel_lowerStar_epi D S.g) n
  let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    D.fromSpecFunctionField).unit.app (D.constantZMod ℓ)) :=
    isIso_constant_generic_unit g M
  let c : D.constantZMod ℓ ≅ T.obj ((Spec D.functionField).constantZMod ℓ) :=
    asIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).unit.app (D.constantZMod ℓ)) ≪≫
        T.mapIso ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          D.fromSpecFunctionField).app M)
  let e₃ : R.X₃ ≅ D.constantZMod ℓ := T.mapIso e ≪≫ c.symm
  have hthird : Subsingleton (Sheaf.H R.X₃ 2) := by
    let := hconstant
    apply Function.Injective.subsingleton (f := Sheaf.H.map e₃.hom 2)
    intro x y hxy
    have h := congrArg (Sheaf.H.map e₃.inv 2) hxy
    simpa only [← Sheaf.H.map_comp_apply, e₃.hom_inv_id, Sheaf.H.map_id_apply] using h
  have hI : Subsingleton (Sheaf.H I 2) := by
    let := hQ 0
    let := hthird
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hB x
      (Subsingleton.elim _ _) (by decide : 1 + 1 = 2)
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa only [hy0, CategoryTheory.Abelian.Ext.zero_comp] using hy.symm
  let : Subsingleton (Sheaf.H A.X₁ 2) := hfirst
  let : Subsingleton (Sheaf.H A.X₃ 2) := hI
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ _ hA x
    (Subsingleton.elim _ _)
  change Sheaf.H.map R.f 2 y = x at hy
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

end AlgebraicGeometry.IsConnectedCurve
