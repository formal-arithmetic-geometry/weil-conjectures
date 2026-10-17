/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension

import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
/-! # Bounded-torsion higher direct images of a projective line

Source: blueprint thm-sc-affine-torsion-cd, projective-line compactification row.
(blueprint: lem-sc-projective-line-bounded-torsion-vanishing)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
private theorem bounded_functor
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (P : C ⥤ D) [P.Additive] (F : C) (N : ℕ) (hF : N • 𝟙 F = 0) :
    N • 𝟙 (P.obj F) = 0 := by
  calc
    N • 𝟙 (P.obj F) = P.map (N • 𝟙 F) := by rw [Functor.map_nsmul, P.map_id]
    _ = P.map 0 := congrArg P.map hF
    _ = 0 := P.map_zero _ _

private theorem module_bound (S : Scheme.{u})
    (F : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (N : ℕ) (hN : 0 < N)
    (hF : N • 𝟙 F = 0) (q : ℕ) (hq : 2 < q) :
    IsZero (((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj F) := by
  let Λ := ULift.{u + 1} ℤ
  let A := ModuleCat.{u + 1} Λ
  let p := AlgebraicGeometry.ProjectiveLine S ↘ S
  let Ψ := sheafCompose (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
    (forget₂ A AddCommGrpCat.{u + 1})
  have : IsTorsionModuleSheaf F := (isTorsionModuleSheaf_iff_isTorsion F).mpr
    (isTorsion_of_nsmul_id_eq_zero hN (bounded_functor Ψ F N hF))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let Ω := AlgebraicClosure (S.residueField x)
  let s := S.algClosurePoint x
  have sq : IsPullback (𝟙 (AlgebraicGeometry.ProjectiveLine S)) p p (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨e₁, e₂, he⟩ := Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    Λ sq s s (𝟙 (Spec (.of Ω)))
      ((Category.id_comp s).trans (Category.comp_id s).symm)
    ⟨x, CommRingCat.ofHom (algebraMap (S.residueField x) Ω),
      Algebra.IsIntegral.isIntegral (R := S.residueField x), rfl⟩
    ⟨x, CommRingCat.ofHom (algebraMap (S.residueField x) Ω),
      Algebra.IsIntegral.isIntegral (R := S.residueField x), rfl⟩ F q
  let P := ProjectiveSpace.map (ULift.{u} (Fin 2)) s
  let Q := Etale.upperStar A P ⋙
    sheafCompose _ (forget₂ A AddCommGrpCat.{u + 1})
  have hQt : (Q.obj F).IsTorsion :=
    isTorsion_of_nsmul_id_eq_zero hN (bounded_functor Q F N hF)
  have hcoh : Subsingleton (Sheaf.H (Q.obj F) q) :=
    (IsCurve.hasTorsionCohomologicalDimensionLE
      (AlgebraicGeometry.ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω))).1 _ hQt q hq
  have : Subsingleton (Sheaf.H
      ((sheafCompose (AlgebraicGeometry.ProjectiveLine (Spec (.of Ω))).smallEtaleTopology
        (forget₂ A AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar A P).obj F)) q) := hcoh
  let E := (Etale.baseChangeSourceFunctorIso Λ (𝟙 S) p q).app F ≪≫
    (Etale.upperStarId A S).app (Etale.higherDirectImage Λ p q F)
  let D := (Etale.lowerStar A p).homologyRightDerivedFunctorPlusObjSingleFunctorIso F q
  let C := ((pointSmallEtale s).sheafFiber (A := A)).mapIso (D.symm ≪≫ E.symm)
  have : Subsingleton (((pointSmallEtale s).sheafFiber (A := A)).obj
      (((Etale.lowerStar A p).rightDerived q).obj F)) :=
    (C.toLinearEquiv.toAddEquiv.trans e₁).injective.subsingleton
  have hz := ModuleCat.isZero_of_subsingleton
    (((pointSmallEtale s).sheafFiber (A := A)).obj (((Etale.lowerStar A p).rightDerived q).obj F))
  let T := (pointSmallEtale s).sheafFiber (A := A)
  calc
    T.map (𝟙 _) = 𝟙 _ := T.map_id _
    _ = 0 := hz.eq_of_src _ _
    _ = T.map 0 := (T.map_zero _ _).symm

/-- A relative projective line has no bounded-torsion direct images above degree two.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, projective-line row of the Leray spectral sequence.
(blueprint: lem-sc-projective-line-bounded-torsion-vanishing)

Proof: Identify abelian sheaves with sheaves of modules over ULift integers, using the
exact underlying-abelian-group equivalence. The annihilator is preserved and reflected.
At each algebraic-closure geometric point of the base, the projective-line geometric-stalk
comparison identifies the stalk of the higher direct image with cohomology of the geometric
projective line. This is a curve over an algebraically closed field, so its torsion
cohomology vanishes above degree two. Geometric fibres are jointly faithful and therefore
vanishing of all these stalks gives a zero sheaf. Exact forgetting commutes with right
derived functors and direct image, which transfers the result to abelian sheaves. -/
theorem isZero_rightDerived_projectiveLine_of_killed_by
    (S : Scheme.{u})
    (F : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hF : N • 𝟙 F = 0)
    (q : ℕ) (hq : 2 < q) :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj F) := by
  let Λ := ULift.{u + 1} ℤ
  let A := ModuleCat.{u + 1} Λ
  let X := AlgebraicGeometry.ProjectiveLine S
  let p := X ↘ S
  let ΦX := sheafCompose X.smallEtaleTopology (forget₂ A AddCommGrpCat.{u + 1})
  let ΦS := sheafCompose S.smallEtaleTopology (forget₂ A AddCommGrpCat.{u + 1})
  let G := ΦX.objPreimage F
  let eG := ΦX.objObjPreimageIso F
  have hΦG : N • 𝟙 (ΦX.obj G) = 0 := by
    rw [← cancel_mono eG.hom, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id eG.hom, ← Preadditive.comp_nsmul, hF, comp_zero]
  have hG : N • 𝟙 G = 0 := by
    apply ΦX.map_injective
    rw [Functor.map_nsmul, ΦX.map_id, ΦX.map_zero]
    exact hΦG
  let DM := Etale.lowerStar A p
  let DA := Etale.lowerStar AddCommGrpCat.{u + 1} p
  let e₁ := Functor.compRightDerivedObjIso ΦX DA
    (fun I _ ↦ Functor.rightAcyclic_of_injective (ΦX.obj I)) q G
  let e₂ := Functor.rightDerivedObjIsoOfIso
    (Etale.lowerStarCompForget₂Iso Λ p).symm q G
  let e₃ := Functor.rightDerivedCompObjIso DM ΦS q G
  have hz := ΦS.map_isZero (module_bound S G N hN hG q hq)
  have hz' : IsZero ((DA.rightDerived q).obj (ΦX.obj G)) :=
    hz.of_iso (e₁.symm ≪≫ e₂ ≪≫ e₃)
  exact hz'.of_iso ((DA.rightDerived q).mapIso eG.symm)

end AlgebraicGeometry.Scheme
