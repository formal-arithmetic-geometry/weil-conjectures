/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocalCyclicModuleForget
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
/-!
# Constructible cyclic module sheaves from finite abelian charts

Source: Stacks Project, Tags 03RU, 03RW and 0GKV, final coefficient comparison.
(blueprint: lem-weil-pbc-constructible-cyclic-module-of-abelian)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Finite abelian constructible charts of a cyclic module sheaf lift to module charts.
Source: Stacks Project, Tag 0GKV, final coefficient comparison, and Tags 03RU and 03RW.
(blueprint: lem-weil-pbc-constructible-cyclic-module-of-abelian)

Proof: use the same finite stratification. Inverse image commutes with forgetting
coefficients, so its module restriction has the indicated underlying abelian sheaf.
The given finite constant charts provide a locally constant datum. Lift any geometric
point through their etale cover; the pullback-stalk and constant-stalk comparisons
identify its stalk with the finite abelian chart value. Transport through the given
abelian isomorphism. The finite-local-cyclic-module comparison now lifts these finite
abelian local systems to finite module charts. This comparison discards empty charts,
so neither empty schemes nor arbitrarily large constant values on empty charts cause
an exception. The argument works for every nonzero modulus, including modulus one. -/
theorem isConstructibleEtaleModuleSheaf_of_abelianIso {S : Scheme.{u}} (p : ℕ) [NeZero p]
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))))
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (Etale.moduleAbelianForget (ULift.{u + 1} (ZMod p)) S).obj M ≅ A)
    (hA : IsConstructibleAbelianSheaf A) : IsConstructibleEtaleModuleSheaf M := by
  classical
  let R := ULift.{u + 1} (ZMod p)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨T, -, hT⟩ := hA
  refine ⟨T, fun k ↦ ?_⟩
  let G := (Etale.upperStar (ModuleCat.{u + 1} R) (T.immersion k)).obj M
  let B := (Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion k)).obj A
  let H := (Etale.moduleAbelianForget R (T.domain k)).obj G
  let eH : H ≅ B :=
    ((Etale.moduleAbelianUpperStarIso R (T.immersion k)).app M).symm ≪≫
      (Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion k)).mapIso e
  obtain ⟨𝒰, h𝒰⟩ := hT k
  have hconst (i : 𝒰.I₀) : (B.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      ((T.domain k).smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) := by
    apply (isConstant_over_iff_upperStar AddCommGrpCat.{u + 1}
      (𝒰.etalePrecoverageToEtale i) B).mpr
    obtain ⟨E, -, ⟨eE⟩⟩ := h𝒰 i
    exact Sheaf.isConstant_of_iso _ eE
  have : IsLocallyConstantSheaf B := ⟨⟨⟨𝒰, hconst⟩⟩⟩
  have : IsLocallyConstantSheaf H := IsLocallyConstantSheaf.of_iso eH.symm
  apply (finite_local_cyclic_module_forget_iff p G).mp
  refine ⟨inferInstance, ?_⟩
  intro Ω _ _ s
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
  have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
  obtain ⟨E, hE, ⟨eE⟩⟩ := h𝒰 i
  let eS := ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (𝒰.f i) t).app B).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso eE ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso E
  have hB : Finite (((pointSmallEtale (t ≫ 𝒰.f i)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj B) :=
    Finite.of_equiv E eS.addCommGroupIsoToAddEquiv.toEquiv.symm
  have : Finite (((pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj B) := by simpa only [ht] using hB
  exact Finite.of_equiv _
    ((pointSmallEtale s).sheafFiber.mapIso eH).addCommGroupIsoToAddEquiv.toEquiv.symm
end AlgebraicGeometry.Scheme
