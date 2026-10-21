/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClosedCostalkEtaleOperations
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import all Sheaf.SixFunctors.EtaleNativeTensorPullback
import all Sheaf.SixFunctors.ClosedTensorDualAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.SixFunctors.Finite.Exact

/-! # The closed-support projection formula

Source: the projection-identity paragraph of the current closed-costalk-duality proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem etaleOpenClosedData
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (pi : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    (ai : pi ⊣ closedCostalkEtaleModulePush i R)
    (pj : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules U ((closedCostalkEtaleRingPullback j).obj R))
    (aj : pj ⊣ closedCostalkEtaleModulePush j R) :
    let qi := closedCostalkEtaleModulePush i R
    PreservesFiniteLimits qi ∧ PreservesFiniteColimits qi ∧ IsIso ai.counit ∧
      (∀ N, IsZero (pj.obj (qi.obj N))) ∧
      JointlyReflectIsomorphisms (pairFunctor pi pj) := by
  dsimp only
  let P := etaleForget T R
  let Qi := etaleForget Z ((closedCostalkEtaleRingPullback i).obj R)
  let Qj := etaleForget U ((closedCostalkEtaleRingPullback j).obj R)
  let qi := closedCostalkEtaleModulePush i R
  obtain ⟨ei, _, hci⟩ := etaleModuleUnderlying i R pi ai
  obtain ⟨ej, _, _hcj⟩ := etaleModuleUnderlying j R pj aj
  have : PreservesFiniteLimits (qi ⋙ P) :=
    inferInstanceAs (PreservesFiniteLimits (Qi ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} i))
  have : PreservesFiniteColimits (qi ⋙ P) :=
    inferInstanceAs (PreservesFiniteColimits (Qi ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} i))
  have hl := preservesFiniteLimits_of_reflects_of_preserves qi P
  have hr := preservesFiniteColimits_of_reflects_of_preserves qi P
  have hc (N) : IsIso (ai.counit.app N) := by
    have : IsIso (Qi.map (ai.counit.app N)) := by
      rw [hci]
      infer_instance
    exact isIso_of_reflects_iso _ Qi
  have hcn : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  refine ⟨hl, hr, hcn, ?_, ?_⟩
  · intro N
    have hz : IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Qi.obj N))) :=
      Etale.isZero_upperStar_lowerStar_of_disjoint_range AddCommGrpCat.{u + 1} j i
        (disjoint_range_of_range_eq_compl i j hij).symm (Qi.obj N)
    have h0 : IsZero (Qj.obj (pj.obj (qi.obj N))) := hz.of_iso (ej.app (qi.obj N))
    apply (IsZero.iff_id_eq_zero _).2
    apply Qj.map_injective
    rw [Qj.map_id, Qj.map_zero]
    exact h0.eq_of_src _ _
  · refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
    intro M N f hi hj
    have hpi : IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} i).map (P.map f)) :=
      (NatIso.isIso_map_iff ei f).1 (by dsimp; infer_instance)
    have hpj : IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} j).map (P.map f)) :=
      (NatIso.isIso_map_iff ej f).1 (by dsimp; infer_instance)
    have : IsIso (P.map f) := Etale.isIso_of_isIso_upperStar_map
      AddCommGrpCat.{u + 1} j i (by simp [hij]) (P.map f) hpj hpi
    exact isIso_of_reflects_iso f P

/-- Closed direct image commutes with native derived tensor against ambient complexes.
No exceptional functor or dualizing object occurs in this assertion.
Source: current blueprint, closed-costalk-duality, projection-identity paragraph;
Stacks Tags 03EL, 07A4 and 04CA.
(blueprint: lem-weil-etale-closed-tensor-projection).

Proof: identify module inverse image with the existing abelian inverse image,
compatibly with both units and counits. Forgetting scalars detects exactness,
the closed counit, complementary-open vanishing and joint detection. Pass to exact
termwise derived functors. Homology comparisons retain vanishing and detection.
For X = i_* N tensor K, open inverse image vanishes, by tensor pullback and the
closed/open vanishing. Closed inverse image of the adjunction unit on X is invertible
by the triangle identity and closed counit. Its open image is between zero objects.
Joint detection makes the unit on X invertible. Compose this unit with the natural
tensor-pullback isomorphism and closed counit to obtain the projection isomorphism.
Finally transport exact derived inverse and direct image to the supplied functors by
uniqueness of lifts through Q. Everything is natural in N and K, without boundedness,
flatness or constancy assumptions on them or on the coefficient ring. -/
theorem etaleClosedTensorProjection
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (iStar : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    [iStar.Additive] (ai : iStar ⊣ closedCostalkEtaleModulePush i R)
    (iPull : DerivedCategory (closedCostalkEtaleModules T R) ⥤
      DerivedCategory (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (pullFactors : DerivedCategory.Q ⋙ iPull ≅
      iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (iPush : DerivedCategory
        (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)) ⥤
      DerivedCategory (closedCostalkEtaleModules T R))
    (pushFactors : DerivedCategory.Q ⋙ iPush ≅
      (closedCostalkEtaleModulePush i R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) :
    let RZ := ((closedCostalkEtaleRingPullback i).obj R)
    let tT := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} T.smallEtaleTopology R)
    let tZ := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ)
    Nonempty ((iPush).prod (𝟭 _) ⋙ tT ≅
      (𝟭 _).prod (iPull) ⋙ tZ ⋙ (iPush)) := by
  dsimp only
  let RZ := (closedCostalkEtaleRingPullback i).obj R
  let RU := (closedCostalkEtaleRingPullback j).obj R
  let pi := iStar
  let qi := closedCostalkEtaleModulePush i R
  obtain ⟨pj, aj, _, _⟩ := etaleModulePresentation j R
  obtain ⟨hpi, hpi'⟩ := etalePullExact i R pi ai
  obtain ⟨hpj, hpj'⟩ := etalePullExact j R pj aj
  have : PreservesFiniteLimits pi := hpi
  have : PreservesFiniteColimits pi := hpi'
  have : PreservesFiniteLimits pj := hpj
  have : PreservesFiniteColimits pj := hpj'
  have : pj.Additive := Functor.additive_of_preserves_binary_products pj
  obtain ⟨hqi, hqi', hc, hz, hdet⟩ := etaleOpenClosedData i j hij R pi ai pj aj
  have : PreservesFiniteLimits qi := hqi
  have : PreservesFiniteColimits qi := hqi'
  have : IsIso ai.counit := hc
  let ad := exactDerivedAdjunction ai
  have : ∀ N, IsIso (ad.counit.app N) :=
    fun N ↦ exactDerivedAdjunction_counit_isIso ai N
  have : IsIso ad.counit := NatIso.isIso_of_isIso_app _
  have hd := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory pi pj hdet
  have hzd (N : DerivedCategory (closedCostalkEtaleModules Z RZ)) :
      IsZero (pj.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (hz ((DerivedCategory.homologyFunctor _ n).obj N)).of_iso
      (pj.mapIso ((qi.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  obtain ⟨ei⟩ := etaleNativeTensorPullback i R pi ai
    pi.mapDerivedCategory pi.mapDerivedCategoryFactors
  obtain ⟨ej⟩ := etaleNativeTensorPullback j R pj aj
    pj.mapDerivedCategory pj.mapDerivedCategoryFactors
  let tT := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} T.smallEtaleTopology R)
  let tZ := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ)
  have hu (N : DerivedCategory (closedCostalkEtaleModules Z RZ))
      (K : DerivedCategory (closedCostalkEtaleModules T R)) :
      IsIso (ad.unit.app (tT.obj (qi.mapDerivedCategory.obj N, K))) := by
    apply CategoryTheory.supportedUnit pi.mapDerivedCategory qi.mapDerivedCategory
      pj.mapDerivedCategory ad
      (fun f hi hj ↦ hd.isIso_of_pairFunctor f hi hj) hzd
    let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} U.smallEtaleTopology RU
    obtain ⟨⟨m, ac, ev⟩, hm, _, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} U.smallEtaleTopology RU
    dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
    subst m
    have := (ac (pj.mapDerivedCategory.obj K)).isLeftAdjoint
    have h0 : IsZero
        ((@MonoidalCategory.tensor _ _
          (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} U.smallEtaleTopology RU)).obj
            (pj.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N),
              pj.mapDerivedCategory.obj K)) :=
      (MonoidalCategory.tensorRight (pj.mapDerivedCategory.obj K)).map_isZero (hzd N)
    exact h0.of_iso (ej.app (qi.mapDerivedCategory.obj N, K))
  obtain ⟨e⟩ := CategoryTheory.projectionOfSupportedUnit
    pi.mapDerivedCategory qi.mapDerivedCategory ad tT tZ ei hu
  obtain ⟨eP⟩ := derivedIso pi iPull pullFactors
  obtain ⟨eQ⟩ := derivedIso qi iPush pushFactors
  exact ⟨Functor.isoWhiskerRight (NatIso.prod eQ.symm (Iso.refl (𝟭 _))) tT ≪≫ e ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod (Iso.refl (𝟭 _)) eP) tZ)
      qi.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod iPull ⋙ tZ) eQ⟩


end AlgebraicGeometry.Scheme
