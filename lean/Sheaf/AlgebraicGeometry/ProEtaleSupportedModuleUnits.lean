/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

/-!
# Supported module units before passage to complexes

Source: blueprint main-20261015, smooth purity, sk-prop-sf-localization,
lem-exc-proetale-support-triangle, supported-kernel identification, Steps 1–3
(blueprint: lem-exc-proetale-finite-supported-module-units).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {T U Z : Scheme.{u}} (i : Z ⟶ T) (j : U ⟶ T) (A : Type (u + 1))
  [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]

private theorem isIso_unitMate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    {M : C} {N : D} (e : N ≅ L.obj M) (g : M ⟶ G.obj N)
    (h : g ≫ G.map e.hom = adj.unit.app M) :
    IsIso ((adj.homEquiv M N).symm g) := by
  have he : (adj.homEquiv M N).symm g = e.inv := by
    apply (adj.homEquiv M N).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, ← h,
      Category.assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [he]
  infer_instance

private theorem isIso_of_unit_comparison
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (adj' : L' ⊣ G)
    (P : C ⥤ E) [P.ReflectsIsomorphisms] (H : F ⥤ E)
    {M : C} {N : F} (b : P.obj (G.obj (L'.obj M)) ≅ H.obj N)
    (a : P.obj M ⟶ H.obj N) [IsIso a]
    (h : P.map (adj'.unit.app M) ≫ b.hom = a) : IsIso (adj.unit.app M) := by
  have : IsIso (P.map (adj'.unit.app M) ≫ b.hom) := h ▸ inferInstance
  have : IsIso (P.map (adj'.unit.app M)) :=
    IsIso.of_isIso_comp_right (P.map (adj'.unit.app M)) b.hom
  have : IsIso (adj'.unit.app M) := isIso_of_reflects_iso _ P
  have he := Adjunction.unit_leftAdjointUniq_hom_app adj adj' M
  have : IsIso (adj.unit.app M ≫ G.map ((adj.leftAdjointUniq adj').hom.app M)) :=
    he ▸ inferInstance
  exact IsIso.of_isIso_comp_right (adj.unit.app M)
    (G.map ((adj.leftAdjointUniq adj').hom.app M))

/-- Pullback of the actual open adjunction unit is invertible.
Source: blueprint supported-kernel argument, Step 3
(blueprint: lem-exc-proetale-finite-supported-module-units).
Proof: the unit-compatible abelian comparison identifies the mate of the module
unit with an isomorphism. The abelian open direct image is fully faithful, so its
counit is invertible. The right triangle identity then makes the module counit
invertible after forgetting modules. This forgetful functor reflects isomorphisms,
so the module direct image is fully faithful. For any adjunction to this right
adjoint, the left adjoint sends the unit to an isomorphism. -/
private theorem finiteOpenUnit_pullback_isIso [IsOpenImmersion j]
    (N : FiniteCoefficientModules T A) :
    IsIso ((finiteCoefficientModulePullback j A).map
      ((finiteModuleAdjunction j A).unit.app N)) := by
  obtain ⟨adjR, adjS, eR, eS, α, β, hR, hS, huR, huS, he, hb, hc⟩ :=
    finiteScalarUnitComparison j (RingHom.id A)
  let P := SheafOfModules.toSheaf (finiteCoefficientRingSheaf T A)
  let Q := SheafOfModules.toSheaf (finiteCoefficientRingSheaf U A)
  let a := Scheme.proEtaleSheafAdjunction j AddCommGrpCat.{u + 1}
  have ha : IsIso a.counit := by
    let aj := openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j
    have : IsIso aj.counit := inferInstance
    have : (Scheme.proEtaleSheafDirectImage j AddCommGrpCat.{u + 1}).Full :=
      aj.fullyFaithfulROfIsIsoCounit.full
    have : (Scheme.proEtaleSheafDirectImage j AddCommGrpCat.{u + 1}).Faithful :=
      aj.fullyFaithfulROfIsIsoCounit.faithful
    exact a.counit_isIso_of_R_fully_faithful
  have hcounit (H : FiniteCoefficientModules U A) : IsIso (adjS.counit.app H) := by
    let c := (a.homEquiv (P.obj ((finiteScalarModuleDirectImage j A).obj H))
      (Q.obj ((finiteCoefficientModulePullback j A).obj
        ((finiteScalarModuleDirectImage j A).obj H)))).symm
      (P.map (adjS.unit.app ((finiteScalarModuleDirectImage j A).obj H)))
    have hci : IsIso c := isIso_unitMate a
      (eS.app ((finiteScalarModuleDirectImage j A).obj H)) _ (huS _)
    have hh : c ≫ Q.map (adjS.counit.app H) = a.counit.app (Q.obj H) := by
      apply (a.homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      calc
        _ = 𝟙 _ := by
          change P.map (adjS.unit.app _) ≫
            P.map ((finiteScalarModuleDirectImage j A).map (adjS.counit.app H)) = 𝟙 _
          rw [← P.map_comp, adjS.right_triangle_components]
          exact P.map_id _
        _ = _ := by
          symm
          change (a.homEquiv _ _) (a.counit.app (Q.obj H)) = 𝟙 _
          rw [Adjunction.homEquiv_unit, a.right_triangle_components]
    have : IsIso (c ≫ Q.map (adjS.counit.app H)) := by rw [hh]; infer_instance
    have : IsIso (Q.map (adjS.counit.app H)) := IsIso.of_isIso_comp_left c _
    exact isIso_of_reflects_iso _ Q
  have : IsIso adjS.counit := NatIso.isIso_of_isIso_app _
  have : (finiteModulePushforward j A).Full := adjS.fullyFaithfulROfIsIsoCounit.full
  have : (finiteModulePushforward j A).Faithful := adjS.fullyFaithfulROfIsIsoCounit.faithful
  infer_instance

/-- Supported closed units, zero open restriction of closed direct images, and
invertibility of the restricted open unit for finite left modules.

Source: blueprint main-20261015, smooth purity, sk-prop-sf-localization,
lem-exc-proetale-support-triangle.proof.md, supported-kernel identification, Steps 1–3;
Stacks Project, Tags 09AA and 09AH; the unit-preserving abelian comparison of
lem-exc-proetale-finite-scalar-unit-comparison
(blueprint: lem-exc-proetale-finite-supported-module-units).

Proof:
1. Apply finiteScalarUnitComparison to the identity ring map of A for i and j.
   Its comparisons identify the underlying abelian sheaves of module pullbacks
   with abelian inverse images, and identify the module units with abelian units.
   Forgetting module structure reflects isomorphisms and detects zero objects.
2. If j* N is zero, the open comparison makes the abelian open restriction zero.
   Apply abelian_closed_support to obtain invertibility of the abelian closed unit.
   The closed unit equation writes this map as the forgotten module unit followed
   by an isomorphism. Cancel the latter and reflect invertibility through forgetting.
   The comparison supplies an adjunction with the specified right adjoint. The
   left-adjoint uniqueness isomorphism intertwines its unit with the actual unit
   of finiteModuleAdjunction, so the actual closed unit is invertible too.
3. For M on Z, the open restriction of its abelian closed direct image is zero:
   sections are evaluated on empty base changes since the two ranges are disjoint.
   The pullback comparison identifies this with the forgotten module pullback.
   Faithfulness and preservation of zero morphisms show its identity is zero.
4. For the open immersion, the abelian right adjoint is fully faithful. The mate
   of the forgotten module unit is an isomorphism by its unit equation. The right
   triangle identity then identifies its composite with the forgotten module
   counit with the invertible abelian counit. Cancel and reflect to show the
   module counit invertible. Thus the module right adjoint is fully faithful,
   and the left adjoint of finiteModuleAdjunction sends its unit to an isomorphism.
This uses the direct abelian support theorem, so the assumed commutative criterion
is retained as an input but is unnecessary for this shorter proof. No choice of
coefficient witnesses, commutativity, or nonzero-ring hypothesis is required. -/
theorem finiteSupportedModuleUnits
    [IsLocallyNoetherian T] [CompactSpace T]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (_hB : ∀ N : Scheme.proEtaleRingModules T
        (Scheme.proEtaleConstantRing T (ULift.{u} (ZMod (addOrderOf (1 : A))))),
      ((Scheme.proEtaleConstantRingPushforward
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) i).essImage N ↔
        IsZero ((Scheme.proEtaleConstantRingPullback
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) j).obj N)) ∧
      (IsZero ((Scheme.proEtaleConstantRingPullback
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) j).obj N) →
        IsIso ((Scheme.proEtaleConstantRingAdjunction
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) i).unit.app N))) :
    (∀ N : FiniteCoefficientModules T A,
      IsZero ((finiteCoefficientModulePullback j A).obj N) →
        IsIso ((finiteModuleAdjunction i A).unit.app N)) ∧
    (∀ M : FiniteCoefficientModules Z A,
      IsZero ((finiteCoefficientModulePullback j A).obj
        ((finiteModulePushforward i A).obj M))) ∧
    (∀ N : FiniteCoefficientModules T A,
      IsIso ((finiteCoefficientModulePullback j A).map
        ((finiteModuleAdjunction j A).unit.app N))) := by
  obtain ⟨adjRi, adjSi, eRi, eSi, αi, βi, hRi, hSi, huRi, huSi, hei, hbi, hci⟩ :=
    finiteScalarUnitComparison i (RingHom.id A)
  obtain ⟨adjRj, adjSj, eRj, eSj, αj, βj, hRj, hSj, huRj, huSj, hej, hbj, hcj⟩ :=
    finiteScalarUnitComparison j (RingHom.id A)
  let P := SheafOfModules.toSheaf (finiteCoefficientRingSheaf T A)
  let Q := SheafOfModules.toSheaf (finiteCoefficientRingSheaf U A)
  let R := SheafOfModules.toSheaf (finiteCoefficientRingSheaf Z A)
  refine ⟨?_, ?_, finiteOpenUnit_pullback_isIso j A⟩
  · intro N hN
    have hz := (Q.map_isZero hN).of_iso (eSj.app N).symm
    have hu : IsIso ((Scheme.proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app
        (P.obj N)) := (abelian_closed_support i j hU).2 _ hz
    exact isIso_of_unit_comparison (finiteModuleAdjunction i A) adjSi P
      (Scheme.proEtaleSheafDirectImage i AddCommGrpCat.{u + 1})
      ((Scheme.proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).mapIso (eSi.app N))
      ((Scheme.proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app (P.obj N))
      (huSi N)
  · intro M
    have hz : IsZero ((Scheme.proEtaleSheafInverseImage j AddCommGrpCat.{u + 1}).obj
        ((Scheme.proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).obj (R.obj M))) := by
      have hd : Set.range i.base ∩ Set.range j.base = ∅ := by
        rw [hU]
        exact Set.inter_compl_self _
      exact (isZero_openImmersionRestriction_lowerStar AddCommGrpCat.{u + 1}
        i j hd (R.obj M)).of_iso
          ((upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).app _)
    have hz' : IsZero (Q.obj ((finiteCoefficientModulePullback j A).obj
        ((finiteModulePushforward i A).obj M))) := hz.of_iso (eSj.app _)
    apply (IsZero.iff_id_eq_zero _).2
    apply Q.map_injective
    rw [Q.map_id, Q.map_zero]
    exact hz'.eq_of_src _ _

end AlgebraicGeometry.ProEtale
