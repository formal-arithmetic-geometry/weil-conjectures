/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# Open and closed localization for noncommutative ring objects

Source: Stacks Project, Pro-etale Cohomology, Tags 09AA, 09BM, 09BN and 09AH;
Modules on Sites, Tag 0F6Z (blueprint: lem-sfb-noncommutative-ringed-open-closed).

The assertion bundle below spells out the conclusions for specified adjunctions. This lets
one state precisely the same conclusions after the specified coefficient identifications.
The coefficient equivalence is constructed by restriction in both directions, without a
commutativity hypothesis. All geometric operations are the recorded canonical operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vC uC vD uD vE uE vA uA

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The conclusions of open/closed localization, bundled for specified functors and
adjunctions so the same assertion can be used after coefficient transport.

Source: Stacks Tags 09AA, 09BM, 09BN, 09AH and 0F6Z
(blueprint: lem-sfb-noncommutative-ringed-open-closed).
The three maps in the sequence are the specified counit and unit, not arbitrary maps.
`ComposableArrows.Exact` with monic first arrow and epic second arrow states short exactness.
-/
def ringSheafOpenClosedAssertions
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {E : Type uE} [Category.{vE} E] [Abelian E]
    (iL : C ⥤ D) (iR : D ⥤ C) (jL : C ⥤ E) (jR jE : E ⥤ C)
    (ai : iL ⊣ iR) (aj : jL ⊣ jR) (ae : jE ⊣ jL) : Prop :=
  iL.Additive ∧ iR.Additive ∧ jL.Additive ∧ jR.Additive ∧ jE.Additive ∧
  PreservesFiniteLimits iL ∧ PreservesFiniteColimits iL ∧
  PreservesFiniteLimits jL ∧ PreservesFiniteColimits jL ∧
  PreservesFiniteLimits iR ∧ PreservesFiniteColimits iR ∧
  PreservesFiniteLimits jE ∧ PreservesFiniteColimits jE ∧
  (∀ N : D, IsIso (ai.counit.app N)) ∧
  (∀ N : E, IsIso (aj.counit.app N)) ∧
  (∀ N : E, IsIso (ae.unit.app N)) ∧
  (∀ N : D, IsZero (jL.obj (iR.obj N))) ∧
  (∀ N : E, IsZero (iL.obj (jE.obj N))) ∧
  (∀ M : C, Mono (ae.counit.app M) ∧ Epi (ai.unit.app M) ∧
    (ComposableArrows.mk₂ (ae.counit.app M) (ai.unit.app M)).Exact) ∧
  (∀ M : C, IsIso (jL.map (aj.unit.app M))) ∧
  (∀ M : C, IsZero (jL.obj M) → IsZero (iL.obj M) → IsZero M) ∧
  (∀ (M N : C) (f : M ⟶ N), Mono (jL.map f) → Mono (iL.map f) → Mono f)

/-- The coefficient equivalence needed here, with no commutativity restriction.
Its functor is restriction along the specified ring-object isomorphism; its inverse
is restriction along the inverse. Both comparison isomorphisms have identity carriers.

Source: restriction of scalars in blueprint `sk-def-sfb-change-of-scalars`, clause 5;
the elementary inverse-restriction argument in step 8 of this node
(blueprint: lem-sfb-noncommutative-ringed-open-closed).
-/
def ringSheafScalarEquivalence
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    {R S : A} [MonObj R] [MonObj S] (e : R ≅ S) [IsMonHom e.hom] :
    Mod A S ≌ Mod A R :=
  CategoryTheory.Equivalence.mk (Mod.comap e.hom) (Mod.comap e.inv)
    ((Mod.comapId S).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp e.inv e.hom)
    ((Mod.comapComp e.hom e.inv).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)

private theorem abelianOpenCounit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction _ j)
    (openImmersionRestrictionLowerStarAdjunction _ j)]
  exact inferInstanceAs
    (IsIso ((upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).hom.app _ ≫ _))

private theorem transportAssertions
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D D' : Type uD} [Category.{vD} D] [Abelian D] [Category.{vD} D'] [Abelian D']
    {E E' : Type uE} [Category.{vE} E] [Abelian E] [Category.{vE} E'] [Abelian E']
    (iL : C ⥤ D) (iR : D ⥤ C) (jL : C ⥤ E) (jR jE : E ⥤ C)
    (ai : iL ⊣ iR) (aj : jL ⊣ jR) (ae : jE ⊣ jL)
    (e : D ≌ D') (f : E ≌ E') [e.functor.Additive] [f.functor.Additive]
    (h : ringSheafOpenClosedAssertions iL iR jL jR jE ai aj ae) :
    ringSheafOpenClosedAssertions (iL ⋙ e.functor) (e.inverse ⋙ iR)
      (jL ⋙ f.functor) (f.inverse ⋙ jR) (f.inverse ⋙ jE)
      (ai.comp e.toAdjunction) (aj.comp f.toAdjunction) (f.symm.toAdjunction.comp ae) := by
  rcases h with ⟨hiL, hiR, hjL, hjR, hjE, hiLl, hiLc, hjLl, hjLc,
    hiRl, hiRc, hjEl, hjEc, hci, hcj, hue, hzj, hzi, hs, huj, hd, hm⟩
  have ci (N) : IsIso ((ai.comp e.toAdjunction).counit.app N) := by
    have := hci (e.inverse.obj N)
    rw [Adjunction.comp_counit_app]
    infer_instance
  have cj (N) : IsIso ((aj.comp f.toAdjunction).counit.app N) := by
    have := hcj (f.inverse.obj N)
    rw [Adjunction.comp_counit_app]
    infer_instance
  have ue (N) : IsIso ((f.symm.toAdjunction.comp ae).unit.app N) := by
    have := hue (f.inverse.obj N)
    rw [Adjunction.comp_unit_app]
    infer_instance
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ci, cj, ue, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    exact f.functor.map_isZero (hzj (e.inverse.obj N))
  · intro N
    exact e.functor.map_isZero (hzi (f.inverse.obj N))
  · intro M
    obtain ⟨hmono, hepi, hex⟩ := hs M
    let α := jE.mapIso (f.unitIso.symm.app (jL.obj M))
    let β := iR.mapIso (e.unitIso.app (iL.obj M))
    have ha : (f.symm.toAdjunction.comp ae).counit.app M = α.hom ≫ ae.counit.app M := by
      rw [Adjunction.comp_counit_app]
      rfl
    have hb : (ai.comp e.toAdjunction).unit.app M = ai.unit.app M ≫ β.hom := by
      rw [Adjunction.comp_unit_app]
      rfl
    rw [ha, hb]
    refine ⟨inferInstance, inferInstance, ?_⟩
    let iso : ComposableArrows.mk₂ (ae.counit.app M) (ai.unit.app M) ≅
        ComposableArrows.mk₂ (α.hom ≫ ae.counit.app M) (ai.unit.app M ≫ β.hom) :=
      ComposableArrows.isoMk₂ α.symm (Iso.refl _) β
        (by change ae.counit.app M ≫ 𝟙 _ = α.inv ≫ α.hom ≫ ae.counit.app M; simp)
        (by change ai.unit.app M ≫ β.hom = 𝟙 _ ≫ (ai.unit.app M ≫ β.hom); simp)
    exact ComposableArrows.exact_of_iso iso hex
  · intro M
    have := cj ((jL ⋙ f.functor).obj M)
    have htri := (aj.comp f.toAdjunction).left_triangle_components M
    rw [← IsIso.inv_eq_of_inv_hom_id htri]
    infer_instance
  · intro M hj hi
    apply hd M
    · apply (IsZero.iff_id_eq_zero _).2
      apply f.functor.map_injective
      simpa using hj.eq_of_src (f.functor.map (𝟙 (jL.obj M))) (f.functor.map 0)
    · apply (IsZero.iff_id_eq_zero _).2
      apply e.functor.map_injective
      simpa using hi.eq_of_src (e.functor.map (𝟙 (iL.obj M))) (e.functor.map 0)
  · intro M N g hj hi
    exact hm M N g (f.functor.mono_of_mono_map hj) (e.functor.mono_of_mono_map hi)

private theorem scalarUnitInv_hom
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    {R S : A} [MonObj R] [MonObj S] (e : R ≅ S) [IsMonHom e.hom] (N : Mod A S) :
    ((ringSheafScalarEquivalence e).unitIso.inv.app N).hom = 𝟙 _ := by
  simp only [ringSheafScalarEquivalence, CategoryTheory.Equivalence.mk,
    CategoryTheory.Equivalence.adjointifyη, Iso.trans_def,
    Iso.trans_symm, Iso.symm_symm_eq, Functor.comp_obj, Functor.id_obj, Iso.trans_assoc,
    Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp, Mod.comp_hom', Mod.comap_map_hom,
    Mod.comapId_inv_app_hom, Mod.comapCongr_hom_app_hom, Mod.comapComp_hom_app_hom,
    Mod.comapComp_inv_app_hom, Mod.comapId_hom_app_hom, Mod.comapCongr_inv_app_hom]
  repeat erw [Category.id_comp]
  rfl

private theorem scalarUnit_hom
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    {R S : A} [MonObj R] [MonObj S] (e : R ≅ S) [IsMonHom e.hom] (N : Mod A S) :
    ((ringSheafScalarEquivalence e).unitIso.hom.app N).hom = 𝟙 _ := by
  have h := congrArg (fun g ↦ g.hom) ((ringSheafScalarEquivalence e).unitIso.app N).hom_inv_id
  change ((ringSheafScalarEquivalence e).unitIso.hom.app N).hom ≫
    ((ringSheafScalarEquivalence e).unitIso.inv.app N).hom = 𝟙 _ at h
  rw [scalarUnitInv_hom] at h
  change ((ringSheafScalarEquivalence e).unitIso.hom.app N).hom ≫ 𝟙 N.X = 𝟙 N.X at h
  exact (Category.comp_id _).symm.trans h

private theorem scalarCounit_hom
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    {R S : A} [MonObj R] [MonObj S] (e : R ≅ S) [IsMonHom e.hom] (N : Mod A R) :
    ((ringSheafScalarEquivalence e).counitIso.hom.app N).hom = 𝟙 _ := by
  simp only [ringSheafScalarEquivalence, CategoryTheory.Equivalence.mk, Functor.comp_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom, Mod.comapId_hom_app_hom]
  change 𝟙 N.X ≫ 𝟙 N.X ≫ 𝟙 N.X = 𝟙 N.X
  simp only [Category.id_comp]

private theorem scalarCounitInv_hom
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
    {R S : A} [MonObj R] [MonObj S] (e : R ≅ S) [IsMonHom e.hom] (N : Mod A R) :
    ((ringSheafScalarEquivalence e).counitIso.inv.app N).hom = 𝟙 _ := by
  have h := congrArg (fun g ↦ g.hom) ((ringSheafScalarEquivalence e).counitIso.app N).hom_inv_id
  change ((ringSheafScalarEquivalence e).counitIso.hom.app N).hom ≫
    ((ringSheafScalarEquivalence e).counitIso.inv.app N).hom = 𝟙 _ at h
  rw [scalarCounit_hom] at h
  change 𝟙 N.X ≫ ((ringSheafScalarEquivalence e).counitIso.inv.app N).hom = 𝟙 N.X at h
  exact (Category.id_comp _).symm.trans h

private theorem abZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  have := (abelian_closed_support i j hU).2 F hj
  exact ((lowerStar Ab.{u + 1} i).map_isZero hi).of_iso
    (asIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F))
private theorem modCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStar Ab.{u + 1} i).obj B)) :
    IsIso ((ringSheafAdjunction i B).counit.app G) := by
  have h : IsIso ((Mod.forget _).map ((ringSheafAdjunction i B).counit.app G)) := by
    change IsIso (((ringSheafAdjunction i B).counit.app G).hom)
    rw [Adjunction.mapModAdjunction_counit_app_hom]
    have := abelian_closed_counit i
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem modZero
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStar Ab.{u + 1} i).obj B)) :
    IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G)) := by
  have hij : Disjoint (Set.range i.base) (Set.range j.base) := by
    rw [hU]
    exact disjoint_compl_right
  have h := (isZero_openImmersionRestriction_lowerStar Ab.{u + 1} i j
    (Set.disjoint_iff_inter_eq_empty.1 hij) G.X).of_iso
      ((upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    (hi : IsZero ((ringSheafInverseImage i B).obj M))
    (hj : IsZero ((ringSheafInverseImage j B).obj M)) : IsZero M := by
  have h := abZeroDetect i j hU M.X ((Mod.forget _).map_isZero hi)
    ((Mod.forget _).map_isZero hj)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modIsoDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B} (φ : M ⟶ N)
    [IsIso ((ringSheafInverseImage i B).map φ)]
    [IsIso ((ringSheafInverseImage j B).map φ)] : IsIso φ := by
  have hker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (kernel φ)) := fun f _ ↦
    (isZero_kernel_of_mono ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (cokernel φ)) := fun f _ ↦
    (isZero_cokernel_of_epi ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (modZeroDetect i j hU B _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (modZeroDetect i j hU B _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ


private theorem localization
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (_hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    PreservesFiniteColimits (ringSheafDirectImage i B) ∧
    (∀ G, IsIso ((ringSheafAdjunction i B).counit.app G)) ∧
    (∀ G, IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G))) ∧
    (∀ M, Mono ((ringSheafOpenAdjunction j B).counit.app M) ∧
      Epi ((ringSheafAdjunction i B).unit.app M) ∧
      (ComposableArrows.mk₂ ((ringSheafOpenAdjunction j B).counit.app M)
        ((ringSheafAdjunction i B).unit.app M)).Exact) := by
  have hc := modCounit i B
  have hz := modZero i j _hU B
  let a := ringSheafOpenAdjunction j B
  let b := ringSheafAdjunction i B
  have hu (N) : IsIso (a.unit.app N) := by
    have h : IsIso ((Mod.forget _).map (a.unit.app N)) := by
      change IsIso ((a.unit.app N).hom)
      simp only [a, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv_unit_app]
      change IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv _ _
        (𝟙 ((openImmersionLowerShriek Ab.{u + 1} j).obj N.X)))
      rw [Adjunction.homEquiv_id]
      have := Adjunction.unit_isIso_of_L_fully_faithful
        (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j)
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hd : JointlyReflectIsomorphisms
      (pairFunctor (ringSheafInverseImage j B) (ringSheafInverseImage i B)) :=
    jointlyReflectIsomorphisms_pairFunctor _ _ fun _ _ φ hj hi ↦ by
      have := hj
      have := hi
      exact modIsoDetect i j _hU B φ
  have hseq (M) : Mono (a.counit.app M) ∧ Epi (b.unit.app M) ∧
      (ComposableArrows.mk₂ (a.counit.app M) (b.unit.app M)).Exact := by
    have hzi (N) : IsZero ((ringSheafInverseImage i B).obj
        ((ringSheafOpenExtension j B).obj N)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply (b.homEquiv _ _).injective
      apply (a.homEquiv _ _).injective
      exact (hz _).eq_of_tgt _ _
    have hzero : a.counit.app M ≫ b.unit.app M = 0 := by
      apply (a.homEquiv _ _).injective
      exact (hz _).eq_of_tgt _ _
    let Q := ShortComplex.mk (a.counit.app M) (b.unit.app M) hzero
    have hQ : Q.ShortExact := by
      rw [hd.shortExact_iff]
      rintro (_ | _)
      · have hgi : IsIso ((ringSheafInverseImage i B).map (b.unit.app M)) := by
          have h := b.left_triangle_components M
          rw [← IsIso.inv_eq_of_inv_hom_id h]
          have := hc ((ringSheafInverseImage i B).obj M)
          infer_instance
        have : IsIso ((Q.map (ringSheafInverseImage i B)).g) := hgi
        have hfi : (Q.map (ringSheafInverseImage i B)).f = 0 := (hzi _).eq_of_src _ _
        exact
          { exact := (ShortComplex.exact_iff_mono _ hfi).2 inferInstance
            mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
            epi_g := by
              change Epi ((ringSheafInverseImage i B).map (b.unit.app M))
              infer_instance }
      · have hfj : IsIso ((ringSheafInverseImage j B).map (a.counit.app M)) := by
          have h := a.right_triangle_components (Y := M)
          rw [← IsIso.inv_eq_of_hom_inv_id h]
          have := hu ((ringSheafInverseImage j B).obj M)
          infer_instance
        have : IsIso ((Q.map (ringSheafInverseImage j B)).f) := hfj
        have hgj : (Q.map (ringSheafInverseImage j B)).g = 0 := (hz _).eq_of_tgt _ _
        exact
          { exact := (ShortComplex.exact_iff_epi _ hgj).2 inferInstance
            mono_f := by
              change Mono ((ringSheafInverseImage j B).map (a.counit.app M))
              infer_instance
            epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }
    exact ⟨hQ.mono_f, hQ.epi_g, hQ.exact.exact_toComposableArrows⟩
  refine ⟨?_, hc, hz, hseq⟩
  have hEpi {G H} (φ : G ⟶ H) [Epi φ] : Epi ((ringSheafDirectImage i B).map φ) := by
    have hε : (ringSheafInverseImage i B).map ((ringSheafDirectImage i B).map φ) =
        b.counit.app G ≫ φ ≫ inv (b.counit.app H) := by
      have := hc H
      rw [← Category.assoc, IsIso.eq_comp_inv]
      exact b.counit.naturality φ
    have : Epi ((ringSheafInverseImage i B).map ((ringSheafDirectImage i B).map φ)) := by
      have := hc G
      rw [hε]
      infer_instance
    refine Preadditive.epi_of_isZero_cokernel _
      (modZeroDetect i j _hU B _ ?_ ?_)
    · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)
    · exact (IsZero.of_epi (cokernel.π _) (hz H)).of_iso (PreservesCokernel.iso _ _)
  have : (ringSheafDirectImage i B).PreservesEpimorphisms := ⟨fun φ _ ↦ hEpi φ⟩
  have : (ringSheafDirectImage i B).IsRightAdjoint := b.isRightAdjoint
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (ringSheafDirectImage i B)
  exact Functor.preservesFiniteColimits_of_preservesHomology _


/-- Canonical open/closed localization for arbitrary, possibly noncommutative, ring
objects on the small pro-etale site. There is no qcqs or Noetherian hypothesis on X.

Source: Stacks Project, Pro-etale Cohomology, Tags 09AA, 09BM, 09BN and 09AH;
Modules on Sites, Tag 0F6Z (blueprint: lem-sfb-noncommutative-ringed-open-closed).

Proof, following the eight steps of the DAG node:
1. The sheaf tensor is additive and right exact. The generic module-object results
   `lem-sfb-modobj-abelian`, `lem-sfb-modobj-kernels`, `lem-sfb-modobj-cokernels` and
   `lem-sfb-modobj-forget-faithful` give abelian module categories, kernels and cokernels
   on carriers, and faithful forgetful functors reflecting zero objects and isomorphisms.
2. Apply `lem-weil-pbc-proetale-ringed-open-closed` at the constant integer ring.
   Modules over the initial ring sheaf are abelian sheaves: the integer action is forced
   by repeated addition and negation, locally also for locally constant integer sections.
   Both inverse images are sheafified left Kan extensions along scheme base change;
   both direct images are precomposition. Extension by zero is the same sheafified
   sum over arrows into the open. These identifications carry the Hom adjunctions and
   their units and counits to the recorded abelian operations. Tags 09AA, 09BM, 09BN,
   09AH and 0F6Z thus give exactness, both vanishings and the abelian exact sequence.
3. `def-sfb-modobj-transport-adjunction` lifts inverse/direct image and their actual
   units and counits. The open projection formula makes `mapModLeftAdjunction` lift
   extension/restriction and its actual unit and counit. All carriers are unchanged.
4. Apply `det-prop-sfb-module-pullback-exact-lifted` to the four exact abelian functors.
   Direct image along the open is additive by its sectionwise formula and faithfulness.
5. The abstract abelian identifications of closed restriction/direct image and open
   restriction/extension imply invertibility of their actual counit and unit by
   `lem-sfb-adjunction-abstract-iso-unit-counit`. Reflect isomorphisms through forgetting.
   The vanishings and the actual counit-unit short exact sequence lift from carriers;
   naturality is the naturality of these specified adjunction transformations.
6. On an object W over V, open restriction of open direct image evaluates at
   W times_X V, canonically W since j is a monomorphism. This gives a natural abstract
   isomorphism, hence the actual open counit is invertible by the same adjunction lemma.
   The triangle identity then makes j-star of the actual open unit invertible.
7. If both restrictions vanish, the outside terms of the localization sequence vanish,
   so the middle object is zero. Apply exact restriction to the kernel of a map whose
   restrictions are monic. Its restrictions vanish, hence its kernel vanishes and it
   is monic. This proves joint zero detection and reflection of monomorphisms.
8. Restriction along a ring-object isomorphism and its inverse are inverse equivalences
   by `Mod.comapComp`, `Mod.comapCongr`, and `Mod.comapId`; no commutative scalar extension
   is used. Compose the three adjunctions with their equivalence adjunctions. The new
   units and counits insert only these identity-carrier comparisons, so they still forget
   to the abelian units and counits. Equivalences
   preserve and reflect exactness, zero objects, monomorphisms and isomorphisms, proving
   every assertion for the transported functors and the transported actual maps.
-/
theorem noncommutative_ringSheaf_open_closed
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (_hV : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenClosedAssertions
      (ringSheafInverseImage i B) (ringSheafDirectImage i B)
      (ringSheafInverseImage j B) (ringSheafDirectImage j B) (ringSheafOpenExtension j B)
      (ringSheafAdjunction i B) (ringSheafAdjunction j B) (ringSheafOpenAdjunction j B) ∧
    (∀ M, ((ringSheafAdjunction i B).unit.app M).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X) ∧
    (∀ N, ((ringSheafAdjunction i B).counit.app N).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app N.X) ∧
    (∀ M, ((ringSheafAdjunction j B).unit.app M).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X) ∧
    (∀ N, ((ringSheafAdjunction j B).counit.app N).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} j).counit.app N.X) ∧
    (∀ N, ((ringSheafOpenAdjunction j B).unit.app N).hom =
      (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app N.X) ∧
    (∀ M, ((ringSheafOpenAdjunction j B).counit.app M).hom =
      (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).counit.app M.X) ∧
    (∀ (RZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj RZ]
      (RV : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) [MonObj RV]
      (eZ : RZ ≅ (upperStar Ab.{u + 1} i).obj B) [IsMonHom eZ.hom]
      (eV : RV ≅ (upperStar Ab.{u + 1} j).obj B) [IsMonHom eV.hom],
      ringSheafOpenClosedAssertions
        (ringSheafInverseImage i B ⋙ (ringSheafScalarEquivalence eZ).functor)
        ((ringSheafScalarEquivalence eZ).inverse ⋙ ringSheafDirectImage i B)
        (ringSheafInverseImage j B ⋙ (ringSheafScalarEquivalence eV).functor)
        ((ringSheafScalarEquivalence eV).inverse ⋙ ringSheafDirectImage j B)
        ((ringSheafScalarEquivalence eV).inverse ⋙ ringSheafOpenExtension j B)
        ((ringSheafAdjunction i B).comp (ringSheafScalarEquivalence eZ).toAdjunction)
        ((ringSheafAdjunction j B).comp (ringSheafScalarEquivalence eV).toAdjunction)
        ((ringSheafScalarEquivalence eV).symm.toAdjunction.comp
          (ringSheafOpenAdjunction j B)) ∧
      (∀ M, (((ringSheafAdjunction i B).comp
          (ringSheafScalarEquivalence eZ).toAdjunction).unit.app M).hom =
        (upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X) ∧
      (∀ N, (((ringSheafAdjunction i B).comp
          (ringSheafScalarEquivalence eZ).toAdjunction).counit.app N).hom =
        (upperStarLowerStarAdjunction Ab.{u + 1} i).counit.app N.X) ∧
      (∀ M, (((ringSheafAdjunction j B).comp
          (ringSheafScalarEquivalence eV).toAdjunction).unit.app M).hom =
        (upperStarLowerStarAdjunction Ab.{u + 1} j).unit.app M.X) ∧
      (∀ N, (((ringSheafAdjunction j B).comp
          (ringSheafScalarEquivalence eV).toAdjunction).counit.app N).hom =
        (upperStarLowerStarAdjunction Ab.{u + 1} j).counit.app N.X) ∧
      (∀ N, (((ringSheafScalarEquivalence eV).symm.toAdjunction.comp
          (ringSheafOpenAdjunction j B)).unit.app N).hom =
        (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app N.X) ∧
      (∀ M, (((ringSheafScalarEquivalence eV).symm.toAdjunction.comp
          (ringSheafOpenAdjunction j B)).counit.app M).hom =
        (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).counit.app M.X)) := by
  have hcore : ringSheafOpenClosedAssertions
      (ringSheafInverseImage i B) (ringSheafDirectImage i B)
      (ringSheafInverseImage j B) (ringSheafDirectImage j B) (ringSheafOpenExtension j B)
      (ringSheafAdjunction i B) (ringSheafAdjunction j B) (ringSheafOpenAdjunction j B) := by
    obtain ⟨hcol, hc, hz, hs⟩ := localization i j _hV B
    have := hcol
    have := abelianOpenCounit j
    have : (ringSheafDirectImage i B).IsRightAdjoint := (ringSheafAdjunction i B).isRightAdjoint
    have : (ringSheafOpenExtension j B).IsLeftAdjoint :=
      (ringSheafOpenAdjunction j B).isLeftAdjoint
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, hc, ?_, ?_, hz, ?_, hs, ?_, ?_, ?_⟩
    · intro N
      have h : IsIso ((Mod.forget _).map ((ringSheafAdjunction j B).counit.app N)) := by
        change IsIso (((ringSheafAdjunction j B).counit.app N).hom)
        rw [Adjunction.mapModAdjunction_counit_app_hom]
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    · intro N
      have h : IsIso ((Mod.forget _).map ((ringSheafOpenAdjunction j B).unit.app N)) := by
        change IsIso (((ringSheafOpenAdjunction j B).unit.app N).hom)
        simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
          Adjunction.mkOfHomEquiv_unit_app]
        change IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
          ).homEquiv _ _ (𝟙 ((openImmersionLowerShriek Ab.{u + 1} j).obj N.X)))
        rw [Adjunction.homEquiv_id]
        have := (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
          ).unit_isIso_of_L_fully_faithful
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    · intro N
      apply (IsZero.iff_id_eq_zero _).2
      apply ((ringSheafAdjunction i B).homEquiv _ _).injective
      apply ((ringSheafOpenAdjunction j B).homEquiv _ _).injective
      exact (hz _).eq_of_tgt _ _
    · intro M
      have h := (ringSheafAdjunction j B).left_triangle_components M
      have hcj : IsIso ((ringSheafAdjunction j B).counit.app
          ((ringSheafInverseImage j B).obj M)) := by
        have hi : IsIso ((Mod.forget _).map ((ringSheafAdjunction j B).counit.app
            ((ringSheafInverseImage j B).obj M))) := by
          change IsIso (((ringSheafAdjunction j B).counit.app _).hom)
          rw [Adjunction.mapModAdjunction_counit_app_hom]
          infer_instance
        exact isIso_of_reflects_iso _ (Mod.forget _)
      rw [← IsIso.inv_eq_of_inv_hom_id h]
      infer_instance
    · intro M hj hi
      exact modZeroDetect i j _hV B M hi hj
    · intro M N f hj hi
      have := hj
      have := hi
      apply Preadditive.mono_of_isZero_kernel
      apply modZeroDetect i j _hV B
      · exact (isZero_kernel_of_mono ((ringSheafInverseImage i B).map f)).of_iso
          (PreservesKernel.iso _ f)
      · exact (isZero_kernel_of_mono ((ringSheafInverseImage j B).map f)).of_iso
          (PreservesKernel.iso _ f)
  refine ⟨hcore, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M
    exact Adjunction.mapModAdjunction_unit_app_hom _ _ _
  · intro N
    exact Adjunction.mapModAdjunction_counit_app_hom _ _ _
  · intro M
    exact Adjunction.mapModAdjunction_unit_app_hom _ _ _
  · intro N
    exact Adjunction.mapModAdjunction_counit_app_hom _ _ _
  · intro N
    simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
      Adjunction.mkOfHomEquiv_unit_app]
    exact (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv_id N.X
  · intro M
    simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
      Adjunction.mkOfHomEquiv_counit_app]
    exact (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv_symm_id M.X
  · intro RZ _ RV _ eZ _ eV _
    have : (ringSheafScalarEquivalence eZ).functor.Additive :=
      inferInstanceAs (Mod.comap eZ.hom).Additive
    have : (ringSheafScalarEquivalence eV).functor.Additive :=
      inferInstanceAs (Mod.comap eV.hom).Additive
    refine ⟨transportAssertions _ _ _ _ _ _ _ _
      (ringSheafScalarEquivalence eZ) (ringSheafScalarEquivalence eV) hcore,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro M
      rw [Adjunction.comp_unit_app]
      change ((ringSheafAdjunction i B).unit.app M).hom ≫
        (lowerStar Ab.{u + 1} i).map
          (((ringSheafScalarEquivalence eZ).unitIso.hom.app _).hom) = _
      rw [scalarUnit_hom]
      change ((ringSheafAdjunction i B).unit.app M).hom ≫
        (lowerStar Ab.{u + 1} i).map (𝟙 ((upperStar Ab.{u + 1} i).obj M.X)) = _
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact Adjunction.mapModAdjunction_unit_app_hom _ _ _
    · intro N
      rw [Adjunction.comp_counit_app]
      change ((ringSheafAdjunction i B).counit.app _).hom ≫
        ((ringSheafScalarEquivalence eZ).counitIso.hom.app N).hom = _
      rw [scalarCounit_hom]
      change ((ringSheafAdjunction i B).counit.app
        ((Mod.comap eZ.inv).obj N)).hom ≫ 𝟙 N.X = _
      erw [Category.comp_id]
      exact Adjunction.mapModAdjunction_counit_app_hom _ _ _
    · intro M
      rw [Adjunction.comp_unit_app]
      change ((ringSheafAdjunction j B).unit.app M).hom ≫
        (lowerStar Ab.{u + 1} j).map
          (((ringSheafScalarEquivalence eV).unitIso.hom.app _).hom) = _
      rw [scalarUnit_hom]
      change ((ringSheafAdjunction j B).unit.app M).hom ≫
        (lowerStar Ab.{u + 1} j).map (𝟙 ((upperStar Ab.{u + 1} j).obj M.X)) = _
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact Adjunction.mapModAdjunction_unit_app_hom _ _ _
    · intro N
      rw [Adjunction.comp_counit_app]
      change ((ringSheafAdjunction j B).counit.app _).hom ≫
        ((ringSheafScalarEquivalence eV).counitIso.hom.app N).hom = _
      rw [scalarCounit_hom]
      change ((ringSheafAdjunction j B).counit.app
        ((Mod.comap eV.inv).obj N)).hom ≫ 𝟙 N.X = _
      erw [Category.comp_id]
      exact Adjunction.mapModAdjunction_counit_app_hom _ _ _
    · intro N
      rw [Adjunction.comp_unit_app]
      change ((ringSheafScalarEquivalence eV).counitIso.inv.app N).hom ≫
        ((ringSheafOpenAdjunction j B).unit.app _).hom = _
      rw [scalarCounitInv_hom, Category.id_comp]
      simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv_unit_app]
      exact (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv_id N.X
    · intro M
      rw [Adjunction.comp_counit_app]
      change (openImmersionLowerShriek Ab.{u + 1} j).map
        (((ringSheafScalarEquivalence eV).unitIso.inv.app _).hom) ≫
        ((ringSheafOpenAdjunction j B).counit.app M).hom = _
      rw [scalarUnitInv_hom]
      change (openImmersionLowerShriek Ab.{u + 1} j).map
        (𝟙 ((upperStar Ab.{u + 1} j).obj M.X)) ≫
        ((ringSheafOpenAdjunction j B).counit.app M).hom = _
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv_counit_app]
      exact (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv_symm_id M.X

end AlgebraicGeometry.ProEtale
