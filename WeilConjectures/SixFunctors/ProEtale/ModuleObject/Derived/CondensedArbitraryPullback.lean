/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullbackDefinitions

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.InverseImageModuleFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Arbitrary pullback of condensed constructible complexes

Source: blueprint latest, sec-six-functors-basics/sk-prop-proper-base-change-unbounded,
opening inverse-image paragraph and sk-prop-proper-base-change-unbounded-pullback.proof.md
(blueprint: lem-zl-condensed-arbitrary-pullback).

The ambient categories are ordinary unbounded derived categories of internal modules over
`condensedRingObj Λ T`. Constructibility uses finite constant scalar models, and the
algebraic-closure coefficient has finite-subextension-valued sections. Both schemes are
separated and of finite type over `k`; the map between them is any scheme morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] AlgebraicGeometry.ProEtale.unboundedLocalizingPullbackCommShift

private theorem condensed_coproduct_small_support.{w, v, u₂, v₂}
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [LocallySmall.{w} D]
    {I : Type v} (K : I → D) (t : Cofan K) (ht : IsColimit t) :
    Small.{w} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

/-- Shrinking nonzero support extends preservation to every indexing universe. -/
private theorem condensed_preservesCoproducts_of_small.{w, v, u₁, u₂, v₁, v₂}
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [LocallySmall.{w} D]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (c : D ⥤ C) [c.PreservesZeroMorphisms]
    (hsmall : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) c)
    (I : Type v) : PreservesColimitsOfShape (Discrete I) c := by
  classical
  have hpres (K : I → D) : PreservesColimit (Discrete.functor K) c := by
    refine ⟨fun {t} ht ↦ ⟨?_⟩⟩
    let t₀ : Cofan K := t
    have hsupport : Small.{w} {i // ¬ IsZero (K i)} := condensed_coproduct_small_support K t₀ ht
    let J := {i // ¬ IsZero (K i)}
    have : PreservesColimitsOfShape (Discrete (Shrink.{w} J)) c := hsmall _
    have : PreservesColimitsOfShape (Discrete J) c :=
      preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink J)).symm c
    let U : J → D := fun i ↦ K i.val
    let r : Cofan U := Cofan.mk t.pt (fun i ↦ t₀.inj i.val)
    have hr : IsColimit r := by
      refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s i
        obtain ⟨i, hi⟩ := i
        change t.ι.app (Discrete.mk i) ≫ _ = _
        rw [ht.fac]
        simp only [Cofan.mk_ι_app, dif_pos hi]
      · intro s m hm
        apply ht.hom_ext
        intro ⟨i⟩
        rw [ht.fac]
        by_cases hi : ¬ IsZero (K i)
        · simpa only [r, cofan_mk_inj, t₀, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    let q : Cofan (fun i ↦ c.obj (U i)) :=
      Cofan.mk (c.obj t.pt) (fun i ↦ c.map (t₀.inj i.val))
    have hq : IsColimit q := isColimitCofanMkObjOfIsColimit c U _ hr
    refine { desc := fun s ↦ hq.desc (Cofan.mk s.pt
        (fun i ↦ s.ι.app (Discrete.mk i.val))), fac := ?_, uniq := ?_ }
    · intro s ⟨i⟩
      by_cases hi : ¬ IsZero (K i)
      · exact hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk ⟨i, hi⟩)
      · exact (c.map_isZero (not_not.mp hi)).eq_of_src _ _
    · intro s m hm
      apply Cofan.IsColimit.hom_ext hq
      intro i
      exact (hm (Discrete.mk i.val)).trans
        (hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk i)).symm
  exact preservesColimitsOfShape_of_discrete c

private theorem condensed_pullback_exact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (upperStar Λ g).leftDerivedFunctor.IsTriangulated := by
  let : (upperStar Λ g).leftDerivedFunctor.CommShift ℤ :=
    unboundedLocalizingPullbackCommShift Λ g
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

private theorem condensed_pullback_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ f).PreservesFlat := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : upperStar Λ f ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ ObjectProperty.prop_of_iso ObjectProperty.flat
    (e.symm.app _) (h.flat_obj hM)⟩

private theorem condensed_pullback_tor_interval
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    {a b : ℤ} (hK : DerivedCategory.torAmplitudeIn _ a b K) :
    DerivedCategory.torAmplitudeIn _ a b
      ((upperStar Λ g).leftDerivedFunctor.obj K) := by
  let F := upperStar Λ g
  obtain ⟨P, hPa, hPb, hP, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hK
  let P' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y')) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj P
  have : P'.IsStrictlyGE a := inferInstance
  have : P'.IsStrictlyLE b := inferInstance
  have hflat := condensed_pullback_flat Λ g
  have hP' : ∀ n, ObjectProperty.flat (P'.X n) :=
    fun n ↦ hflat.flat_obj (hP n)
  refine (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso ?_
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat P' a b hP')
  exact (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm.app K

private theorem condensed_pullback_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((upperStar Λ g).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hX, if_pos hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  let T := S.pullback g
  refine ⟨T, fun i ↦ ?_⟩
  let q : T.domain i ⟶ S.domain i := pullback.fst (S.immersion i) g
  have comm : q ≫ S.immersion i = T.immersion i ≫ g := pullback.condition
  have h := pullback_finiteConstantLocalModel Λ q _ (hS i)
  let e := ((upperStarComp Λ (T.immersion i) g).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (upperStar Λ f).obj M)
      comm.symm) ≪≫
    (upperStarComp Λ q (S.immersion i)).app M
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun j ↦ by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
    exact ⟨P, hP, ⟨(upperStar Λ (U.f j)).mapIso e ≪≫ eP⟩⟩⟩

private theorem condensed_pullback_bounded_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (h : ∀ M, IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((upperStar Λ g).obj M))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hK : constantModelBoundedConstructible Λ Y K) :
    constantModelBoundedConstructible Λ Y'
      ((upperStar Λ g).leftDerivedFunctor.obj K) := by
  let F := upperStar Λ g
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ g
  have hi := (constantModelConstructibleFiniteTor_wellDefined Λ Y').1
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.symm.app K)
      (F.bounded_mapDerivedCategory_obj hK.1)
  · exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Y')
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso (e.symm.app K)) (h _ (hK.2 n))

set_option maxHeartbeats 200000 in
-- The full-subcategory and universe transports require explicit structural comparisons.
private theorem condensed_pullback_of_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (h : ∀ M, IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((upperStar Λ g).obj M)) :
    Nonempty (UnboundedLocalizingPullback Λ g) := by
  let F := (upperStar Λ g).leftDerivedFunctor
  let G : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :=
    constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _
  let G' : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))) :=
    constantModelBoundedConstructible Λ Y' ⊓ DerivedCategory.finiteTorAmplitude _
  obtain ⟨hsums, _, _, hs, _, _, _, _⟩ := localizingClosure_exists Λ Y G
  obtain ⟨hsums', _, _, ht, hgen, _, _, _⟩ := localizingClosure_exists Λ Y' G'
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) := hsums
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))) := hsums'
  let : F.IsTriangulated := condensed_pullback_exact Λ g
  let : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I) F := fun I ↦
    (derivedUpperStarLowerStarAdjunction Λ g).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  let : (localizingClosureProEtale Λ Y).IsTriangulated := hs.1
  let : (localizingClosureProEtale Λ Y').IsTriangulated := ht.1
  let : (localizingClosureProEtale Λ Y').IsClosedUnderIsomorphisms := ht.2.1
  have hc : ∀ K, G K → G' (F.obj K) := fun K hK ↦ by
    obtain ⟨a, b, hKtor⟩ := hK.2
    exact ⟨condensed_pullback_bounded_constructible Λ g h K hK.1,
      ⟨a, b, condensed_pullback_tor_interval Λ g K hKtor⟩⟩
  have hm : ∀ K, localizingClosureProEtale Λ Y K →
      localizingClosureProEtale Λ Y' (F.obj K) := by
    intro K hK
    apply hK ((localizingClosureProEtale Λ Y').inverseImage F)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hmem
      let := hD
      apply ObjectProperty.prop_of_iso (localizingClosureProEtale Λ Y')
        (preservesColimitIso F D).symm
      exact ht.2.2 (D ⋙ F) inferInstance hmem
    · exact fun L hL ↦ hgen _ (hc L hL)
  let hm' := fun K : (localizingClosureProEtale Λ Y).FullSubcategory ↦ hm K.obj K.property
  let R := (localizingClosureProEtale Λ Y').lift
    ((localizingClosureProEtale Λ Y).ι ⋙ F) hm'
  have hrsmall (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) R := by
    let : (localizingClosureProEtale Λ Y).IsClosedUnderIsomorphisms := hs.2.1
    let : (localizingClosureProEtale Λ Y).IsClosedUnderColimitsOfShape
        (Discrete (ULift.{u + 2} I)) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
        rintro _ ⟨D, hD⟩
        exact hs.2.2 D inferInstance (fun i ↦ hD (Discrete.mk i)))
    let : (localizingClosureProEtale Λ Y).IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence Equiv.ulift)
    have : PreservesColimitsOfShape (Discrete I) F :=
      (derivedUpperStarLowerStarAdjunction Λ g).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimitsOfShape (Discrete I)
        (R ⋙ (localizingClosureProEtale Λ Y').ι) :=
      preservesColimitsOfShape_of_natIso
        ((localizingClosureProEtale Λ Y').liftCompιIso _ hm').symm
    exact preservesColimitsOfShape_of_reflects_of_preserves R
      (localizingClosureProEtale Λ Y').ι
  refine ⟨{ exact := inferInstance
            sums := fun I ↦ inferInstance
            constructible := hc
            localizing := hm'
            restrictionExact := ?_
            restrictionSums := ?_ }⟩
  · infer_instance
  · exact fun I ↦ condensed_preservesCoproducts_of_small R hrsmall I


/-- Arbitrary scheme pullback preserves constructible finite-Tor objects and their localizing
closures, with every specified cohomological and Tor interval. The proposition
`UnboundedLocalizingPullback` uses the canonical shift structure transported from termwise
pullback along `leftDerivedUpperStarIsoMapDerivedCategory`; its restriction is the actual
full-subcategory lift, with inherited triangulations and coproducts.

Source: blueprint latest, proper-base-change-unbounded opening inverse-image paragraph,
expanded pullback proof, and the arbitrary-map requirement in sk-thm-sf-comp-composition (2)
(blueprint: lem-zl-condensed-arbitrary-pullback).

Proof:
1. Abelian sheaves on the essentially small pro-etale site are closed symmetric monoidal
   Grothendieck abelian with additive tensor and functorial flat covers, by the sheaf tensor
   and flat-resolution theorems. The internal-module Grothendieck and flat-resolution
   theorems and relative internal Hom give the same properties for modules over Λ_T.
2. The module inverse image is exact and additive. The exact-derived comparison identifies
   its total left derived functor with termwise D(a*), canonically. The exact-derived
   factorization is triangulated. The total derived adjunction and left-adjoint colimit
   theorem give all small coproducts; localizingClosure_exists supplies their existence.
3. The exact-derived cohomology comparison identifies H^q(La*K) with a*H^q(K). Thus zero
   cohomology outside any specified finite interval remains zero after pullback.
4. Pull back a finite constructible stratification. Its locally closed strata are
   constructible since the target scheme is Noetherian. Pullback composition identifies
   the restrictions, and pullback_finiteConstantLocalModel preserves each witnessing model
   on the base-changed cover. Apply step 3 to the finitely many nonzero cohomology sheaves.
5. The bounded-flat-model theorem represents a Tor-[r,s] object by a flat complex supported
   in [r,s]. The canonical coefficient comparison is invertible for every scheme map.
   inverseImageModule_preservesFlat, together with extendScalarsIsoComapInv, preserves its
   flat terms. Exact-derived comparison computes the pullback by this pulled-back complex.
6. A bounded-above flat complex is K-flat. Tensor against any target module in degree zero
   is computed by its ordinary total tensor, still supported in [r,s]. This tests every
   target module, and therefore preserves the same Tor interval. With step 4 it preserves
   Dctf. The categorical hypotheses needed here were verified in step 1.
7. The inverse image of the target localizing closure is replete, triangulated, and closed
   under ambient small coproducts by step 2, and contains the generators by steps 4--6.
   Minimality gives the localizing inclusion. Its canonical full-subcategory lift inherits
   exactness and coproduct preservation. No step uses compatibility with the k-structures.
-/
theorem condensedArbitraryPullback
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsAdmissibleCoefficient Λ)
    {T' T : Scheme.{u}} [T'.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T' ↘ Spec (.of k))] [QuasiCompact (T' ↘ Spec (.of k))]
    [IsSeparated (T' ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (a : T' ⟶ T) :
    Nonempty (moduleObjectDerivedPullback Λ a ≅ (upperStar Λ a).mapDerivedCategory) ∧
    UnboundedLocalizingPullback Λ a ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
      (r s : ℤ), constantModelBoundedConstructible Λ T K →
      (DerivedCategory.homologyConcentratedIn r s K →
        DerivedCategory.homologyConcentratedIn r s ((moduleObjectDerivedPullback Λ a).obj K)) ∧
      (DerivedCategory.torAmplitudeIn _ r s K →
        DerivedCategory.torAmplitudeIn _ r s ((moduleObjectDerivedPullback Λ a).obj K))) := by
  have _ := hpl
  have _ := hΛ
  have hT : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (T ↘ Spec (.of k))
  have hT' : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace
    (T' ↘ Spec (.of k))
  let : CompactSpace T := hT
  let : CompactSpace T' := hT'
  have hqsT : QuasiSeparatedSpace T :=
    (quasiSeparated_iff_quasiSeparatedSpace (T ↘ Spec (.of k))).mp inferInstance
  have hqsT' : QuasiSeparatedSpace T' :=
    (quasiSeparated_iff_quasiSeparatedSpace (T' ↘ Spec (.of k))).mp inferInstance
  let : QuasiSeparatedSpace T := hqsT
  let : QuasiSeparatedSpace T' := hqsT'
  have hconstructible : ∀ M, IsConstantModelConstructible Λ T M →
      IsConstantModelConstructible Λ T' ((upperStar Λ a).obj M) :=
    fun M hM ↦ condensed_pullback_constructible Λ a M hM
  obtain ⟨hlocal⟩ := condensed_pullback_of_constructible Λ a hconstructible
  refine ⟨⟨leftDerivedUpperStarIsoMapDerivedCategory Λ a⟩, hlocal, ?_⟩
  intro K r s hK
  constructor
  · intro hH
    let F := upperStar Λ a
    have hmap : DerivedCategory.homologyConcentratedIn r s
        (F.mapDerivedCategory.obj K) :=
      F.homologyConcentratedIn_mapDerivedCategory_obj hH
    exact (DerivedCategory.homologyConcentratedIn r s).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ a).symm.app K) hmap
  · intro hTor
    exact condensed_pullback_tor_interval Λ a K hTor

end AlgebraicGeometry.ProEtale.CondensedRing
