/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.NativeAdicEncodingCore
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.WeilSheaf.MiddleExtension

/-! # Full faithfulness of condensed lisse restriction on geometric open lines

Source: Stacks Project, Tag 0BQM; latest blueprint, rem-dl-a1-conventions,
proof step 5 of lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-condensed-lisse-restriction-fully-faithful).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

private noncomputable def encodedRegularIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (NativeEncoding.encoding l T).obj (Mod.regular (adicConstantSheaf l T)) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T) :=
  (Mod.comap (NativeEncoding.coefficientIso l T).hom).mapIso
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
      (Mod.regularIsoComapRegular (NativeEncoding.coefficientIso l T).hom).symm

private noncomputable def encodedFreeIso (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (r : ℕ) :
    (NativeEncoding.encoding l T).obj (Mod.finiteFree (adicConstantSheaf l T) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) T) r :=
  (NativeEncoding.encoding l T).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ encodedRegularIso l T

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem encoded_lisse_iff (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (M : AdicSheaf l T) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      ((NativeEncoding.encoding l T).obj M) ↔ IsAdicLisseSheaf M := by
  classical
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U.presieve₀, U.mem₀, ?_⟩
    rintro V f ⟨i⟩
    obtain ⟨n, ⟨e⟩⟩ := hU i
    refine ⟨n, ⟨(NativeEncoding.encoding l (U.X i)).preimageIso ?_⟩⟩
    exact (NativeEncoding.pullComparison l (U.f i)).app M ≪≫ e ≪≫
      (encodedFreeIso l (U.X i) n).symm
  · rintro ⟨R, hR, H⟩
    obtain ⟨V, hV⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
    let U := V.restrictIndexOfSmall.{u}
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨n, ⟨e⟩⟩ := H (U.f i) (by
      rw [hV]
      exact V.presieve₀_f (Precoverage.ZeroHypercover.Small.restrictFun V i))
    exact ⟨n, ⟨(NativeEncoding.pullComparison l (U.f i)).symm.app M ≪≫
      (NativeEncoding.encoding l (U.X i)).mapIso e ≪≫ encodedFreeIso l (U.X i) n⟩⟩

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem lisse_of_iso (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)}
    (e : M ≅ N) (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨f⟩⟩ := hU i
  exact ⟨n, ⟨((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (U.f i)).mapIso e).symm ≪≫ f⟩⟩

set_option maxHeartbeats 0 in
-- Canonical sheaf-module categories require a larger elaboration budget.
private theorem dense_open_map_bijective (l : ℕ) [Fact l.Prime]
    {U C : Scheme.{u}} (hC : ∀ x : C, IsRegularLocalRing (C.presheaf.stalk x))
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j))
    (L M : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) C))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    Function.Bijective ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).map :
      (L ⟶ M) → _) := by
  let E := NativeEncoding.equivalence l C
  let E' := NativeEncoding.equivalence l U
  let J := adicUpperStar l j
  let J' := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j
  let c : J ⋙ E'.functor ≅ E.functor ⋙ J' := NativeEncoding.pullComparison l j
  let A := E.inverse.obj L
  let B := E.inverse.obj M
  let a : E.functor.obj A ≅ L := E.counitIso.app L
  let b : E.functor.obj B ≅ M := E.counitIso.app M
  have hB : IsAdicLisseSheaf B := (encoded_lisse_iff l C B).mp
    (lisse_of_iso l b.symm hM)
  have hJ := hB.adicUpperStar_map_bijective hC j hj A
  let e : (A ⟶ B) ≃ (L ⟶ M) :=
    (E.fullyFaithfulFunctor.homEquiv).trans
      { toFun f := a.inv ≫ f ≫ b.hom
        invFun f := a.hom ≫ f ≫ b.inv
        left_inv f := by simp [Category.assoc]
        right_inv f := by simp [Category.assoc] }
  let a' : E'.functor.obj (J.obj A) ≅ J'.obj L := c.app A ≪≫ J'.mapIso a
  let b' : E'.functor.obj (J.obj B) ≅ J'.obj M := c.app B ≪≫ J'.mapIso b
  let e' : (J.obj A ⟶ J.obj B) ≃ (J'.obj L ⟶ J'.obj M) :=
    (E'.fullyFaithfulFunctor.homEquiv).trans
      { toFun f := a'.inv ≫ f ≫ b'.hom
        invFun f := a'.hom ≫ f ≫ b'.inv
        left_inv f := by simp [Category.assoc]
        right_inv f := by simp [Category.assoc] }
  have heq : J'.map ∘ e = e' ∘ J.map := by
    funext f
    change J'.map (a.inv ≫ E.functor.map f ≫ b.hom) =
      a'.inv ≫ E'.functor.map (J.map f) ≫ b'.hom
    have hn : E'.functor.map (J.map f) ≫ (c.app B).hom =
        (c.app A).hom ≫ J'.map (E.functor.map f) := c.hom.naturality f
    simp only [a', b', Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, J'.map_comp, Category.assoc]
    rw [reassoc_of% hn]
    simp
  exact (Function.Bijective.of_comp_iff J'.map e.bijective).mp
    (heq ▸ e'.bijective.comp hJ)

set_option maxHeartbeats 0 in
-- Elaborate the actual coefficient-module functors and their comparisons.
/-- Restriction to a dense geometric open of the standard projective line is fully
faithful on condensed lisse Qbar_l modules.

Source: Stacks Project, Tag 0BQM and thm-lisse-qlbar-representations;
lem-dl-a1-condensed-lisse-extension-inertia, proof step 5.
(blueprint: lem-dl-a1-condensed-lisse-restriction-fully-faithful).

Proof: the specified native-to-condensed coefficient encoding is an equivalence.
Its regular-module comparison and finite biproduct comparison identify finite free
modules. Its pullback comparison identifies local trivializations, hence identifies
the two lisse predicates. On a regular scheme, the native dense-open theorem gives
bijectivity on Hom sets into a lisse module. Conjugate both Hom sets by the counits
of the encoding equivalences; naturality of the pullback comparison identifies
the resulting map with the actual condensed pullback on morphisms.
For the given models, projective-line smoothness makes the geometric target
regular. The open inclusion is dense; flat base change preserves this density
because generic points map to generic points. The base-changed square is
Cartesian, so its map is an open immersion, quasi-compact since its target is
locally Noetherian. Transport these assertions by eU and eC and apply the general
encoded dense-open argument. No inertia or Frobenius assumption is needed.
-/
theorem condensed_lisse_restriction_map_bijective
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (L M : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) C))
    (_hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L)
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    Function.Bijective ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) j).map :
      (L ⟶ M) → _) := by
  let P := ProjectiveLine (Spec (.of D.k₀))
  let β := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let fU := U₀.ι ≫ P ↘ Spec (.of D.k₀)
  let fC := C₀.ι ≫ P ↘ Spec (.of D.k₀)
  let jb : pullback fU β ⟶ pullback fC β := ((Over.pullback β).map j₀).left
  have hUft : LocallyOfFiniteType fU := by dsimp [fU, P]; infer_instance
  have hCft : LocallyOfFiniteType fC := by dsimp [fC, P]; infer_instance
  have hUn : IsLocallyNoetherian U₀ := LocallyOfFiniteType.isLocallyNoetherian fU
  have hCn : IsLocallyNoetherian C₀ := LocallyOfFiniteType.isLocallyNoetherian fC
  have hPn : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (P ↘ Spec (.of D.k₀))
  have hUqc : QuasiCompact fU := inferInstance
  have hCqc : QuasiCompact fC := inferInstance
  have hPs : Smooth (P ↘ Spec (.of D.k₀)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hUs : Smooth fU := by dsimp [fU]; infer_instance
  have hCs : Smooth fC := by dsimp [fC]; infer_instance
  have hCbs : Smooth (pullback.snd fC β) := inferInstance
  have hUbft : LocallyOfFiniteType (pullback.snd fU β) := inferInstance
  have hUbqc : QuasiCompact (pullback.snd fU β) := inferInstance
  have hCbn : IsLocallyNoetherian (pullback fC β) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd fC β)
  have hj0o : IsOpenImmersion j₀.left := by rw [_hj₀]; infer_instance
  have hd0 : Dense (Set.range j₀.left) := by
    rw [_hj₀]
    refine (_hdense.preimage_val C₀.isOpen).mono ?_
    intro x hx
    refine ⟨⟨x.val, hx⟩, ?_⟩
    exact Scheme.homOfLE_apply' hUC x.val hx
  have hsq : IsPullback jb (pullback.fst fU β) (pullback.fst fC β) j₀.left := by
    have hw : j₀.left ≫ fC = fU := Over.w j₀
    have hs : jb ≫ pullback.snd fC β = pullback.snd fU β := by
      dsimp only [jb, fU, fC, P]
      simp only [Over.pullback_map_left, Over.mk_hom, pullback.lift_snd]
    refine IsPullback.of_right (h₁₂ := pullback.snd fC β) (h₂₂ := fC)
      (v₁₃ := β) ?_ ?_ (IsPullback.of_hasPullback fC β).flip
    · rw [hw, hs]
      exact (IsPullback.of_hasPullback fU β).flip
    · dsimp only [jb, fU, fC, P]
      simp only [Over.pullback_map_left, Over.mk_hom, pullback.lift_fst]
  have hjbo : IsOpenImmersion jb :=
    MorphismProperty.of_isPullback hsq.flip hj0o
  have hjbq : QuasiCompact jb := inferInstance
  have hbflat : Flat β := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hpflat : Flat (pullback.fst fC β) := inferInstance
  have hdb : Dense (Set.range jb) := by
    rw [Scheme.range_snd_of_isPullback hsq.flip]
    refine dense_of_genericPoints_subset fun η hη ↦ ?_
    refine Scheme.genericPoints_subset_of_isOpen_of_dense (X := (C₀ : Scheme.{u}))
      j₀.left.isOpenEmbedding.isOpen_range hd0 ?_
    rw [mem_genericPoints_iff_forall_specializes] at hη ⊢
    intro c hc
    obtain ⟨η', hη'η, rfl⟩ := Flat.generalizingMap (pullback.fst fC β) hc
    exact congrArg (fun z ↦ (pullback.fst fC β) z) (hη _ hη'η)
  have hjo : IsOpenImmersion j := by rw [_hj]; infer_instance
  have hjq : QuasiCompact j := by rw [_hj]; infer_instance
  have hdj : Dense (Set.range j) := by
    rw [_hj]
    change Dense (Set.range ((eC.inv : _ → _) ∘ (jb : _ → _) ∘ (eU.hom : _ → _)))
    rw [Set.range_comp, Set.range_comp, eU.hom.surjective.range_eq,
      Set.image_univ]
    exact eC.inv.homeomorph.isDenseEmbedding.dense_image.mpr hdb
  have hCs' : Smooth (eC.hom ≫ pullback.snd fC β) := inferInstance
  have hCr : IsRegular C := IsRegular.of_smooth (eC.hom ≫ pullback.snd fC β)
  exact dense_open_map_bijective l (fun x ↦ inferInstance) j hdj L M _hM

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
