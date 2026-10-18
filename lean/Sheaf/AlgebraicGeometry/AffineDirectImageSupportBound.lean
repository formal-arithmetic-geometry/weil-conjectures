/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.PointCount
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.AffineSupportVanishing
import Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Support bounds for affine higher direct images

Source: Stacks Project, Etale Cohomology, Tag 0F0X, lemma-interlude-I
(blueprint: lem-kun-affine-direct-image-support-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits in
private theorem support_upperStar_subset {T X : Scheme.{u}} (p : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleSheafSupport ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj F) ⊆
      p ⁻¹' etaleSheafSupport F := by
  rintro z ⟨Ω, hΩ, hΩc, s, hs, hn⟩
  let := hΩ
  let := hΩc
  refine ⟨Ω, hΩ, hΩc, s ≫ p, ?_, ?_⟩
  · simp only [Hom.comp_apply, hs]
  · intro hz
    exact hn (hz.of_iso ((Etale.upperStarCompSheafFiberIso
      AddCommGrpCat.{u + 1} p s).app F))

open CategoryTheory.Limits in
private theorem isZero_cohomology_of_cofiltered_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] {X : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (π : D ⟶ (Functor.const I).obj X)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hz : ∀ i, IsZero (AddCommGrpCat.of
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (π.app i)).obj F) q))) (i₀ : I) :
    IsZero (AddCommGrpCat.of (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1} (c.π.app i₀ ≫ π.app i₀)).obj F) q)) := by
  obtain ⟨H, eH, r, hr, heH, B, hB, e, he⟩ :=
    Etale.exists_cofiltered_etale_cohomology_cocone D π c hc F q i₀
  have hH : IsZero H := (Functor.isZero_iff _).2 fun i ↦
    (hz i.unop).of_iso (eH i.unop)
  exact (hB.isZero_pt hH).of_iso e.symm

open CategoryTheory.Limits in
private theorem isZero_of_support_empty {T : Scheme.{u}}
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : etaleSheafSupport G = ∅) : IsZero G := by
  apply (IsZero.iff_id_eq_zero _).2
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro z
  have hz : IsZero ((pointSmallEtale (T.algClosurePoint z)).sheafFiber.obj G) := by
    by_contra hn
    have : z ∈ etaleSheafSupport G :=
      ⟨AlgebraicClosure (T.residueField z), inferInstance, inferInstance,
        T.algClosurePoint z, T.algClosurePoint_base z _, hn⟩
    simp only [hG, Set.mem_empty_iff_false] at this
  exact hz.eq_of_src _ _

open CategoryTheory.Limits in
private theorem isZero_affine_cohomology_of_support_sum
    {L : Type u} [Field L] [IsSepClosed L]
    (T : Scheme.{u}) [IsAffine T] [T.Over (Spec (.of L))]
    [LocallyOfFiniteType (T ↘ Spec (.of L))] [QuasiCompact (T ↘ Spec (.of L))]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsTorsionAbelianSheaf G) (a b q : ℕ)
    (hsupport : ∀ z ∈ etaleSheafSupport G,
      (b : Cardinal.{u}) +
        @Algebra.trdeg L (T.residueField z) _ _
          (((T ↘ Spec (.of L)).residueFieldAlgebraMap z).toAlgebra) ≤ a)
    (hq : a < b + q) : IsZero (AddCommGrpCat.of (Sheaf.H G q)) := by
  obtain ⟨eH⟩ := nonempty_sheafH_extDerivedIso T q
  apply IsZero.of_iso _ (eH.app G)
  by_cases hba : b ≤ a
  · apply affine_support_vanishing (L := L) T G hG (a - b)
    · intro z hz
      have h := hsupport z hz
      change _ ≤ ((a - b : ℕ) : Cardinal.{u})
      apply (Cardinal.add_le_add_iff_of_lt_aleph0
        (Cardinal.natCast_lt_aleph0 (n := b))).mp
      simpa only [add_comm _ (b : Cardinal.{u}), ← Nat.cast_add,
        show b + (a - b) = a by omega] using h
    · omega
  · have hempty : etaleSheafSupport G = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have h : (b : Cardinal.{u}) ≤ a := le_trans le_self_add (hsupport z hz)
      have : b ≤ a := by exact_mod_cast h
      exact hba this
    have hz := isZero_of_support_empty G hempty
    exact ((Sheaf.functorH.{u + 1} T.smallEtaleTopology q).map_isZero hz).of_iso
      (eH.app G).symm

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits in
private theorem algebraic_pullback_snd_residueField
    {V X U : Scheme.{u}} (f : V ⟶ U) (g : X ⟶ U)
    (z : ↑(pullback f g))
    (hg : @Algebra.IsAlgebraic (U.residueField (f (pullback.fst f g z)))
      (V.residueField (pullback.fst f g z)) _ _
        ((f.residueFieldMap (pullback.fst f g z)).hom.toAlgebra)) :
    @Algebra.IsAlgebraic (X.residueField (pullback.snd f g z))
      ((pullback f g).residueField z) _ _
        (((pullback.snd f g).residueFieldMap z).hom.toAlgebra) := by
  let T := Pullback.Triplet.ofPoint z
  let := ((f.residueFieldMap T.x).hom.toAlgebra)
  have : Algebra.IsAlgebraic (U.residueField (f T.x)) (V.residueField T.x) := hg
  have hint : (f.residueFieldMap T.x).hom.IsIntegral :=
    (algebraMap_isIntegral_iff).2 inferInstance
  have : IsIntegralHom (Spec.map (f.residueFieldMap T.x)) :=
    IsIntegralHom.SpecMap_iff.2 hint
  have hconj : IsIntegralHom (Spec.map
      ((U.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)) := by
    rw [Spec.map_comp]
    infer_instance
  have hinl : IsIntegralHom (Spec.map T.tensorInr) :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom)
      T.isPullback_SpecMap_tensor hconj
  let : Algebra (X.residueField T.y) T.tensor := T.tensorInr.hom.toAlgebra
  have : Algebra.IsIntegral (X.residueField T.y) T.tensor :=
    (algebraMap_isIntegral_iff).1 (IsIntegralHom.SpecMap_iff.1 hinl)
  let ψ := (Pullback.ofPointTensor z).hom
  let p := RingHom.ker ψ
  have : p.IsPrime := RingHom.ker_isPrime ψ
  have hfield : IsField (T.tensor ⧸ p) :=
    isField_of_isIntegral_of_isField' (R := X.residueField T.y) (Field.toIsField _)
  obtain ⟨e, -, -, hl⟩ := (Pullback.exists_residueField_equiv_ofPointTensor f g z).2 hfield
  let : Algebra (X.residueField T.y) ((pullback f g).residueField z) :=
    ((pullback.snd f g).residueFieldMap z).hom.toAlgebra
  let ea : (T.tensor ⧸ p) ≃ₐ[X.residueField T.y] ((pullback f g).residueField z) :=
    { e with commutes' := fun x ↦ RingHom.congr_fun hl x }
  exact ea.isAlgebraic

open CategoryTheory.Limits in
private theorem trdeg_sum_eq_of_algebraic_residue
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X T : Scheme.{u}} (x : X ⟶ Spec (.of K))
    (p : T ⟶ X) (t : T ⟶ Spec (.of L))
    (hcomm : p ≫ x = t ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (z : T)
    (halg : @Algebra.IsAlgebraic (X.residueField (p z)) (T.residueField z) _ _
      ((p.residueFieldMap z).hom.toAlgebra)) :
    Algebra.trdeg K L + @Algebra.trdeg L (T.residueField z) _ _
        ((t.residueFieldAlgebraMap z).toAlgebra) =
      @Algebra.trdeg K (X.residueField (p z)) _ _
        ((x.residueFieldAlgebraMap (p z)).toAlgebra) := by
  let : Algebra K (X.residueField (p z)) := (x.residueFieldAlgebraMap (p z)).toAlgebra
  let : Algebra (X.residueField (p z)) (T.residueField z) :=
    (p.residueFieldMap z).hom.toAlgebra
  let : Algebra K (T.residueField z) := ((p ≫ x).residueFieldAlgebraMap z).toAlgebra
  let : Algebra L (T.residueField z) := (t.residueFieldAlgebraMap z).toAlgebra
  have : IsScalarTower K (X.residueField (p z)) (T.residueField z) :=
    IsScalarTower.of_algebraMap_eq' (Hom.residueFieldAlgebraMap_comp p x z)
  have : IsScalarTower K L (T.residueField z) := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro k
    have he : CommRingCat.ofHom ((p ≫ x).residueFieldAlgebraMap z) =
        CommRingCat.ofHom ((t.residueFieldAlgebraMap z).comp (algebraMap K L)) := by
      apply Spec.map_injective
      rw [Hom.specMap_residueFieldAlgebraMap, hcomm]
      change _ = Spec.map
        (CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom (t.residueFieldAlgebraMap z))
      rw [Spec.map_comp, Hom.specMap_residueFieldAlgebraMap, Category.assoc]
    exact congrArg (fun f : CommRingCat.of K ⟶ T.residueField z ↦ f.hom k) he
  have : Algebra.IsAlgebraic (X.residueField (p z)) (T.residueField z) := halg
  rw [trdeg_add_eq K L, ← trdeg_add_eq K (X.residueField (p z)),
    trdeg_eq_zero (R := X.residueField (p z)), add_zero]

open CategoryTheory.Limits in
private theorem isZero_cohomology_pullback_of_models
    {I : Type u} [SmallCategory I] [IsCofiltered I] {X U : Scheme.{u}}
    (f : X ⟶ U) [IsAffineHom f]
    (D : I ⥤ Over U) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i).left]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hz : ∀ i, IsZero (AddCommGrpCat.of (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.snd (D.obj i).hom f)).obj F) q))) :
    IsZero (AddCommGrpCat.of (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd c.pt.hom f)).obj F) q)) := by
  classical
  have : IsConnected I := IsCofiltered.isConnected I
  let E := D ⋙ Over.pullback f
  let cE := (Over.pullback f).mapCone c
  have hcE : IsLimit cE := isLimitOfPreserves (Over.pullback f) hc
  let D' := E ⋙ Over.forget X
  let c' := (Over.forget X).mapCone cE
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget X) hcE
  let π : D' ⟶ (Functor.const I).obj X :=
    { app := fun i ↦ (E.obj i).hom
      naturality := fun i j a ↦ by
        change (E.map a).left ≫ (E.obj j).hom = (E.obj i).hom ≫ 𝟙 X
        rw [Category.comp_id]
        exact Over.w (E.map a) }
  have hAff (i : I) : IsAffine (D'.obj i) := by
    change IsAffine (pullback (D.obj i).hom f)
    infer_instance
  let (i : I) : IsAffine (D'.obj i) := hAff i
  let (i : I) : CompactSpace (D'.obj i) := inferInstance
  let (i : I) : QuasiSeparatedSpace (D'.obj i) := inferInstance
  let {i j : I} (a : i ⟶ j) : IsAffineHom (D'.map a) := inferInstance
  let i₀ : I := Classical.arbitrary I
  have hh := isZero_cohomology_of_cofiltered_isLimit D' π c' hc' F q hz i₀
  have hfac : c'.π.app i₀ ≫ π.app i₀ = pullback.snd c.pt.hom f :=
    Over.w (cE.π.app i₀)
  rw [hfac] at hh
  exact hh

open CategoryTheory.Limits in
private theorem algebraic_residue_comp_open
    {T V X : Scheme.{u}} (p : T ⟶ V) (g : V ⟶ X) [IsOpenImmersion g] (z : T)
    (hp : @Algebra.IsAlgebraic (V.residueField (p z)) (T.residueField z) _ _
      ((p.residueFieldMap z).hom.toAlgebra)) :
    @Algebra.IsAlgebraic (X.residueField ((p ≫ g) z)) (T.residueField z) _ _
      (((p ≫ g).residueFieldMap z).hom.toAlgebra) := by
  let := (p.residueFieldMap z).hom.toAlgebra
  have : Algebra.IsAlgebraic (V.residueField (p z)) (T.residueField z) := hp
  have hpint : (p.residueFieldMap z).hom.IsIntegral :=
    algebraMap_isIntegral_iff.2 inferInstance
  have hgint : (g.residueFieldMap (p z)).hom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  let := ((p ≫ g).residueFieldMap z).hom.toAlgebra
  have : Algebra.IsIntegral (X.residueField ((p ≫ g) z)) (T.residueField z) := by
    apply algebraMap_isIntegral_iff.1
    change ((p ≫ g).residueFieldMap z).hom.IsIntegral
    rw [residueFieldMap_comp, CommRingCat.hom_comp]
    exact hgint.trans _ _ hpint
  infer_instance

open CategoryTheory.Limits in
private theorem isZero_cohomology_upperStar_iso
    {T V X : Scheme.{u}} (e : T ≅ V) (p : V ⟶ X) (r : T ⟶ X)
    (hr : r = e.hom ≫ p)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hz : IsZero (AddCommGrpCat.of
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj F) q))) :
    IsZero (AddCommGrpCat.of
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} r).obj F) q)) := by
  let eH : AddCommGrpCat.of
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj F) q) ≅
      AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} e.hom).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj F)) q) :=
    (Etale.cohomologyEquiv e.hom
      ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj F) q).toAddCommGrpIso
  have hh := hz.of_iso eH.symm
  exact hh.of_iso ((Sheaf.functorH.{u + 1} T.smallEtaleTopology q).mapIso
    ((Etale.upperStarComp AddCommGrpCat.{u + 1} e.hom p r hr).app F))

open CategoryTheory.Limits in
private theorem isZero_cohomology_pullback_strictHenselization
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsAffineHom f]
    (a : ℤ) (ha : 0 ≤ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf F)
    (hsupport : etaleSheafSupport F ⊆ (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat)
    (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    (hout : s (IsLocalRing.closedPoint Ω) ∉
      {y | 0 ≤ a - (q : ℤ) ∧
        y ∈ (Y ↘ Spec (.of K)).pointsOfTrdegLE (a - (q : ℤ)).toNat}) :
    IsZero (AddCommGrpCat.of (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q)) := by
  classical
  obtain ⟨U, hUs, hUa, L, hL, hKL, hsep, htr, I, hcat, hcof, D, p, c, e,
    ⟨hc⟩, he, hmodels, htrans, hres⟩ := exists_strictLocal_algebraicResidue_models (K := K) Y s
  let := hL
  let := hKL
  let := hsep
  let := hcat
  let := hcof
  have : IsConnected I := IsCofiltered.isConnected I
  obtain ⟨b, hbY⟩ := Cardinal.lt_aleph0.mp
    (finite_trdeg_residueField (K := K) (s (IsLocalRing.closedPoint Ω)))
  have hb : Algebra.trdeg K L = (b : Cardinal.{u}) := htr.trans hbY
  have hq : a.toNat < b + q := by
    by_contra hn
    apply hout
    refine ⟨by omega, ?_⟩
    change @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
      (((Y ↘ Spec (.of K)).residueFieldAlgebraMap
        (s (IsLocalRing.closedPoint Ω))).toAlgebra) ≤ _
    rw [hbY]
    exact_mod_cast (show b ≤ (a - (q : ℤ)).toNat by omega)
  have hf : f ≫ (Y ↘ Spec (.of K)) = X ↘ Spec (.of K) :=
    (Hom.isOver_iff (Spec (.of K)) (f := f)).mp inferInstance
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of K))) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of K))
  let E := D ⋙ Over.map U.ι
  let cE := (Over.map U.ι).mapCone c
  have : PreservesLimit D (Over.map U.ι ⋙ Over.forget Y) := by
    change PreservesLimit D (Over.forget U.toScheme)
    infer_instance
  have : PreservesLimit D (Over.map U.ι) :=
    preservesLimit_of_reflects_of_preserves (Over.map U.ι) (Over.forget Y)
  have hcE : IsLimit cE := isLimitOfPreserves (Over.map U.ι) hc
  let (i : I) : IsAffine (E.obj i).left := (hmodels i).2.1
  have hz (i : I) : IsZero (AddCommGrpCat.of (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd (E.obj i).hom f)).obj F) q)) := by
    let T := pullback (E.obj i).hom f
    let t : T ⟶ Spec (.of L) := pullback.fst (E.obj i).hom f ≫ p i
    let r : T ⟶ X := pullback.snd (E.obj i).hom f
    let : T.Over (Spec (.of L)) := ⟨t⟩
    have : IsAffine T := by dsimp only [T]; infer_instance
    have : LocallyOfFiniteType (T ↘ Spec (.of L)) := by
      change LocallyOfFiniteType t
      have : LocallyOfFiniteType (p i) := (hmodels i).2.2.1
      infer_instance
    have : QuasiCompact (T ↘ Spec (.of L)) := inferInstance
    have hcomm : r ≫ (X ↘ Spec (.of K)) =
        t ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      dsimp only [r, t]
      rw [← hf, ← Category.assoc, ← pullback.condition]
      change (pullback.fst (E.obj i).hom f ≫ (D.obj i).hom ≫ U.ι) ≫ _ = _
      simp only [Category.assoc]
      rw [(hmodels i).2.2.2.2]
    let G := (Etale.upperStar AddCommGrpCat.{u + 1} r).obj F
    have hG : IsTorsionAbelianSheaf G :=
      (isTorsionAbelianSheaf_characterizations G).1.mpr
        (Etale.isTorsion_upperStar r ((isTorsionAbelianSheaf_characterizations F).1.mp hF))
    apply isZero_affine_cohomology_of_support_sum (L := L) T G hG a.toNat b q _ hq
    intro z hz
    have halg : @Algebra.IsAlgebraic (Y.residueField ((E.obj i).hom
        (pullback.fst (E.obj i).hom f z)))
        ((E.obj i).left.residueField (pullback.fst (E.obj i).hom f z)) _ _
        (((E.obj i).hom.residueFieldMap (pullback.fst (E.obj i).hom f z)).hom.toAlgebra) :=
      algebraic_residue_comp_open (D.obj i).hom U.ι _ (hres i _)
    have hr := algebraic_pullback_snd_residueField (E.obj i).hom f z halg
    have hsum := trdeg_sum_eq_of_algebraic_residue (X ↘ Spec (.of K)) r t hcomm z hr
    rw [hb] at hsum
    rw [hsum]
    exact hsupport (support_upperStar_subset r F hz)
  have hlim := isZero_cohomology_pullback_of_models f E cE hcE F q hz
  have hp : IsPullback
      (pullback.snd f (strictHenselizationStructuralMap s) ≫ e.hom)
      (pullback.fst f (strictHenselizationStructuralMap s))
      (c.pt.hom ≫ U.ι) f := by
    apply (IsPullback.of_hasPullback f (strictHenselizationStructuralMap s)).flip.of_iso
      (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using he.symm
    · simp
  exact isZero_cohomology_upperStar_iso hp.isoPullback
    (pullback.snd (c.pt.hom ≫ U.ι) f)
    (pullback.fst f (strictHenselizationStructuralMap s))
    hp.isoPullback_hom_snd.symm F q hlim

open CategoryTheory.Limits in
private theorem affine_direct_image_geometric_stalk_vanishing
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsAffineHom f]
    (a : ℤ) (ha : 0 ≤ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf F)
    (hsupport : etaleSheafSupport F ⊆ (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat)
    (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y)
    (hout : s (IsLocalRing.closedPoint Ω) ∉
      {y | 0 ≤ a - (q : ℤ) ∧
        y ∈ (Y ↘ Spec (.of K)).pointsOfTrdegLE (a - (q : ℤ)).toNat}) :
    IsZero (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))) := by
  obtain ⟨r, hr, hri⟩ := (Etale.strictHenselizationStalkFormula f s F
    ((isTorsionAbelianSheaf_characterizations F).1.mp hF) q).1
  have := hri
  have hh := isZero_cohomology_pullback_strictHenselization f a ha F hF hsupport q Ω s hout
  obtain ⟨eH⟩ := nonempty_sheafH_extDerivedIso
    (pullback f (strictHenselizationStructuralMap s)) q
  have hzero := hh.of_iso (eH.app
    ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (strictHenselizationStructuralMap s))).obj F)).symm
  exact hzero.of_iso (asIso (r ≫ Etale.strictHenselizationCohomologyComparison s f F q))

/-- Affine higher direct images lower the transcendence-degree support bound by their degree.
The target stratum is empty when `a - q < 0`, as expressed by the first conjunct.
Source: Stacks Project, Etale Cohomology, Tag 0F0X, lemma-interlude-I
(blueprint: lem-kun-affine-direct-image-support-bound).

Proof:
1. At a geometric point y with b = trdeg_K kappa(y) > a - q, use affine permanence
   (lem-weil-pbc-affine-morphism-permanence) and the strict-henselization stalk formula
   (prop-weil-pbc-strict-henselization-stalk-formula) to compute the stalk as H^q(T,F_T),
   where T is the pullback of X to the strict local scheme at y.
2. Use lem-kun-strict-local-algebraic-residue-models to express T as a cofiltered limit
   of affine finite-type schemes T_i over a separably closed field L of trdeg_K L = b.
   Their transition maps are affine. Tensor products commute with the ring colimit by
   their universal property, giving the required limit over X.
3. Residue extensions from points of T_i to their images in X are algebraic: they come
   from prime quotients of a tensor product with an algebraic field extension, which
   is integral over the other field. Pullback stalks (lemma-openclosed-stalk-upperstar)
   imply support pulls back into support of F; torsion pulls back too, using
   lem-weil-pbc-torsion-sheaf-characterizations.
4. The transcendence-degree tower formula (lem-kun-transcendence-degree-tower) gives
   b + trdeg_L kappa(z) <= a on this support. If b > a the sheaves F_i vanish by
   lemma-weil-pbc-geometric-stalk-conservative. Otherwise apply
   lem-kun-affine-support-vanishing with bound a - b; q > a - b gives H^q(T_i,F_i) = 0.
5. The canonical pullback transition isomorphisms identify the limit sheaf with F_T.
   Apply lem-weil-pbc-cofiltered-etale-cohomology-continuity to get H^q(T,F_T) = 0.
   By def-kun-support, vanishing of these stalks is exactly the asserted containment.
   This includes degree zero, q > a, and empty schemes. -/
theorem affine_direct_image_support_bound
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsAffineHom f]
    (a : ℤ) (ha : 0 ≤ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf F)
    (hsupport : etaleSheafSupport F ⊆ (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat)
    (q : ℕ) :
    etaleSheafSupport
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⊆
      {y | 0 ≤ a - (q : ℤ) ∧
        y ∈ (Y ↘ Spec (.of K)).pointsOfTrdegLE (a - (q : ℤ)).toNat} := by
  intro y hy
  by_contra hnot
  obtain ⟨Ω, hΩ, hΩc, s, hs, hn⟩ := hy
  let _ := hΩ
  let _ := hΩc
  rw [← hs] at hnot
  have hpoint : s default = s (IsLocalRing.closedPoint Ω) :=
    congrArg s (Subsingleton.elim _ _)
  have hz := affine_direct_image_geometric_stalk_vanishing f a ha F hF hsupport q Ω s
    (by simpa [hpoint] using hnot)
  exact hn hz

end AlgebraicGeometry.Scheme
