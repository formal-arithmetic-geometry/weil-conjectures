/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.KInjectiveResolution
import Sheaf.Algebra.Homology.HomComplexProjections
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! The finite-projective Hom-complex comparison used by the bounded RHom model.

Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

private theorem homObjMap_zero_target
    {E M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (𝟙 E) (0 : M ⟶ N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private theorem homObjMap_zero_source
    {E F N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : E ⟶ F) (𝟙 N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 N : N ⟶ N).val = 0
  ext W x
  change ((φ.app W).hom) (0) = 0
  exact map_zero _

private theorem homObj_zero_target
    (E N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero N) : IsZero (SheafOfModules.homObj (R := R) E N) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := E) (N := N),
    hz.eq_of_tgt (𝟙 N) 0, homObjMap_zero_target]

private theorem homObj_zero_source
    (E N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero E) : IsZero (SheafOfModules.homObj (R := R) E N) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := E) (N := N),
    hz.eq_of_src (𝟙 E) 0, homObjMap_zero_source]

set_option backward.isDefEq.respectTransparency false in
private theorem exact_homObj_of_retract
    (E F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (i : E ⟶ F) (r : F ⟶ E) (hir : i ≫ r = 𝟙 E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hF : ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 F) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 F) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 F) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 F) S.g) hz).ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hz).ShortExact := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  obtain ⟨hzF, hF⟩ := hF
  have hzE : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0 := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R), S.zero, Category.id_comp,
      homObjMap_zero_target]
  let TE := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hzE
  let TF := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 F) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 F) S.g) hzF
  let inc : TE ⟶ TF :=
    { τ₁ := SheafOfModules.homObjMap (R := R) r (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) r (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) r (𝟙 S.X₃)
      comm₁₂ := by simp [TE, TF]
      comm₂₃ := by simp [TE, TF] }
  let ret : TF ⟶ TE :=
    { τ₁ := SheafOfModules.homObjMap (R := R) i (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) i (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) i (𝟙 S.X₃)
      comm₁₂ := by simp [TE, TF]
      comm₂₃ := by simp [TE, TF] }
  have hret : inc ≫ ret = 𝟙 TE := by
    ext <;> simp [inc, ret, hir, TE]
  exact ⟨hzE, AlgebraicGeometry.Scheme.shortExact_of_retract inc ret hret hF⟩

private theorem isIso_of_fan_maps
    {A : Type*} [Category A] {X Y : ℤ → A} {T U : A}
    (π : ∀ p, T ⟶ X p) (ρ : ∀ p, U ⟶ Y p)
    (hπ : IsLimit (Fan.mk T π)) (hρ : IsLimit (Fan.mk U ρ))
    (e : ∀ p, X p ⟶ Y p) [∀ p, IsIso (e p)] (f : T ⟶ U)
    (hf : ∀ p, f ≫ ρ p = π p ≫ e p) : IsIso f := by
  let g : U ⟶ T := Fan.IsLimit.lift hπ (fun p ↦ ρ p ≫ inv (e p))
  have hg (p : ℤ) : g ≫ π p = ρ p ≫ inv (e p) := Fan.IsLimit.fac hπ _ p
  have hfg : f ≫ g = 𝟙 T := by
    apply Fan.IsLimit.hom_ext hπ
    intro p
    change (f ≫ g) ≫ π p = 𝟙 T ≫ π p
    rw [Category.assoc, hg, ← Category.assoc, hf]
    simp
  have hgf : g ≫ f = 𝟙 U := by
    apply Fan.IsLimit.hom_ext hρ
    intro p
    change (g ≫ f) ≫ ρ p = 𝟙 U ≫ ρ p
    rw [Category.assoc, hf, ← Category.assoc, hg]
    simp
  exact (Iso.mk f g hfg hgf).isIso_hom

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_cut_isIso
    (P M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k a d : ℤ) (hM : ∀ j : ℤ, j < a → IsZero (M.X j)) (hkd : k + d ≤ a) :
    IsIso ((((homComplexFunctor (R := R)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M).f d) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  classical
  let T := P.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  let i := P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)
  obtain ⟨π, hπ, _, hmap⟩ := homComplex_projections_exists (R := R)
  let e (p : ℤ) := SheafOfModules.homObjMap (R := R) (i.f p) (𝟙 (M.X (p + d)))
  have he (p : ℤ) : IsIso (e p) := by
    by_cases hp : p < k
    · have hz := hM (p + d) (by omega)
      exact (homObj_zero_target (R := R) (P.X p) (M.X (p + d)) hz).isIso
        (homObj_zero_target (R := R) (T.X p) (M.X (p + d)) hz) (e p)
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      have : IsIso (i.f p) := P.isIso_ιStupidTrunc_f _ hj'
      change IsIso (((SheafOfModules.homFunctor R).flip.obj (M.X (p + d))).map
        (i.f p).op)
      infer_instance
  apply isIso_of_fan_maps (fun p ↦ π P M d p (p + d) rfl)
    (fun p ↦ π T M d p (p + d) rfl) (Classical.choice (hπ P M d))
    (Classical.choice (hπ T M d)) e _
  intro p
  have hm := hmap P T M M i (𝟙 M) d p (p + d) rfl
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using hm

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_cut_quasiIsoAt
    (P M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k a n : ℤ) (hM : ∀ j : ℤ, j < a → IsZero (M.X j)) (hkn : k + n + 1 ≤ a) :
    QuasiIsoAt (((homComplexFunctor (R := R)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M) n := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  let f := ((homComplexFunctor (R := R)).map
    (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)).op).app M
  have : IsIso (f.f (n - 1)) := homComplex_cut_isIso P M k a _ hM (by omega)
  have : IsIso (f.f n) := homComplex_cut_isIso P M k a _ hM (by omega)
  have : IsIso (f.f (n + 1)) := homComplex_cut_isIso P M k a _ hM (by omega)
  rw [quasiIsoAt_iff' f (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℤ)
      (n - 1) n (n + 1)).map f) := by
    rw [ShortComplex.isIso_iff]
    change IsIso (f.f (n - 1)) ∧ IsIso (f.f n) ∧ IsIso (f.f (n + 1))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ShortComplex.quasiIso_of_isIso _

set_option backward.isDefEq.respectTransparency true in
private theorem exact_homObj_zero
    (E : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hz : IsZero E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ h : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) h).ShortExact := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  have h₁ := homObj_zero_source (R := R) E S.X₁ hz
  have h₂ := homObj_zero_source (R := R) E S.X₂ hz
  have h₃ := homObj_zero_source (R := R) E S.X₃ hz
  exact ⟨h₁.eq_of_src _ _,
    { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
      mono_f := h₁.mono _
      epi_g := h₃.epi _ }⟩

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_map_boundedBelow
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hexact : ∀ (p : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g) hz).ShortExact)
    (M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hM : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (M.X j))
    (hN : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (N.X j))
    (α : M ⟶ N) [QuasiIso α] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map α) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  obtain ⟨b, hb⟩ := hP
  obtain ⟨aM, haM⟩ := hM
  obtain ⟨aN, haN⟩ := hN
  rw [quasiIso_iff]
  intro n
  let k := min aM aN - n - 1
  let T := P.stupidTrunc (ComplexShape.embeddingUpIntGE k)
  let i := P.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)
  have hT : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (T.X p) := by
    refine ⟨k, b, ?_⟩
    intro p hp
    by_cases hpk : p < k
    · exact P.isZero_stupidTrunc_X _ p
        ((ComplexShape.notMem_range_embeddingUpIntGE_iff k p).2 hpk)
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      exact (hb p (by omega)).of_iso (P.stupidTruncXIso _ hj')
  have hTexact : ∀ (p : ℤ) (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) S.g) hz).ShortExact := by
    intro p S hS
    by_cases hpk : p < k
    · exact exact_homObj_zero (R := R) _
        (P.isZero_stupidTrunc_X _ p
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff k p).2 hpk)) S
    · obtain ⟨j, hj⟩ := Int.le.dest (show k ≤ p by omega)
      have hj' : (ComplexShape.embeddingUpIntGE k).f j = p := by simpa using hj
      let e := P.stupidTruncXIso _ hj'
      exact exact_homObj_of_retract (R := R) _ _ e.hom e.inv e.hom_inv_id S (hexact p S hS)
  have : QuasiIso (((homComplexFunctor (R := R)).obj (op T)).map α) :=
    quasiIso_homComplex_map_of_bounded_exact_terms J R T hT hTexact α
  have : QuasiIsoAt (((homComplexFunctor (R := R)).map i.op).app M) n :=
    homComplex_cut_quasiIsoAt P M k aM n haM (by dsimp [k]; omega)
  have : QuasiIsoAt (((homComplexFunctor (R := R)).map i.op).app N) n :=
    homComplex_cut_quasiIsoAt P N k aN n haN (by dsimp [k]; omega)
  apply (quasiIsoAt_iff_comp_right
    (((homComplexFunctor (R := R)).obj (op P)).map α)
    (((homComplexFunctor (R := R)).map i.op).app N) n).mp
  rw [((homComplexFunctor (R := R)).map i.op).naturality α]
  exact quasiIsoAt_comp _ _ n

set_option backward.isDefEq.respectTransparency true in
private theorem homComplex_map_KInjective
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {I I' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    [I.IsKInjective] [I'.IsKInjective] (s : I ⟶ I') [QuasiIso s] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map s) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] using
    quasiIso_homComplex_map (R := R) s (𝟙 P)

set_option backward.isDefEq.respectTransparency true in
/-- A bounded-above complex of retracts of finite free sheaves sends bounded-below
quasi-isomorphisms to quasi-isomorphisms under internal Hom.

Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso).

Proof:
1. Internal Hom from a finite free sheaf preserves short exact sequences. The
   splitting maps exhibit the Hom sequence from each term of P as a retract of
   that exact sequence. Its homology is a retract of zero, hence zero; its first
   map is monic and its last map epic by the splitting identities.
2. For bounded-below targets M,N and a fixed homology degree n, cut P below
   k = min(aM,aN)-n-1. The inclusion of this stupid truncation induces isomorphisms
   of Hom terms in degrees n-1,n,n+1: below k the target terms vanish; at and above
   k the source inclusion is an isomorphism. Thus it preserves degree-n homology.
   The truncated source is bounded and has exact internal Hom in every term, so
   the existing bounded exact-term Hom comparison applies. Naturality and
   two-out-of-three prove the comparison for P in degree n, and hence in all degrees.
3. Choose a bounded-below K-injective resolution of M. Step 2 applies to its map.
   Compare it with the functorial K-injective resolution using its naturality
   square. Hom sends quasi-isomorphisms between K-injective complexes to
   quasi-isomorphisms, so two-out-of-three proves the comparison into the
   functorial resolution. Apply the same naturality square to the given map
   M→I to obtain its Hom comparison, even when I is unbounded below. -/
theorem ringedSite_boundedFree_rhom_map_quasiIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hfinite : ∀ i : ℤ, ∃ r : ℕ,
      ∃ s : P.X i ⟶ SheafOfModules.free
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin r)),
      ∃ t : SheafOfModules.free
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin r))
          ⟶ P.X i, s ≫ t = 𝟙 (P.X i))
    (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    [I.IsKInjective]
    (M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hM : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero (M.X j))
    (α : M ⟶ I)
    [QuasiIso α] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map α) := by
  let : Abelian (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let H := (homComplexFunctor (R := R)).obj (op P)
  have hexact : ∀ (p : ℤ) (S : ShortComplex A), S.ShortExact →
      ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) S.g) hz).ShortExact := by
    intro p S hS
    obtain ⟨r, s, t, hst⟩ := hfinite p
    apply exact_homObj_of_retract (R := R) _ _ s t hst S
    obtain ⟨hz, hF, _⟩ := SheafOfModules.finiteFreeInternalHomExact
      (R := R) r _ (Iso.refl _) S hS
    exact ⟨hz, hF⟩
  obtain ⟨a, ha⟩ := hM
  have : M.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff M a).2 (fun j hj ↦ ha j hj)
  obtain ⟨T, hT, _⟩ := CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE M a
  have hβ : QuasiIso (H.map T.ι) :=
    homComplex_map_boundedBelow (R := R) P hP hexact M T.I ⟨a, ha⟩
      ⟨a, fun j hj ↦ (CochainComplex.isStrictlyGE_iff T.I a).1 hT j hj⟩ T.ι
  let F := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have hη (X : CochainComplex A ℤ) : QuasiIso (η.app X) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A X).2
  have hF {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [QuasiIso f] :
      QuasiIso (F.map f) := by
    have := hη X
    have := hη Y
    apply (quasiIso_iff_comp_left (η.app X) (F.map f)).mp
    rw [← η.naturality f]
    change QuasiIso (f ≫ η.app Y)
    exact quasiIso_comp _ _
  have hηT : QuasiIso (H.map (η.app T.I)) := by
    have := hη T.I
    exact homComplex_map_KInjective (R := R) P
      (show T.I ⟶ F.obj T.I from η.app T.I)
  have hFβ : QuasiIso (H.map (F.map T.ι)) := by
    have := hF T.ι
    exact homComplex_map_KInjective (R := R) P _
  have hηM : QuasiIso (H.map (η.app M)) := by
    apply (quasiIso_iff_comp_right (H.map (η.app M)) (H.map (F.map T.ι))).mp
    rw [← H.map_comp, ← η.naturality T.ι]
    change QuasiIso (H.map (T.ι ≫ η.app T.I))
    rw [H.map_comp]
    exact quasiIso_comp _ _
  have hηI : QuasiIso (H.map (η.app I)) := by
    have := hη I
    exact homComplex_map_KInjective (R := R) P (show I ⟶ F.obj I from η.app I)
  have hFα : QuasiIso (H.map (F.map α)) := by
    have := hF α
    exact homComplex_map_KInjective (R := R) P _
  change QuasiIso (H.map α)
  apply (quasiIso_iff_comp_right (H.map α) (H.map (η.app I))).mp
  rw [← H.map_comp]
  have hn : α ≫ η.app I = η.app M ≫ F.map α := η.naturality α
  rw [hn, H.map_comp]
  exact quasiIso_comp _ _

end CategoryTheory
