/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoverCech
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Second-limit comparison for finite affine étale Čech covers

Source: Stacks Project, Tags 099U (second Čech-colimit calculation) and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison).

The stage and limit families below are actual fibre products in the recorded sites.
The theorem specifies every transition and comparison map on tuple coordinates.
Its colimit universal properties express the canonical isomorphisms, both for complexes
and for every cohomology group. Fixed-ring left-module sheaves use the module-valued
comparison of `proEtaleSiteComparisonModules`; forgetting scalars gives exactly the
underlying abelian-presheaf Čech construction of `CoverCech`.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change of an initial covering object to a later stage, in the small étale site.
Source: Stacks Project, Tag 099U, second limit paragraph
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverStageObject {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (i : {i : L // i₀ ≤ i}) (a : Fin m) : X.Etale :=
  pullback (f a) (D.map (homOfLE i.property).op)

/-- The covering arrow at a later stage is the second fibre-product projection.
Source: Stacks Project, Tag 099U, second limit paragraph
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverStageArrow {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (i : {i : L // i₀ ≤ i}) (a : Fin m) :
    finiteEtaleCoverStageObject D i₀ W f i a ⟶ D.obj (op i.val) :=
  pullback.snd (f a) (D.map (homOfLE i.property).op)

/-- Base change of an initial covering object to the given pro-étale limit.
Source: Stacks Project, Tags 099U and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverLimitObject {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (a : Fin m) : X.ProEt :=
  pullback ((Scheme.toProEt X).map (f a)) (π.app (op i₀))

/-- The limiting covering arrow is the second fibre-product projection.
Source: Stacks Project, Tags 099U and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison). -/
noncomputable abbrev finiteEtaleCoverLimitArrow {X : Scheme.{u}}
    {L : Type u} [Preorder L] (D : Lᵒᵖ ⥤ X.Etale) (i₀ : L)
    {m : ℕ} (W : Fin m → X.Etale) (f : ∀ a, W a ⟶ D.obj (op i₀))
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (a : Fin m) : finiteEtaleCoverLimitObject D i₀ W f U π a ⟶ U :=
  pullback.snd ((Scheme.toProEt X).map (f a)) (π.app (op i₀))

private instance tail_nonempty {L : Type*} [Preorder L] (i₀ : L) :
    Nonempty {i : L // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩

private instance tail_directed {L : Type*} [Preorder L] [IsDirected L (· ≤ ·)]
    (i₀ : L) : IsDirected {i : L // i₀ ≤ i} (· ≤ ·) :=
  ⟨fun i j ↦ by
    obtain ⟨k, hi, hj⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hi⟩, hi, hj⟩⟩

private def tailInclusion {L : Type*} [Preorder L] (i₀ : L) :
    {i : L // i₀ ≤ i}ᵒᵖ ⥤ Lᵒᵖ :=
  (show Monotone (fun i : {i : L // i₀ ≤ i} ↦ i.val) from fun _ _ h ↦ h).functor.op

private instance tail_initial {L : Type*} [Preorder L] [IsDirected L (· ≤ ·)]
    (i₀ : L) : (tailInclusion i₀).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro i
    obtain ⟨j, h₀, hi⟩ := exists_ge_ge i₀ i.unop
    exact ⟨op ⟨j, h₀⟩, ⟨(homOfLE hi).op⟩⟩
  · intro i j a b
    exact ⟨j, 𝟙 _, Subsingleton.elim _ _⟩

private def tupleCone {C : Type*} [Category* C] {B : C} {N : Type*}
    {V : N → C} {f : ∀ a, V a ⟶ B} (S : SiteCechComplex V f)
    (p : ℕ) (t : Fin (p + 1) → N) :
    Cone (WidePullbackShape.wideCospan B (V ∘ t) (fun k ↦ f (t k))) :=
  WidePullbackCone.mk (S.pr p t 0 ≫ f (t 0)) (S.pr p t) (S.comm p t)

private noncomputable def tupleIsLimit {C : Type*} [Category* C] {B : C} {N : Type*}
    {V : N → C} {f : ∀ a, V a ⟶ B} (S : SiteCechComplex V f)
    (p : ℕ) (t : Fin (p + 1) → N) : IsLimit (tupleCone S p t) := by
  classical
  let h (c : WidePullbackCone (fun k ↦ f (t k))) :=
    S.universal p t c.pt c.π (fun k ↦ (c.condition k).trans (c.condition 0).symm)
  exact WidePullbackCone.IsLimit.mk _ (fun c ↦ (h c).choose)
    (fun c ↦ by
      change (h c).choose ≫ S.pr p t 0 ≫ f (t 0) = _
      rw [← Category.assoc, (h c).choose_spec.1 0]
      exact c.condition 0)
    (fun c k ↦ (h c).choose_spec.1 k)
    (fun c a _ ha ↦ (h c).choose_spec.2 a ha)

private theorem tuple_ext {C : Type*} [Category* C] {B : C} {N : Type*}
    {V : N → C} {f : ∀ a, V a ⟶ B} (S : SiteCechComplex V f)
    {p : ℕ} {t : Fin (p + 1) → N} {Z : C} {a b : Z ⟶ S.W p t}
    (h : ∀ k, a ≫ S.pr p t k = b ≫ S.pr p t k) : a = b := by
  obtain ⟨c, hc, hu⟩ := S.universal p t Z (fun k ↦ b ≫ S.pr p t k)
    (fun k ↦ by rw [Category.assoc, Category.assoc, S.comm])
  exact (hu a h).trans (hu b (fun _ ↦ rfl)).symm

private noncomputable def tupleLift {C E : Type*} [Category* C] [Category* E]
    {B : C} {N : Type*} {V : N → C} {f : ∀ a, V a ⟶ B}
    (S : SiteCechComplex V f) (Q : C ⥤ E)
    (p : ℕ) (t : Fin (p + 1) → N)
    [PreservesLimit (WidePullbackShape.wideCospan B (V ∘ t) (fun k ↦ f (t k))) Q]
    {Z : E} (a : ∀ k, Z ⟶ Q.obj (V (t k)))
    (ha : ∀ k, a k ≫ Q.map (f (t k)) = a 0 ≫ Q.map (f (t 0))) :
    Z ⟶ Q.obj (S.W p t) :=
  (isLimitOfPreserves Q (tupleIsLimit S p t)).lift
    (WidePullbackShape.mkCone (a 0 ≫ Q.map (f (t 0))) a ha)

private theorem tupleLift_pr {C E : Type*} [Category* C] [Category* E]
    {B : C} {N : Type*} {V : N → C} {f : ∀ a, V a ⟶ B}
    (S : SiteCechComplex V f) (Q : C ⥤ E)
    (p : ℕ) (t : Fin (p + 1) → N)
    [PreservesLimit (WidePullbackShape.wideCospan B (V ∘ t) (fun k ↦ f (t k))) Q]
    {Z : E} (a : ∀ k, Z ⟶ Q.obj (V (t k)))
    (ha : ∀ k, a k ≫ Q.map (f (t k)) = a 0 ≫ Q.map (f (t 0))) (k) :
    tupleLift S Q p t a ha ≫ Q.map (S.pr p t k) = a k :=
  (isLimitOfPreserves Q (tupleIsLimit S p t)).fac _ (some k)

private theorem mapped_tuple_ext {C E : Type*} [Category* C] [Category* E]
    {B : C} {N : Type*} {V : N → C} {f : ∀ a, V a ⟶ B}
    (S : SiteCechComplex V f) (Q : C ⥤ E)
    {p : ℕ} {t : Fin (p + 1) → N}
    [PreservesLimit (WidePullbackShape.wideCospan B (V ∘ t) (fun k ↦ f (t k))) Q]
    {Z : E} {a b : Z ⟶ Q.obj (S.W p t)}
    (h : ∀ k, a ≫ Q.map (S.pr p t k) = b ≫ Q.map (S.pr p t k)) : a = b := by
  apply (isLimitOfPreserves Q (tupleIsLimit S p t)).hom_ext
  intro j
  cases j with
  | none =>
    change a ≫ Q.map (S.pr p t 0 ≫ f (t 0)) =
      b ≫ Q.map (S.pr p t 0 ≫ f (t 0))
    simp only [Q.map_comp, ← Category.assoc, h]
  | some k => exact h k

private noncomputable def tupleCochainMap
    {C E : Type*} [Category* C] [Category* E] {B : C} {B' : E} {N : Type*}
    {V : N → C} {f : ∀ a, V a ⟶ B} {V' : N → E} {f' : ∀ a, V' a ⟶ B'}
    (S : SiteCechComplex V f) (T : SiteCechComplex V' f')
    (Q : C ⥤ E) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (G : Eᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (η : F ⟶ Q.op ⋙ G)
    (s : ∀ p t, T.W p t ⟶ Q.obj (S.W p t))
    (hs : ∀ p t (j : Fin (p + 2)),
      T.indexMap t j.succAbove ≫ s p (t ∘ j.succAbove) =
        s (p + 1) t ≫ Q.map (S.indexMap t j.succAbove)) :
    S.complex F ⟶ T.complex G :=
  CochainComplex.ofHom (fun p ↦ AddCommGrpCat.ofHom
    { toFun := fun z t ↦ G.map (s p t).op (η.app (op (S.W p t)) (z t))
      map_zero' := by funext t; simp
      map_add' := by intro a b; funext t; simp }) (by
    intro p
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    apply AddCommGrpCat.ext
    intro z
    funext t
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      G.map (T.indexMap t j.succAbove).op
        (G.map (s p (t ∘ j.succAbove)).op
          (η.app _ (z (t ∘ j.succAbove))))) =
      G.map (s (p + 1) t).op (η.app _ (∑ j : Fin (p + 2),
        (-1 : ℤ) ^ j.val • F.map (S.indexMap t j.succAbove).op
          (z (t ∘ j.succAbove))))
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, map_zsmul]
    congr 1
    have hn := η.naturality (S.indexMap t j.succAbove).op
    have hm := congrArg (fun a ↦ G.map a.op) (hs p t j)
    simp only [op_comp, G.map_comp] at hm
    change _ = ((F.map _ ≫ η.app _) ≫ G.map _).hom _
    rw [hn]
    exact congrArg (fun a ↦ a (η.app _ (z (t ∘ j.succAbove)))) hm)

private def coordinateProjection {N : Type} (D : N → AddCommGrpCat.{u + 1})
    (t : N) : AddCommGrpCat.of (∀ t, D t) ⟶ D t :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦ z t
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

private def coordinateProduct {N : Type} (D : N → AddCommGrpCat.{u + 1}) :
    IsLimit (Fan.mk (AddCommGrpCat.of (∀ t, D t)) (coordinateProjection D)) := by
  refine Fan.IsLimit.mk _ (fun z ↦ AddCommGrpCat.ofHom
    { toFun := fun a t ↦ z.proj t a
      map_zero' := by funext t; exact map_zero (z.proj t).hom
      map_add' := by intro a b; funext t; exact map_add (z.proj t).hom _ _ }) ?_ ?_
  · intro z t
    rfl
  · intro z q hq
    apply AddCommGrpCat.ext
    intro a
    funext t
    exact congrArg (fun f ↦ f a) (hq t)

private noncomputable def productColimit {I : Type u} [SmallCategory I]
    [IsFiltered I] {N : Type} [Finite N]
    (D : N → I ⥤ AddCommGrpCat.{u + 1}) (A : I ⥤ AddCommGrpCat.{u + 1})
    (α : ∀ t, A ⟶ D t) (hA : IsLimit (Fan.mk A α))
    (K : Cocone A) (c : ∀ t, Cocone (D t)) (hc : ∀ t, IsColimit (c t))
    (β : ∀ t, K.pt ⟶ (c t).pt) (hβ : IsLimit (Fan.mk K.pt β))
    (h : ∀ i t, (α t).app i ≫ (c t).ι.app i = K.ι.app i ≫ β t) :
    IsColimit K := by
  classical
  have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let e (t : N) : colimit (D t) ≅ (c t).pt :=
    (colimit.isColimit (D t)).coconePointUniqueUpToIso (hc t)
  let H := Fan.isLimitMapConeEquiv
    (colim : (I ⥤ AddCommGrpCat.{u + 1}) ⥤ _) D (Fan.mk A α)
      (isLimitOfPreserves _ hA)
  let C : Fan (fun t ↦ colimit (D t)) := Fan.mk K.pt (fun t ↦ β t ≫ (e t).inv)
  have HC : IsLimit C := by
    refine Fan.IsLimit.mk _
      (fun z ↦ hβ.lift (Fan.mk z.pt (fun t ↦ z.proj t ≫ (e t).hom))) ?_ ?_
    · intro z t
      change _ ≫ β t ≫ (e t).inv = z.proj t
      have ht := hβ.fac (Fan.mk z.pt (fun t ↦ z.proj t ≫ (e t).hom)) ⟨t⟩
      change _ ≫ β t = z.proj t ≫ (e t).hom at ht
      rw [← Category.assoc, ht]
      simp
    · intro z q hq
      apply hβ.hom_ext
      rintro ⟨t⟩
      rw [hβ.fac]
      have ht := hq t
      change q ≫ β t ≫ (e t).inv = z.proj t at ht
      rw [← cancel_mono (e t).inv]
      simpa using ht
  let i := H.conePointUniqueUpToIso HC
  have hi : colimit.desc A K = i.hom := by
    apply HC.hom_ext
    rintro ⟨t⟩
    change colimit.desc A K ≫ C.proj t =
      (H.conePointUniqueUpToIso HC).hom ≫ C.π.app ⟨t⟩
    rw [IsLimit.conePointUniqueUpToIso_hom_comp H HC ⟨t⟩]
    apply colimit.hom_ext
    intro j
    change colimit.ι A j ≫ colimit.desc A K ≫ β t ≫ (e t).inv =
      colimit.ι A j ≫ colim.map (α t)
    rw [colimit.ι_desc_assoc, colimit.ι_map]
    rw [← Category.assoc, ← h j t]
    simp [e, Category.assoc]
  have : IsIso ((colimit.isColimit A).desc K) := by
    change IsIso (colimit.desc A K)
    rw [hi]
    infer_instance
  exact IsColimit.ofPointIso (colimit.isColimit A)

set_option backward.isDefEq.respectTransparency false in
private theorem homologyPreserves {I : Type u} [SmallCategory I] [IsFiltered I]
    (q : ℕ) : PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℕ) q) := by
  have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have : (colim : (I ⥤ AddCommGrpCat.{u + 1}) ⥤ _).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : PreservesColimitsOfShape I
      (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}) := by
    refine ⟨fun {F} ↦ ?_⟩
    let S := (ShortComplex.functorEquivalence I AddCommGrpCat.{u + 1}).inverse.obj F
    let e : S.homology ≅ F ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{u + 1} :=
      NatIso.ofComponents
        (fun i ↦ (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u + 1}).obj i)).symm)
        (by
          intro i j f
          have h := S.homologyMap_mapNatTrans ((evaluation I AddCommGrpCat.{u + 1}).map f)
          change ShortComplex.homologyMap (F.map f) = _ at h
          change S.homology.map f ≫
            (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u + 1}).obj j)).inv =
            (S.mapHomologyIso ((evaluation I AddCommGrpCat.{u + 1}).obj i)).inv ≫
              ShortComplex.homologyMap (F.map f)
          rw [h]
          simp)
    let a : colimit (F ⋙ ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}) ≅
        (ShortComplex.colimitCocone F).pt.homology :=
      (colim.mapIso e).symm ≪≫ (S.mapHomologyIso colim).symm
    refine preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F) ?_
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    refine Cocone.ext a ?_
    intro i
    have h := S.homologyMap_mapNatTrans (colim.ι (C := AddCommGrpCat.{u + 1}) i)
    change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
    change colimit.ι _ i ≫ a.hom =
      ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
    rw [h]
    simp [a, e]
  have : PreservesColimitsOfShape I
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u + 1} (.up ℕ) q) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso AddCommGrpCat.{u + 1} (.up ℕ) q).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPreserves {I : Type u} [SmallCategory I] :
    PreservesColimitsOfShape I
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}) := by
  classical
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let E := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  by_cases hn : 0 ≤ n
  · let k := n.toNat
    have hk : ComplexShape.embeddingUpNat.f k = n := by
      exact Int.toNat_of_nonneg hn
    let e : E ⋙ HomologicalComplex.eval _ (.up ℤ) n ≅
        HomologicalComplex.eval _ (.up ℕ) k :=
      NatIso.ofComponents (fun K ↦ HomologicalComplex.extendXIso K _ hk)
        (by
          intro K L f
          change (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f n ≫
            (L.extendXIso _ hk).hom = (K.extendXIso _ hk).hom ≫ f.f k
          rw [HomologicalComplex.extendMap_f f _ hk]
          simp)
    exact preservesColimitsOfShape_of_natIso e.symm
  · apply Functor.preservesColimitsOfShape_of_isZero
    apply (Functor.isZero_iff _).mpr
    intro K
    exact HomologicalComplex.isZero_extend_X K _ n (by
      intro k hk
      exact hn (hk ▸ Int.natCast_nonneg k))

set_option maxHeartbeats 800000 in
-- The explicit tuple-limit and colimit constructions require additional elaboration steps.

set_option backward.isDefEq.respectTransparency false in
/-- The canonical restriction cocone of finite affine étale covering complexes is
colimiting, and remains colimiting on every Čech cohomology group. The two projection
identities for `r` and `s` uniquely characterize the canonical maps of tuple products;
the next two identities prescribe all cochain maps using those restrictions. Thus the
existentials assert existence of these specified canonical constructions, not a choice
of unrelated isomorphisms. The nonnegative complexes extend by zero to the integer
complexes of `CoverCech`; the second colimit assertion records that extension explicitly.

Source: Stacks Project, Tags 099U (second Čech-colimit calculation) and 099S
(blueprint: lem-weil-pbc-finite-etale-cover-cech-stage-comparison).

Proof: (1) The tail above `i₀` is nonempty and directed and retains the same limit:
extend a cone by choosing a common upper bound with `i₀`, with independence checked at
another common upper bound. For an empty cover every term is the zero abelian group.
(2) The affine-limit theorem makes the limit affine. Étale base change preserves the
finite covering and all tuple fibre products. Their sources are affine; their maps to
`X` are étale of finite presentation, since affine morphisms are quasi-compact and
separated and étale morphisms are locally of finite presentation.
(3) Each limit tuple product is the limit of its stage tuple products: a map to it is
exactly compatible maps to the base and each original covering factor. This also proves
the projection identities, including repeated indices.
(4) Coordinate rings are the filtered colimits of their stage rings, so these are
ind-étale basis objects. Apply comparison-sections to each tuple, with legs the comparison
unit followed by restriction. Ind-étale stability gives the required pro-étale objects;
base change gives the limiting cover.
(5) Filtered colimits commute with the finite products indexed by the ordered tuples.
Thus the prescribed cocone is colimiting in every nonnegative degree.
(6) The projection identities and naturality of the unit commute with deletion of any
factor, hence with the alternating sums defining the differentials. The maps therefore
form the stated diagram and cocone. Its degreewise colimit universal property gives the
colimit in complexes, also after extension by zero to negative degrees.
(7) Filtered colimits commute with kernels and are exact in abelian groups. Applying this
to cycles and boundaries identifies the colimit of the stage cohomology with the limit
complex's cohomology, with the same induced restriction legs. In degree zero the incoming
term is zero. No injectivity, augmentation exactness, or positive-degree vanishing is used. -/
theorem finite_etale_cover_cech_stage_comparison
    {X : Scheme.{u}} [IsAffine X]
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {L : Type u} [Preorder L] [IsDirected L (· ≤ ·)] [Nonempty L]
    (D : Lᵒᵖ ⥤ X.Etale) [∀ i, IsAffine (D.obj i).left]
    (U : X.ProEt) (π : (Functor.const Lᵒᵖ).obj U ⟶ D ⋙ Scheme.toProEt X)
    (_hlim : IsLimit (Cone.mk U.left
      (Functor.whiskerRight π (Scheme.ProEt.forget X ⋙ Over.forget X))))
    (i₀ : L) {m : ℕ} (W : Fin m → X.Etale) [∀ a, IsAffine (W a).left]
    (f : ∀ a, W a ⟶ D.obj (op i₀))
    (_hcover : Sieve.ofArrows W f ∈ X.smallEtaleTopology (D.obj (op i₀)))
    (S : ∀ i : {i : L // i₀ ≤ i},
      SiteCechComplex (finiteEtaleCoverStageObject D i₀ W f i)
        (finiteEtaleCoverStageArrow D i₀ W f i))
    (T : SiteCechComplex (finiteEtaleCoverLimitObject D i₀ W f U π)
      (finiteEtaleCoverLimitArrow D i₀ W f U π)) :
    ∃ (r : ∀ {i j : {i : L // i₀ ≤ i}}, (i ⟶ j) →
        ∀ (p : ℕ) (t : Fin (p + 1) → Fin m), (S j).W p t ⟶ (S i).W p t)
      (s : ∀ (i : {i : L // i₀ ≤ i}) (p : ℕ) (t : Fin (p + 1) → Fin m),
        T.W p t ⟶ (Scheme.toProEt X).obj ((S i).W p t))
      (A : {i : L // i₀ ≤ i} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ i, A.obj i ≅ (S i).complex (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat))
      (K : Cocone A)
      (eK : K.pt ≅ T.complex
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj ⋙
          forget₂ (ModuleCat Λ) AddCommGrpCat)),
      (∀ (i j : {i : L // i₀ ≤ i}) (h : i ⟶ j) (p : ℕ)
          (t : Fin (p + 1) → Fin m) (k : Fin (p + 1)),
        (r h p t ≫ (S i).pr p t k ≫
          pullback.fst (f (t k)) (D.map (homOfLE i.property).op) =
            (S j).pr p t k ≫
              pullback.fst (f (t k)) (D.map (homOfLE j.property).op)) ∧
        (r h p t ≫ (S i).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f i (t k) =
          (S j).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f j (t k) ≫
            D.map (homOfLE (leOfHom h)).op)) ∧
      (∀ (i : {i : L // i₀ ≤ i}) (p : ℕ) (t : Fin (p + 1) → Fin m)
          (k : Fin (p + 1)),
        (s i p t ≫ (Scheme.toProEt X).map ((S i).pr p t k ≫
          pullback.fst (f (t k)) (D.map (homOfLE i.property).op)) =
            T.pr p t k ≫
              pullback.fst ((Scheme.toProEt X).map (f (t k))) (π.app (op i₀))) ∧
        (s i p t ≫ (Scheme.toProEt X).map
          ((S i).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f i (t k)) =
            T.pr p t k ≫ finiteEtaleCoverLimitArrow D i₀ W f U π (t k) ≫
              π.app (op i.val))) ∧
      (∀ (i j : {i : L // i₀ ≤ i}) (h : i ⟶ j) (p : ℕ)
          (z : (S i).cochains (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat) p)
          (t : Fin (p + 1) → Fin m),
        (((eA i).inv ≫ A.map h ≫ (eA j).hom).f p) z t =
          (F.obj.map (r h p t).op) (z t)) ∧
      (∀ (i : {i : L // i₀ ≤ i}) (p : ℕ)
          (z : (S i).cochains (F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat) p)
          (t : Fin (p + 1) → Fin m),
        (((eA i).inv ≫ K.ι.app i ≫ eK.hom).f p) z t =
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F).obj.map
            (s i p t).op)
            ((((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom.app
              (op ((S i).W p t))) (z t))) ∧
      Nonempty (IsColimit K) ∧
      Nonempty (IsColimit ((ComplexShape.embeddingUpNat.extendFunctor
        AddCommGrpCat.{u + 1}).mapCocone K)) ∧
      ∀ q : ℕ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor AddCommGrpCat
          (ComplexShape.up ℕ) q).mapCocone K)) := by
  classical
  let J := {i : L // i₀ ≤ i}
  let Q := Scheme.toProEt X
  let d (i j : J) (h : i ⟶ j) := D.map (homOfLE (show i.val ≤ j.val from leOfHom h)).op
  have dcomp (i j k : J) (h : i ⟶ j) (g : j ⟶ k) :
      d i k (h ≫ g) = d j k g ≫ d i j h := by
    dsimp [d]
    rw [← D.map_comp]
    rfl
  let v (i j : J) (h : i ⟶ j) (a : Fin m) :
      finiteEtaleCoverStageObject D i₀ W f j a ⟶
        finiteEtaleCoverStageObject D i₀ W f i a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ d i j h) (by
      simp only [Category.assoc]
      rw [← D.map_comp]
      exact pullback.condition)
  have vfst (i j : J) (h : i ⟶ j) (a) :
      v i j h a ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have vsnd (i j : J) (h : i ⟶ j) (a) :
      v i j h a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ d i j h :=
    pullback.lift_snd _ _ _
  have rdata {i j : J} (h : i ⟶ j) (p : ℕ) (t : Fin (p + 1) → Fin m) :
      ∃! b : (S j).W p t ⟶ (S i).W p t,
        ∀ k, b ≫ (S i).pr p t k = (S j).pr p t k ≫ v i j h (t k) :=
    (S i).universal p t ((S j).W p t)
      (fun k ↦ (S j).pr p t k ≫ v i j h (t k)) (by
        intro k
        simp only [Category.assoc, vsnd]
        rw [← Category.assoc, ← Category.assoc, (S j).comm])
  let r {i j : J} (h : i ⟶ j) (p : ℕ) (t : Fin (p + 1) → Fin m) :
      (S j).W p t ⟶ (S i).W p t := (rdata h p t).choose
  have rpr {i j : J} (h : i ⟶ j) (p t k) :
      r h p t ≫ (S i).pr p t k = (S j).pr p t k ≫ v i j h (t k) :=
    (rdata h p t).choose_spec.1 k
  let w (i : J) (a : Fin m) :
      finiteEtaleCoverLimitObject D i₀ W f U π a ⟶
        Q.obj (finiteEtaleCoverStageObject D i₀ W f i a) :=
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ π.app (op i.val)) (by
      simp only [Category.assoc]
      have hn : π.app (op i.val) ≫ Q.map (D.map (homOfLE i.property).op) =
          π.app (op i₀) := by
        exact (π.naturality (homOfLE i.property).op).symm.trans
          (Category.id_comp _)
      rw [hn]
      exact pullback.condition)) ≫
      (PreservesPullback.iso Q (f a) (D.map (homOfLE i.property).op)).inv
  have wfst (i : J) (a) : w i a ≫ Q.map (pullback.fst _ _) =
      pullback.fst ((Scheme.toProEt X).map (f a)) (π.app (op i₀)) := by
    dsimp [w]
    simp only [Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst]
  have wsnd (i : J) (a) : w i a ≫ Q.map (pullback.snd _ _) =
      pullback.snd ((Scheme.toProEt X).map (f a)) (π.app (op i₀)) ≫
        π.app (op i.val) := by
    dsimp [w]
    simp only [Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]
  let s (i : J) (p : ℕ) (t : Fin (p + 1) → Fin m) :
      T.W p t ⟶ Q.obj ((S i).W p t) :=
    tupleLift (S i) Q p t (fun k ↦ T.pr p t k ≫ w i (t k)) (by
      intro k
      simp only [Category.assoc, wsnd]
      rw [← Category.assoc, ← Category.assoc, T.comm])
  have spr (i : J) (p t k) : s i p t ≫ Q.map ((S i).pr p t k) =
      T.pr p t k ≫ w i (t k) := tupleLift_pr (S i) Q p t _ _ k
  have rid (i : J) (p t) : r (𝟙 i) p t = 𝟙 _ := by
    apply tuple_ext (S i)
    intro k
    rw [rpr (𝟙 i), Category.id_comp]
    apply pullback.hom_ext <;> simp [v, d]
  have rcomp {i j k : J} (h : i ⟶ j) (g : j ⟶ k) (p t) :
      r (h ≫ g) p t = r g p t ≫ r h p t := by
    apply tuple_ext (S i)
    intro a
    rw [rpr (h ≫ g), Category.assoc, rpr h, ← Category.assoc, rpr g, Category.assoc]
    apply congrArg ((S k).pr p t a ≫ ·)
    apply pullback.hom_ext
    · rw [vfst i k (h ≫ g), Category.assoc, vfst i j h, vfst j k g]
    · rw [vsnd i k (h ≫ g), Category.assoc, vsnd i j h, ← Category.assoc,
        vsnd j k g, Category.assoc, ← dcomp i j k h g]
  have sr {i j : J} (h : i ⟶ j) (p t) :
      s j p t ≫ Q.map (r h p t) = s i p t := by
    apply mapped_tuple_ext (S i) Q
    intro k
    rw [Category.assoc, ← Q.map_comp, rpr h, Q.map_comp, ← Category.assoc, spr, spr]
    rw [Category.assoc]
    apply congrArg (T.pr p t k ≫ ·)
    apply PullbackCone.IsLimit.hom_ext
      (isLimitOfHasPullbackOfPreservesLimit Q (f (t k))
        (D.map (homOfLE i.property).op))
    · change (w j (t k) ≫ Q.map (v i j h (t k))) ≫
        Q.map (pullback.fst _ _) = w i (t k) ≫ Q.map (pullback.fst _ _)
      rw [Category.assoc, ← Q.map_comp, vfst i j h, wfst, wfst]
    · change (w j (t k) ≫ Q.map (v i j h (t k))) ≫
        Q.map (pullback.snd _ _) = w i (t k) ≫ Q.map (pullback.snd _ _)
      rw [Category.assoc, ← Q.map_comp, vsnd i j h, Q.map_comp, ← Category.assoc,
        wsnd, wsnd, Category.assoc]
      apply congrArg (pullback.snd _ _ ≫ ·)
      simpa [Q, d] using (π.naturality
        (homOfLE (show i.val ≤ j.val from leOfHom h)).op).symm
  have rindex {i j : J} (h : i ⟶ j) (p : ℕ)
      (t : Fin (p + 2) → Fin m) (a : Fin (p + 2)) :
      (S j).indexMap t a.succAbove ≫ r h p (t ∘ a.succAbove) =
        r h (p + 1) t ≫ (S i).indexMap t a.succAbove := by
    apply tuple_ext (S i)
    intro k
    rw [Category.assoc, rpr h, ← Category.assoc, (S j).indexMap_pr,
      Category.assoc, (S i).indexMap_pr, rpr h]
    rfl
  have sindex (i : J) (p : ℕ) (t : Fin (p + 2) → Fin m) (a : Fin (p + 2)) :
      T.indexMap t a.succAbove ≫ s i p (t ∘ a.succAbove) =
        s i (p + 1) t ≫ Q.map ((S i).indexMap t a.succAbove) := by
    apply mapped_tuple_ext (S i) Q
    intro k
    rw [Category.assoc, spr, ← Category.assoc, T.indexMap_pr,
      Category.assoc, ← Q.map_comp, (S i).indexMap_pr, spr]
    rfl
  let F' := F.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat
  let M := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F
  let G := M.obj ⋙ forget₂ (ModuleCat Λ) AddCommGrpCat
  let η : F' ⟶ Q.op ⋙ G := Functor.whiskerRight
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom
      (forget₂ (ModuleCat Λ) AddCommGrpCat)
  let A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ :=
    { obj := fun i ↦ (S i).complex F'
      map := fun {i j} h ↦ tupleCochainMap (S i) (S j) (𝟭 _) F' F' (𝟙 _)
        (r h) (rindex h)
      map_id := by
        intro i
        ext p z
        funext t
        change F'.map (r (𝟙 i) p t).op (z t) = z t
        rw [rid, op_id, F'.map_id]
        rfl
      map_comp := by
        intro i j k h g
        ext p z
        funext t
        change F'.map (r (h ≫ g) p t).op (z t) =
          F'.map (r g p t).op (F'.map (r h p t).op (z t))
        rw [rcomp h g, op_comp, F'.map_comp]
        rfl }
  let K : Cocone A :=
    { pt := T.complex G
      ι :=
        { app := fun i ↦ tupleCochainMap (S i) T Q F' G η (s i) (sindex i)
          naturality := by
            intro i j h
            ext p z
            funext t
            change G.map (s j p t).op
              (η.app _ (F'.map (r h p t).op (z t))) =
                G.map (s i p t).op (η.app _ (z t))
            have hn := η.naturality (r h p t).op
            have hne := congrArg (fun a ↦ a (z t)) hn
            change η.app _ (F'.map (r h p t).op (z t)) =
              G.map (Q.map (r h p t)).op (η.app _ (z t)) at hne
            rw [hne, ← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp, sr h] } }
  let E (p : ℕ) (t : Fin (p + 1) → Fin m) : Jᵒᵖ ⥤ X.Etale :=
    { obj := fun i ↦ (S i.unop).W p t
      map := fun h ↦ r h.unop p t
      map_id := fun i ↦ rid i.unop p t
      map_comp := fun h g ↦ rcomp g.unop h.unop p t }
  let c (p : ℕ) (t : Fin (p + 1) → Fin m) : Cone (E p t ⋙ Q) :=
    Cone.mk (T.W p t)
      { app := fun i ↦ s i.unop p t
        naturality := fun i j h ↦ by simpa using (sr h.unop p t).symm }
  let P : X.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget X ⋙ Over.forget X
  let B : X.Etale ⥤ Scheme.{u} := Q ⋙ P
  have stage_affine (i : J) (a : Fin m) :
      IsAffine (finiteEtaleCoverStageObject D i₀ W f i a).left := by
    let h := isLimitOfPreserves B (pullbackIsPullback (f a)
      (D.map (homOfLE i.property).op))
    have : ∀ z, IsAffine (((cospan (f a) (D.map (homOfLE i.property).op)) ⋙ B).obj z) := by
      intro z
      cases z with
      | none => exact inferInstanceAs (IsAffine (D.obj (op i₀)).left)
      | some z =>
        cases z with
        | left => exact inferInstanceAs (IsAffine (W a).left)
        | right => exact inferInstanceAs (IsAffine (D.obj (op i.val)).left)
    exact Scheme.isAffine_of_isLimit _ h
  have tuple_affine (p : ℕ) (t : Fin (p + 1) → Fin m) (i : Jᵒᵖ) :
      IsAffine ((E p t).obj i).left := by
    let h := isLimitOfPreserves B (tupleIsLimit (S i.unop) p t)
    have : ∀ z, IsAffine
        (((WidePullbackShape.wideCospan (D.obj (op i.unop.val))
          ((finiteEtaleCoverStageObject D i₀ W f i.unop) ∘ t)
          (fun k ↦ finiteEtaleCoverStageArrow D i₀ W f i.unop (t k))) ⋙ B).obj z) := by
      intro z
      cases z with
      | none => exact inferInstanceAs (IsAffine (D.obj (op i.unop.val)).left)
      | some k => exact stage_affine i.unop (t k)
    exact Scheme.isAffine_of_isLimit _ h
  have tuple_limit (p : ℕ) (t : Fin (p + 1) → Fin m) :
      IsLimit (P.mapCone (c p t)) := by
    let D' := tailInclusion i₀ ⋙ D ⋙ B
    let c₀ : Cone D' :=
      Cone.mk U.left
        { app := fun i ↦ P.map (π.app (op i.unop.val))
          naturality := by
            intro i j h
            have hn := π.naturality ((tailInclusion i₀).map h)
            change 𝟙 U ≫ π.app (op j.unop.val) =
              π.app (op i.unop.val) ≫ Q.map (D.map ((tailInclusion i₀).map h)) at hn
            rw [Category.id_comp] at hn
            change P.map (π.app (op j.unop.val)) =
              P.map (π.app (op i.unop.val)) ≫
                P.map (Q.map (D.map ((tailInclusion i₀).map h)))
            rw [← P.map_comp, hn] }
    have hc₀ : IsLimit c₀ :=
      (Functor.Initial.isLimitWhiskerEquiv (tailInclusion i₀) _).symm _hlim
    let i₀' : J := ⟨i₀, le_rfl⟩
    let bcone (z : Cone ((E p t ⋙ Q) ⋙ P)) : Cone D' :=
      Cone.mk z.pt
        { app := fun i ↦ z.π.app i ≫ B.map
            ((S i.unop).pr p t 0 ≫ finiteEtaleCoverStageArrow D i₀ W f i.unop (t 0))
          naturality := by
            intro i j h
            change z.π.app j ≫ B.map ((S j.unop).pr p t 0 ≫
              finiteEtaleCoverStageArrow D i₀ W f j.unop (t 0)) =
                (z.π.app i ≫ B.map ((S i.unop).pr p t 0 ≫
                  finiteEtaleCoverStageArrow D i₀ W f i.unop (t 0))) ≫
                    B.map (d j.unop i.unop h.unop)
            have hz := z.w h
            change z.π.app i ≫ B.map (r h.unop p t) = z.π.app j at hz
            rw [← hz, Category.assoc, ← B.map_comp, Category.assoc, ← B.map_comp]
            exact congrArg (fun q : (S i.unop).W p t ⟶ D.obj (op j.unop.val) ↦
              z.π.app i ≫ B.map q) (by
              rw [← Category.assoc, rpr h.unop, Category.assoc,
                vsnd j.unop i.unop h.unop]
              simp only [Category.assoc, finiteEtaleCoverStageArrow]) }
    let b (z : Cone ((E p t ⋙ Q) ⋙ P)) := hc₀.lift (bcone z)
    have bfac (z : Cone ((E p t ⋙ Q) ⋙ P)) (i : J) :
        b z ≫ P.map (π.app (op i.val)) = z.π.app (op i) ≫ B.map
          ((S i).pr p t 0 ≫ finiteEtaleCoverStageArrow D i₀ W f i (t 0)) :=
      hc₀.fac (bcone z) (op i)
    let a (z : Cone ((E p t ⋙ Q) ⋙ P)) (k : Fin (p + 1)) :=
      z.π.app (op i₀') ≫ B.map ((S i₀').pr p t k ≫ pullback.fst _ _)
    have afac (z : Cone ((E p t ⋙ Q) ⋙ P)) (i : J) (k) :
        a z k = z.π.app (op i) ≫ B.map ((S i).pr p t k ≫ pullback.fst _ _) := by
      dsimp only [a]
      rw [← z.w ((homOfLE (show i₀' ≤ i from i.property)).op)]
      change (_ ≫ B.map (r (homOfLE (show i₀' ≤ i from i.property)) p t)) ≫ _ = _
      rw [Category.assoc, ← B.map_comp]
      congr 2
      rw [← Category.assoc, rpr (homOfLE (show i₀' ≤ i from i.property)),
        Category.assoc, vfst i₀' i (homOfLE (show i₀' ≤ i from i.property))]
    let u (z : Cone ((E p t ⋙ Q) ⋙ P)) (k : Fin (p + 1)) :
        z.pt ⟶ P.obj (finiteEtaleCoverLimitObject D i₀ W f U π (t k)) :=
      pullback.lift (a z k) (b z) (by
        change a z k ≫ B.map (f (t k)) = b z ≫ P.map (π.app (op i₀))
        rw [afac z i₀', Category.assoc, ← B.map_comp, Category.assoc,
          pullback.condition, ← Category.assoc, B.map_comp]
        change _ = b z ≫ P.map (π.app (op i₀))
        rw [bfac z i₀']
        have hid : D.map (homOfLE i₀'.property).op = 𝟙 (D.obj (op i₀)) := by
          have he : (homOfLE i₀'.property).op = 𝟙 (op i₀) := Subsingleton.elim _ _
          exact (congrArg D.map he).trans (D.map_id _)
        have hid' : B.map (D.map (homOfLE i₀'.property).op) =
            𝟙 (B.obj (D.obj (op i₀))) := by rw [hid, B.map_id]
        rw [hid', Category.comp_id]
        exact congrArg (fun q ↦ z.π.app (op i₀') ≫ B.map q)
          ((S i₀').comm p t k)) ≫
        (PreservesPullback.iso P (Q.map (f (t k))) (π.app (op i₀))).inv
    have ufst (z : Cone ((E p t ⋙ Q) ⋙ P)) (k) :
        u z k ≫ P.map (pullback.fst _ _) = a z k := by
      change (pullback.lift (a z k) (b z) _ ≫
        (PreservesPullback.iso P (Q.map (f (t k))) (π.app (op i₀))).inv) ≫
          P.map (pullback.fst (Q.map (f (t k))) (π.app (op i₀))) = a z k
      rw [Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst]
    have usnd (z : Cone ((E p t ⋙ Q) ⋙ P)) (k) :
        u z k ≫ P.map (finiteEtaleCoverLimitArrow D i₀ W f U π (t k)) = b z := by
      change (pullback.lift (a z k) (b z) _ ≫
        (PreservesPullback.iso P (Q.map (f (t k))) (π.app (op i₀))).inv) ≫
          P.map (pullback.snd (Q.map (f (t k))) (π.app (op i₀))) = b z
      rw [Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]
    let l (z : Cone ((E p t ⋙ Q) ⋙ P)) : z.pt ⟶ (T.W p t).left :=
      tupleLift T P p t (u z) (fun k ↦ (usnd z k).trans (usnd z 0).symm)
    have lpr (z : Cone ((E p t ⋙ Q) ⋙ P)) (k) :
        l z ≫ P.map (T.pr p t k) = u z k := tupleLift_pr T P p t _ _ k
    have lf (z : Cone ((E p t ⋙ Q) ⋙ P)) (i : J) :
        l z ≫ P.map (s i p t) = z.π.app (op i) := by
      apply mapped_tuple_ext (S i) B
      intro k
      change (l z ≫ P.map (s i p t)) ≫ P.map (Q.map ((S i).pr p t k)) = _
      rw [Category.assoc, ← P.map_comp, spr, P.map_comp, ← Category.assoc, lpr]
      apply PullbackCone.IsLimit.hom_ext
        (isLimitOfHasPullbackOfPreservesLimit B (f (t k))
          (D.map (homOfLE i.property).op))
      · change (u z k ≫ P.map (w i (t k))) ≫
          P.map (Q.map (pullback.fst (f (t k))
            (D.map (homOfLE i.property).op))) =
              (z.π.app (op i) ≫ B.map ((S i).pr p t k)) ≫
                B.map (pullback.fst (f (t k)) (D.map (homOfLE i.property).op))
        rw [Category.assoc, ← P.map_comp, wfst, ufst, afac z i k]
        simp only [B.map_comp, Category.assoc]
      · change (u z k ≫ P.map (w i (t k))) ≫
          P.map (Q.map (pullback.snd (f (t k))
            (D.map (homOfLE i.property).op))) =
              (z.π.app (op i) ≫ B.map ((S i).pr p t k)) ≫
                B.map (pullback.snd (f (t k)) (D.map (homOfLE i.property).op))
        rw [Category.assoc, ← P.map_comp, wsnd, P.map_comp, ← Category.assoc, usnd,
          bfac z i]
        change z.π.app (op i) ≫ B.map ((S i).pr p t 0 ≫
          finiteEtaleCoverStageArrow D i₀ W f i (t 0)) =
            z.π.app (op i) ≫ B.map ((S i).pr p t k ≫
              finiteEtaleCoverStageArrow D i₀ W f i (t k))
        rw [(S i).comm p t k]
    refine ⟨l, ?_, ?_⟩
    · intro z i
      exact lf z i.unop
    · intro z e he
      apply mapped_tuple_ext T P
      intro k
      apply PullbackCone.IsLimit.hom_ext
        (isLimitOfHasPullbackOfPreservesLimit P (Q.map (f (t k))) (π.app (op i₀)))
      · change (e ≫ P.map (T.pr p t k)) ≫
          P.map (pullback.fst (Q.map (f (t k))) (π.app (op i₀))) =
            (l z ≫ P.map (T.pr p t k)) ≫
              P.map (pullback.fst (Q.map (f (t k))) (π.app (op i₀)))
        rw [lpr z k, ufst z k]
        have hz := congrArg (fun q ↦ q ≫ B.map
          ((S i₀').pr p t k ≫ pullback.fst _ _)) (he (op i₀'))
        change (e ≫ P.map (s i₀' p t)) ≫ _ = _ at hz
        change (e ≫ P.map (s i₀' p t)) ≫
          P.map (Q.map ((S i₀').pr p t k ≫ pullback.fst _ _)) = _ at hz
        rw [Category.assoc, ← P.map_comp, Q.map_comp,
          ← Category.assoc, spr, Category.assoc, wfst, P.map_comp] at hz
        simpa only [Category.assoc, B.map_comp, finiteEtaleCoverLimitArrow, a, Q] using hz
      · change (e ≫ P.map (T.pr p t k)) ≫
          P.map (finiteEtaleCoverLimitArrow D i₀ W f U π (t k)) =
            (l z ≫ P.map (T.pr p t k)) ≫
              P.map (finiteEtaleCoverLimitArrow D i₀ W f U π (t k))
        rw [lpr z k, usnd z k]
        apply hc₀.hom_ext
        intro i
        have hz := congrArg (fun q ↦ q ≫ B.map
          ((S i.unop).pr p t k ≫ finiteEtaleCoverStageArrow D i₀ W f i.unop (t k)))
            (he i)
        change (e ≫ P.map (s i.unop p t)) ≫ _ = _ at hz
        change (e ≫ P.map (s i.unop p t)) ≫
          P.map (Q.map ((S i.unop).pr p t k ≫
            finiteEtaleCoverStageArrow D i₀ W f i.unop (t k))) = _ at hz
        rw [Category.assoc, ← P.map_comp, Q.map_comp, ← Category.assoc,
          spr, Category.assoc, wsnd, P.map_comp, P.map_comp] at hz
        change (e ≫ P.map (T.pr p t k) ≫
          P.map (finiteEtaleCoverLimitArrow D i₀ W f U π (t k))) ≫
            P.map (π.app (op i.unop.val)) = _
        rw [bfac z i.unop, B.map_comp]
        rw [(S i.unop).comm p t k] at hz
        simpa only [Category.assoc, B.map_comp, finiteEtaleCoverLimitArrow] using hz
  let C (p : ℕ) (t : Fin (p + 1) → Fin m) :
      Cocone ((E p t).rightOp ⋙ F') :=
    { pt := G.obj (op (T.W p t))
      ι :=
        { app := fun i ↦ η.app (op ((S i).W p t)) ≫ G.map (s i p t).op
          naturality := by
            intro i j h
            change F'.map (r h p t).op ≫ _ = _ ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, η.naturality]
            change (η.app _ ≫ G.map (Q.map (r h p t)).op) ≫ _ = _
            rw [Category.assoc, ← G.map_comp, ← op_comp, sr h] } }
  have hC (p : ℕ) (t : Fin (p + 1) → Fin m) : IsColimit (C p t) := by
    letI := tuple_affine p t
    let h := (ProEtale.isColimit_comparisonUpperStar_mapCocone_of_isAffine
      (ModuleCat.{u + 1} Λ) F (E p t) (c p t) (tuple_limit p t)).some
    let e := asIso (Functor.whiskerLeft (E p t).op
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app F).hom)
    have h' := (IsColimit.precomposeHomEquiv e _).2 h
    exact isColimitOfPreserves (forget₂ (ModuleCat Λ) AddCommGrpCat)
      (h'.whiskerEquivalence (opOpEquivalence J).symm)
  have degree_colimit (p : ℕ) : IsColimit
      ((HomologicalComplex.eval AddCommGrpCat (.up ℕ) p).mapCocone K) := by
    let Ap := A ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℕ) p
    let α (t : Fin (p + 1) → Fin m) : Ap ⟶ (E p t).rightOp ⋙ F' :=
      { app := fun i ↦ coordinateProjection (fun t ↦ F'.obj (op ((S i).W p t))) t
        naturality := by intro i j h; rfl }
    have hα : IsLimit (Fan.mk Ap α) := by
      apply evaluationJointlyReflectsLimits
      intro i
      refine (Fan.isLimitMapConeEquiv ((evaluation J AddCommGrpCat).obj i)
        (fun t ↦ (E p t).rightOp ⋙ F') (Fan.mk Ap α)).symm ?_
      exact coordinateProduct (fun t ↦ F'.obj (op ((S i).W p t)))
    exact productColimit (fun t ↦ (E p t).rightOp ⋙ F') Ap α hα _ (C p) (hC p)
      (coordinateProjection (fun t ↦ G.obj (op (T.W p t))))
      (coordinateProduct (fun t ↦ G.obj (op (T.W p t)))) (by
        intro i t
        apply AddCommGrpCat.ext
        intro z
        rfl)
  have hK : IsColimit K := HomologicalComplex.isColimitOfEval _ K degree_colimit
  refine ⟨r, s, A, (fun _ ↦ Iso.refl _), K, Iso.refl _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h p t k
    constructor
    · rw [← Category.assoc, rpr h, Category.assoc, vfst i j h]
    · change r h p t ≫ (S i).pr p t k ≫ pullback.snd _ _ = _
      rw [← Category.assoc, rpr h, Category.assoc, vsnd i j h]
      rfl
  · intro i p t k
    constructor
    · rw [Q.map_comp, ← Category.assoc, spr, Category.assoc, wfst]
    · change s i p t ≫ Q.map ((S i).pr p t k ≫ pullback.snd _ _) = _
      rw [Q.map_comp, ← Category.assoc, spr, Category.assoc, wsnd]
  · intro i j h p z t
    simp [A, tupleCochainMap, F']
    rfl
  · intro i p z t
    simp [K, tupleCochainMap, G, η]
    rfl
  · refine ⟨⟨hK⟩, ?_, ?_⟩
    · have := extensionPreserves (I := J)
      exact ⟨isColimitOfPreserves _ hK⟩
    · intro q
      have := homologyPreserves (I := J) q
      exact ⟨isColimitOfPreserves _ hK⟩

end AlgebraicGeometry
