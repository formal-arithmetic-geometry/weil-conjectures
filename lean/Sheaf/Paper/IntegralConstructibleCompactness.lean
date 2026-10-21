/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.IntegralIndHeartRealization
import Sheaf.Paper.IntegralIndLowerTail
import Sheaf.Paper.IntegralWindowCoproductComparison
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Integral constructible complexes are compact

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-compactness,
sk-prop-int-compactness-compact.md and its proof
(blueprint: det-prop-int-compactness-compact).

The assertion bundle expands the three clauses with the actual ambient module category.
`H.ind` is the full replete filtered-colimit image IndCons; Dic is expanded cohomologically.
The realization is characterized as the filtered-colimit-preserving extension of the
inclusion along Ind.yoneda. Thus it sends every formal filtered diagram to its ambient
colimit, including the induced maps. No unconstrained realization functor is assumed.
All coproducts and truncations are in the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem homIso_first
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (C : D) (T : Triangle D) (hT : T ∈ distTriang D) (m : ℤ)
    (h₀ : Subsingleton (C ⟶ T.obj₃⟦m - 1⟧))
    (h₁ : Subsingleton (C ⟶ T.obj₃⟦m⟧)) :
    IsIso ((preadditiveCoyoneda.obj (op C)).map ((shiftFunctor D m).map T.mor₁)) := by
  let F := preadditiveCoyoneda.obj (op C)
  have : Mono ((F.shift m).map T.mor₁) := by
    apply (F.homologySequence_mono_shift_map_mor₁_iff T hT (m - 1) m (by omega)).2
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h₀).eq_of_src _ _
  have : Epi ((F.shift m).map T.mor₁) := by
    apply (F.homologySequence_epi_shift_map_mor₁_iff T hT m).2
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h₁).eq_of_tgt _ _
  change IsIso ((F.shift m).map _)
  exact isIso_of_mono_of_epi _

private theorem homIso_second
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (C : D) (T : Triangle D) (hT : T ∈ distTriang D) (m : ℤ)
    (h₀ : Subsingleton (C ⟶ T.obj₁⟦m⟧))
    (h₁ : Subsingleton (C ⟶ T.obj₁⟦m + 1⟧)) :
    IsIso ((preadditiveCoyoneda.obj (op C)).map ((shiftFunctor D m).map T.mor₂)) := by
  let F := preadditiveCoyoneda.obj (op C)
  have : Mono ((F.shift m).map T.mor₂) := by
    apply (F.homologySequence_mono_shift_map_mor₂_iff T hT m).2
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h₀).eq_of_src _ _
  have : Epi ((F.shift m).map T.mor₂) := by
    apply (F.homologySequence_epi_shift_map_mor₂_iff T hT m (m + 1) rfl).2
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr h₁).eq_of_tgt _ _
  change IsIso ((F.shift m).map _)
  exact isIso_of_mono_of_epi _

private theorem upperWindowIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (C : A) (K : DerivedCategory A) (m : ℤ) :
    IsIso ((preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj C))).map
      ((shiftFunctor (DerivedCategory A) m).map
        ((DerivedCategory.TStructure.t.truncLEι m).app K))) := by
  apply homIso_first _ _ (DerivedCategory.TStructure.t.triangleLEGT_distinguished m K) m
  · change Subsingleton (((DerivedCategory.singleFunctor A 0).obj C) ⟶
        ((DerivedCategory.TStructure.t.truncGT m).obj K)⟦m - 1⟧)
    have : DerivedCategory.TStructure.t.IsGE
        (((DerivedCategory.TStructure.t.truncGT m).obj K)⟦m - 1⟧) 2 :=
      DerivedCategory.TStructure.t.isGE_shift _ (m + 1) (m - 1) 2 (by omega)
    exact ⟨fun f g ↦ by
      rw [DerivedCategory.TStructure.t.zero f 0 2, DerivedCategory.TStructure.t.zero g 0 2]⟩
  · change Subsingleton (((DerivedCategory.singleFunctor A 0).obj C) ⟶
        ((DerivedCategory.TStructure.t.truncGT m).obj K)⟦m⟧)
    have : DerivedCategory.TStructure.t.IsGE
        (((DerivedCategory.TStructure.t.truncGT m).obj K)⟦m⟧) 1 :=
      DerivedCategory.TStructure.t.isGE_shift _ (m + 1) m 1 (by omega)
    exact ⟨fun f g ↦ by
      rw [DerivedCategory.TStructure.t.zero f 0 1, DerivedCategory.TStructure.t.zero g 0 1]⟩

private theorem coproductSmallSupport
    {D : Type u} [Category.{v} D] [Preadditive D]
    {I : Type w} (K : I → D) (c : Cofan K) (hc : IsColimit c) :
    Small.{v} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : c.pt ⟶ K i := hc.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : c.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    hc.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective.{v} (β := c.pt ⟶ c.pt)
    (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ c.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
  have hi : c.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem closedUnderCoproducts_of_small
    {D : Type u} [Category.{v} D] [Preadditive D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (hsmall : ∀ I : Type v, P.IsClosedUnderColimitsOfShape (Discrete I))
    (I : Type w) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
  classical
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let K : I → D := fun i ↦ F.obj ⟨i⟩
  let c : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
  have hc : IsColimit c := by
    let e : Discrete.functor K ≅ F := Discrete.natIso (fun _ ↦ Iso.refl _)
    apply IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv e (colimit.cocone F)).symm (colimit.isColimit F))
    exact Cocone.ext (Iso.refl _) (fun i ↦ by simp [e, c])
  have : Small.{v} {i // ¬ IsZero (K i)} := coproductSmallSupport K c hc
  let J := {i // ¬ IsZero (K i)}
  let r : Cofan (fun i : J ↦ K i.val) := Cofan.mk c.pt (fun i ↦ c.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ hc.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change c.ι.app ⟨i⟩ ≫ _ = _
      rw [hc.fac]
      simp only [Cofan.mk_ι_app, dif_pos hi]
    · intro s m hm
      apply hc.hom_ext
      intro ⟨i⟩
      rw [hc.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dif_pos hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let : P.IsClosedUnderColimitsOfShape (Discrete (Shrink.{v} J)) := hsmall _
  let : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J)).symm
  exact P.prop_of_isColimit (J := Discrete J) hr (fun i ↦ hF ⟨i.as.val⟩)

private theorem indDerivedStructure
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    (H : ObjectProperty A) [H.ind.{v}.ContainsZero]
    [H.ind.{v}.IsClosedUnderKernels] [H.ind.{v}.IsClosedUnderCokernels]
    [H.ind.{v}.IsClosedUnderExtensions]
    (hsums : ∀ I : Type v, H.ind.{v}.IsClosedUnderColimitsOfShape (Discrete I)) :
    (DerivedCategory.homologyProperty H.ind.{v}).IsTriangulated ∧
    (∀ I : Type u,
      (DerivedCategory.homologyProperty H.ind.{v}).IsClosedUnderColimitsOfShape (Discrete I)) ∧
    (∀ K : DerivedCategory A, DerivedCategory.homologyProperty H.ind.{v} K →
      ∀ m : ℤ,
        DerivedCategory.homologyProperty H.ind.{v}
          ((DerivedCategory.TStructure.t.truncLE m).obj K) ∧
        DerivedCategory.homologyProperty H.ind.{v}
          ((DerivedCategory.TStructure.t.truncGE m).obj K)) := by
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{v}
  let : HasColimitsOfSize.{v, v} A := IsGrothendieckAbelian.hasColimits A
  have hsmall (I : Type v) :
      (DerivedCategory.homologyProperty H.ind.{v}).IsClosedUnderColimitsOfShape (Discrete I) := by
    let : H.ind.{v}.IsClosedUnderColimitsOfShape (Discrete I) := hsums I
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩ n
    exact H.ind.prop_of_isColimit
      (isColimitOfPreserves (DerivedCategory.homologyFunctor A n) (colimit.isColimit F))
      (fun i ↦ hF i n)
  exact ⟨inferInstance, closedUnderCoproducts_of_small _ hsmall, fun K hK m ↦
    ⟨DerivedCategory.homologyProperty_truncLE hK m,
      DerivedCategory.homologyProperty_truncGE hK m⟩⟩

private theorem compact_reflects
    {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) F]
    (K : C) (hK : IsCompactObject (F.obj K)) : IsCompactObject K := by
  classical
  intro I A
  let e (L : C) : (K ⟶ L) ≃+ (F.obj K ⟶ F.obj L) :=
    AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩
  let ds := DirectSum.congrAddEquiv (fun i ↦ e (A i))
  let s := sigmaComparison F A
  let post : (F.obj K ⟶ F.obj (∐ A)) ≃+ (F.obj K ⟶ ∐ fun i ↦ F.obj (A i)) :=
    { toEquiv := Iso.homCongr (Iso.refl _) (asIso s).symm
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.add_comp] }
  let φ := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let ψ := DirectSum.toAddMonoid
    (fun i ↦ Preadditive.rightComp (F.obj K) (Sigma.ι (fun i ↦ F.obj (A i)) i))
  have hcomm : (post.toAddMonoidHom.comp (e (∐ A)).toAddMonoidHom).comp φ =
      ψ.comp ds.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    change post (e (∐ A) (φ (DirectSum.of _ i f))) =
      ψ (ds (DirectSum.of _ i f))
    rw [show φ (DirectSum.of _ i f) = f ≫ Sigma.ι A i from
      DirectSum.toAddMonoid_of
        (fun i ↦ Preadditive.rightComp K (Sigma.ι A i)) i f]
    rw [show ds (DirectSum.of _ i f) = DirectSum.of _ i (e (A i) f) from
      DirectSum.map_of (fun i ↦ (e (A i)).toAddMonoidHom) i f]
    rw [show ψ (DirectSum.of _ i (e (A i) f)) =
        e (A i) f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i from
      DirectSum.toAddMonoid_of
        (fun i ↦ Preadditive.rightComp (F.obj K) (Sigma.ι (fun i ↦ F.obj (A i)) i)) i _]
    dsimp [post, e, Iso.homCongr, AddEquiv.ofBijective]
    simp only [Category.id_comp]
    change F.map (f ≫ Sigma.ι A i) ≫ inv s =
      F.map f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i
    rw [Functor.map_comp, Category.assoc, map_ι_comp_inv_sigmaComparison]
  have hb : Function.Bijective (fun x ↦ post (e (∐ A) (φ x))) := by
    have heq : (fun x ↦ post (e (∐ A) (φ x))) = (fun x ↦ ψ (ds x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [heq]
    exact (hK I (fun i ↦ F.obj (A i))).comp ds.bijective
  constructor
  · intro x y hxy
    exact hb.1 (congrArg (fun z ↦ post (e (∐ A) z)) hxy)
  · intro f
    obtain ⟨x, hx⟩ := hb.2 (post (e (∐ A) f))
    exact ⟨x, (e (∐ A)).injective (post.injective hx)⟩

private theorem compact_devissage_and_restrict
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [HasCoproducts.{v} (DerivedCategory A)]
    (H : ObjectProperty A) [H.IsClosedUnderIsomorphisms]
    (P L : ObjectProperty (DerivedCategory A))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [L.IsTriangulated] [L.IsClosedUnderIsomorphisms]
    [∀ I : Type v, P.IsClosedUnderColimitsOfShape (Discrete I)]
    [∀ I : Type v, L.IsClosedUnderColimitsOfShape (Discrete I)]
    (hLP : L ≤ P)
    (hsingle : ∀ C : A, H C →
      ∃ hC : P ((DerivedCategory.singleFunctor A 0).obj C),
        IsCompactObject.{v}
          (ObjectProperty.FullSubcategory.mk ((DerivedCategory.singleFunctor A 0).obj C) hC))
    (K : L.FullSubcategory)
    (hK : DerivedCategory.TStructure.t.bounded K.obj ∧
      ∀ n : ℤ, H ((DerivedCategory.homologyFunctor A n).obj K.obj)) :
    IsCompactObject.{v} K := by
  let : HasCoproducts.{v} P.FullSubcategory := fun I ↦ inferInstance
  let : HasCoproducts.{v} L.FullSubcategory := fun I ↦ inferInstance
  let R : ObjectProperty P.FullSubcategory := fun K ↦ IsCompactObject.{v} K
  let : R.IsTriangulated := (compactObjects_isThick (C := P.FullSubcategory)).1
  let : R.IsStableUnderRetracts := (compactObjects_isThick (C := P.FullSubcategory)).2
  let Q := R.map P.ι
  have hQ : Q K.obj := by
    apply DerivedCategory.prop_of_bounded Q H ?_ K.obj hK.1 hK.2
    intro C hC
    obtain ⟨h, hc⟩ := hsingle C hC
    exact ⟨⟨_, h⟩, hc, ⟨Iso.refl _⟩⟩
  let F : L.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift L.ι (fun K ↦ hLP K.obj K.property)
  have hpres (I : Type v) : PreservesColimitsOfShape (Discrete I) F := by
    have : PreservesColimitsOfShape (Discrete I) (F ⋙ P.ι) :=
      preservesColimitsOfShape_of_natIso (P.liftCompιIso L.ι _).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves F P.ι
  let := hpres
  obtain ⟨J, hJ, ⟨e⟩⟩ := hQ
  let e' : J ≅ F.obj K := P.fullyFaithfulι.preimageIso e
  have : IsCompactObject (F.obj K) := R.prop_of_iso e' hJ
  exact compact_reflects F K this

private theorem single_ind_homology
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (H : ObjectProperty A) [H.ind.{v}.ContainsZero] (N : A) (hN : H.ind.{v} N) :
    DerivedCategory.homologyProperty H.ind.{v} ((DerivedCategory.singleFunctor A 0).obj N) := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact H.ind.prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app N).symm hN
  · apply H.ind.prop_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

private theorem lowerWindowIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (H : ObjectProperty A) [H.ind.{v}.ContainsZero]
    (C : A) (d : ℕ)
    (htail : ∀ L : DerivedCategory A,
      DerivedCategory.homologyProperty H.ind.{v} L → L.IsLE (-(d : ℤ) - 1) →
      Subsingleton (((DerivedCategory.singleFunctor A 0).obj C) ⟶ L))
    (K : DerivedCategory A) (hK : DerivedCategory.homologyProperty H.ind.{v} K) (m : ℤ) :
    IsIso ((preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj C))).map
      ((shiftFunctor (DerivedCategory A) m).map
        ((DerivedCategory.TStructure.t.truncGEπ (m - (d : ℤ))).app
          ((DerivedCategory.TStructure.t.truncLE m).obj K)))) := by
  let V := (DerivedCategory.TStructure.t.truncLT (m - (d : ℤ))).obj
    ((DerivedCategory.TStructure.t.truncLE m).obj K)
  have hV : DerivedCategory.homologyProperty H.ind.{v} V :=
    (DerivedCategory.homologyProperty H.ind).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT
        (m - (d : ℤ) - 1) (m - (d : ℤ)) (by omega)).app _)
      (DerivedCategory.homologyProperty_truncLE
        (DerivedCategory.homologyProperty_truncLE hK m) (m - (d : ℤ) - 1))
  have hshift (s : ℤ) : DerivedCategory.homologyProperty H.ind.{v} (V⟦s⟧) :=
    (DerivedCategory.homologyProperty H.ind).le_shift s _ hV
  apply homIso_second _ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished
    (m - (d : ℤ)) ((DerivedCategory.TStructure.t.truncLE m).obj K)) m
  · apply htail _ (hshift m)
    exact DerivedCategory.TStructure.t.isLE_shift _ (m - (d : ℤ) - 1) m _ (by omega)
  · apply htail _ (hshift (m + 1))
    have : (V⟦m + 1⟧).IsLE (-(d : ℤ) - 2) :=
      DerivedCategory.TStructure.t.isLE_shift _ (m - (d : ℤ) - 1) (m + 1) _ (by omega)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (-(d : ℤ) - 2) _ (by omega)

open Classical in
private theorem compact_of_window_comparison
    {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasCoproducts.{v} C]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    (K : C) (W : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ preadditiveCoyoneda.obj (op (F.obj K)) ≅ W)
    (hw : ∀ (I : Type v) (L : I → C),
      Function.Bijective (DirectSum.toAddMonoid
        (fun i ↦ (W.map (Sigma.ι L i)).hom))) : IsCompactObject K := by
  classical
  intro I L
  let a (N : C) : (K ⟶ N) ≃+ W.obj N :=
    (AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩).trans
      (e.app N).addCommGroupIsoToAddEquiv
  let ds := DirectSum.congrAddEquiv (fun i ↦ a (L i))
  let φ := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι L i))
  let ψ := DirectSum.toAddMonoid (fun i ↦ (W.map (Sigma.ι L i)).hom)
  have hcomm : (a (∐ L)).toAddMonoidHom.comp φ = ψ.comp ds.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    change a (∐ L) (φ (DirectSum.of _ i f)) = ψ (ds (DirectSum.of _ i f))
    rw [show φ (DirectSum.of _ i f) = f ≫ Sigma.ι L i from
      DirectSum.toAddMonoid_of
        (fun i ↦ Preadditive.rightComp K (Sigma.ι L i)) i f]
    rw [show ds (DirectSum.of _ i f) = DirectSum.of _ i (a (L i) f) from
      DirectSum.map_of (fun i ↦ (a (L i)).toAddMonoidHom) i f]
    rw [show ψ (DirectSum.of _ i (a (L i) f)) =
        (W.map (Sigma.ι L i)).hom (a (L i) f) from
      DirectSum.toAddMonoid_of (fun i ↦ (W.map (Sigma.ι L i)).hom) i _]
    have he := congrArg (fun g ↦ g.hom (F.map f)) (e.hom.naturality (Sigma.ι L i))
    change (e.hom.app (∐ L)).hom (F.map (f ≫ Sigma.ι L i)) = _
    rw [Functor.map_comp]
    exact he
  have hb : Function.Bijective (fun x ↦ a (∐ L) (φ x)) := by
    have heq : (fun x ↦ a (∐ L) (φ x)) = (fun x ↦ ψ (ds x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [heq]
    exact (hw I L).comp ds.bijective
  constructor
  · intro x y hxy
    exact hb.1 (congrArg (a (∐ L)) hxy)
  · intro f
    obtain ⟨x, hx⟩ := hb.2 (a (∐ L) f)
    exact ⟨x, (a (∐ L)).injective hx⟩

private theorem unshift_hom_iso
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    (C : D) {K L : D} (f : K ⟶ L)
    [IsIso ((preadditiveCoyoneda.obj (op C)).map ((shiftFunctor D (0 : ℤ)).map f))] :
    IsIso ((preadditiveCoyoneda.obj (op C)).map f) := by
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (shiftFunctorZero D ℤ) (preadditiveCoyoneda.obj (op C))) f).1
      (show IsIso ((preadditiveCoyoneda.obj (op C)).map
        ((shiftFunctor D (0 : ℤ)).map f)) from inferInstance)

/-- The three assertions of integral compactness, with the ambient category and its
constructible classes as parameters. Source: blueprint main-20261015,
sk-prop-int-compactness-compact, clauses 1--3
(blueprint: det-prop-int-compactness-compact).

Exactness means preservation of finite limits and finite colimits, whose existence
in Ind is included. The natural isomorphism on representables and preservation of
filtered colimits specify the colimit realization up to its unique compatible
isomorphism. The window clause asserts invertibility of the two actual Hom maps of
`K <- tau_le(m) K -> tau_ge(m-d_C) tau_le(m) K`, after shifting by m. Their composite,
inverting the first map, is the asserted natural isomorphism. The final clause uses
the recorded compact-object definition on the full localizing subcategory itself. -/
def IntegralConstructibleCompactnessAssertions
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (H : ObjectProperty A) (B : ObjectProperty (DerivedCategory A))
    (d : H.FullSubcategory → ℕ) : Prop :=
  (HasFiniteLimits (Ind H.FullSubcategory) ∧
    HasFiniteColimits (Ind H.FullSubcategory) ∧
    ∃ Φ : Ind H.FullSubcategory ⥤ A,
      Nonempty (Ind.yoneda ⋙ Φ ≅ H.ι) ∧ PreservesFilteredColimits.{v} Φ ∧
      PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧ Φ.Full ∧ Φ.Faithful ∧
      Φ.essImage = H.ind.{v} ∧
      (∀ S : ShortComplex A, S.ShortExact →
        H.ind.{v} S.X₁ → H.ind.{v} S.X₃ → H.ind.{v} S.X₂) ∧
      (∀ (M N : A) (f : M ⟶ N), H.ind.{v} M → H.ind.{v} N →
        H.ind.{v} (kernel f) ∧ H.ind.{v} (cokernel f)) ∧
      (∀ (C : H.FullSubcategory) (N : A), H.ind.{v} N →
        ∀ q : ℤ, (d C : ℤ) < q →
          Subsingleton (((DerivedCategory.singleFunctor A 0).obj C.obj) ⟶
            ((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧))) ∧
  ((∀ (I : Type v) (K : I → DerivedCategory A),
      (∀ (i : I) (n : ℤ), H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        ∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj c.pt)) ∧
    (∀ K : DerivedCategory A,
      (∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
      ∀ (m n : ℤ),
        H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj K)) ∧
        H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj
          ((DerivedCategory.TStructure.t.truncGE m).obj K))) ∧
    (∀ K : DerivedCategory A, localizingClosure B K →
      ∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) ∧
    (∀ (C : H.FullSubcategory) (K : DerivedCategory A),
      (∀ n : ℤ, H.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
      ∀ m : ℤ,
        IsIso ((preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor A 0).obj C.obj))).map
            ((shiftFunctor (DerivedCategory A) m).map
              ((DerivedCategory.TStructure.t.truncLEι m).app K))) ∧
        IsIso ((preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor A 0).obj C.obj))).map
            ((shiftFunctor (DerivedCategory A) m).map
              ((DerivedCategory.TStructure.t.truncGEπ (m - (d C : ℤ))).app
                ((DerivedCategory.TStructure.t.truncLE m).obj K)))))) ∧
  (∃ hc : HasCoproducts.{v} (localizingClosure B).FullSubcategory,
    ∀ C : (localizingClosure B).FullSubcategory, B C.obj →
      @CategoryTheory.IsCompactObject _ _ _ hc C)

open Classical in
private theorem compactness_from_integral_inputs
    {A : Type (v + 1)} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    (H : ObjectProperty A) (B : ObjectProperty (DerivedCategory A))
    (d : H.FullSubcategory → ℕ)
    (hreal : H.IsClosedUnderIsomorphisms ∧ H.ind.{v}.ContainsZero ∧
      H.ind.{v}.IsClosedUnderKernels ∧ H.ind.{v}.IsClosedUnderCokernels ∧
      H.ind.{v}.IsClosedUnderExtensions ∧
      (∀ I : Type v, H.ind.{v}.IsClosedUnderColimitsOfShape (Discrete I)) ∧
      HasFiniteLimits (Ind H.FullSubcategory) ∧ HasFiniteColimits (Ind H.FullSubcategory) ∧
      ∃ Φ : Ind H.FullSubcategory ⥤ A,
        Nonempty (Ind.yoneda ⋙ Φ ≅ H.ι) ∧ PreservesFilteredColimits.{v} Φ ∧
        PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧ Φ.Full ∧ Φ.Faithful ∧
        Φ.essImage = H.ind.{v})
    (htail : ∀ (C : H.FullSubcategory) (L : DerivedCategory A),
      DerivedCategory.homologyProperty H.ind.{v} L → L.IsLE (-(d C : ℤ) - 1) →
      Subsingleton (((DerivedCategory.singleFunctor A 0).obj C.obj) ⟶ L))
    (hwindow : ∀ (C : H.FullSubcategory) (a : ℕ)
      (I : Type v) (K : I → DerivedCategory A) (c : Cofan K), IsColimit c →
      let W := DerivedCategory.TStructure.t.truncLE 0 ⋙
        DerivedCategory.TStructure.t.truncGE (-(a : ℤ)) ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj C.obj))
      Function.Bijective (DirectSum.toAddMonoid (fun i ↦ (W.map (c.inj i)).hom)))
    (hlocalL : IsLocalizingSubcategory (localizingClosure B))
    (hB : B ≤ DerivedCategory.TStructure.t.bounded ⊓
      fun K ↦ ∀ n : ℤ, H ((DerivedCategory.homologyFunctor A n).obj K)) :
    IntegralConstructibleCompactnessAssertions H B d := by
  classical
  let P := DerivedCategory.homologyProperty H.ind.{v}
  let L := localizingClosure B
  obtain ⟨hiso, hzero, hker, hcoker, hext, hsums, hlim, hcolim, Φ,
      hΦ₀, hΦfil, hΦlim, hΦcolim, hΦfull, hΦfaith, hΦimage⟩ :=
    hreal
  let := hiso
  let := hzero
  let := hker
  let := hcoker
  let := hext
  let := hlim
  let := hcolim
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{v}
  let : HasColimitsOfSize.{v, v} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{v} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  let : HasCoproducts.{v} (DerivedCategory A) := derived_hasCoproducts
  obtain ⟨htri, hPsums, htrunc⟩ := indDerivedStructure H hsums
  let := htri
  let (I : Type (v + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := hPsums I
  let (I : Type (v)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{v + 1} I ≃ I))
  have hlocalP : IsLocalizingSubcategory P := by
    refine ⟨htri, inferInstance, ?_⟩
    intro I F hF hK
    let := hF
    exact P.prop_colimit _ (fun i ↦ hK i.as)
  have hBP : B ≤ P := fun K hK n ↦ H.le_ind _ ((hB _ hK).2 n)
  have hLP : L ≤ P := fun K hK ↦ hK P hlocalP hBP
  let := hlocalL.1
  let := hlocalL.2.1
  let (I : Type (v + 1)) : L.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    exact hlocalL.2.2 F inferInstance (fun i ↦ hF ⟨i⟩)
  let (I : Type (v)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{v + 1} I ≃ I))
  let : HasCoproducts.{v} L.FullSubcategory := fun I ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete I) L
  let : HasCoproducts.{v} P.FullSubcategory := fun I ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete I) P
  have hbound (C : H.FullSubcategory) (N : A) (hN : H.ind.{v} N)
      (q : ℤ) (hq : (d C : ℤ) < q) :
      Subsingleton (((DerivedCategory.singleFunctor A 0).obj C.obj) ⟶
        ((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧) := by
    apply htail C _ ((DerivedCategory.homologyProperty H.ind).le_shift q _
      (single_ind_homology H N hN))
    have : (((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧).IsLE (-q) :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 q (-q) (by omega)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (-q) _ (by omega)
  have hsingle (C : A) (hC : H C) :
      ∃ hC' : P ((DerivedCategory.singleFunctor A 0).obj C),
        IsCompactObject.{v}
          (ObjectProperty.FullSubcategory.mk ((DerivedCategory.singleFunctor A 0).obj C) hC') := by
    let C' : H.FullSubcategory := ⟨C, hC⟩
    let S := (DerivedCategory.singleFunctor A 0).obj C
    have hS : P S := single_ind_homology H C (H.le_ind _ hC)
    let S' : P.FullSubcategory := ⟨S, hS⟩
    let Y := preadditiveCoyoneda.obj (op S)
    let U : DerivedCategory A ⥤ DerivedCategory A :=
      DerivedCategory.TStructure.t.truncLE (0 : ℤ)
    let V : DerivedCategory A ⥤ DerivedCategory A :=
      DerivedCategory.TStructure.t.truncGE (-(d C' : ℤ))
    let W := P.ι ⋙ U ⋙ V ⋙ Y
    have hu (K : P.FullSubcategory) : IsIso (Y.map
        ((DerivedCategory.TStructure.t.truncLEι 0).app K.obj)) := by
      have := upperWindowIso (A := A) C K.obj 0
      exact unshift_hom_iso S _
    have hv (K : P.FullSubcategory) : IsIso (Y.map
        ((DerivedCategory.TStructure.t.truncGEπ (-(d C' : ℤ))).app (U.obj K.obj))) := by
      have hh := lowerWindowIso H C (d C') (htail C') K.obj K.property 0
      have : IsIso (Y.map ((shiftFunctor (DerivedCategory A) (0 : ℤ)).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(d C' : ℤ))).app (U.obj K.obj)))) := by
        dsimp only [Y, S, U]
        have he : (0 : ℤ) - (d C' : ℤ) = -(d C' : ℤ) := by omega
        rw [he] at hh
        exact hh
      exact unshift_hom_iso S _
    let := hu
    let := hv
    let a : P.ι ⋙ U ⋙ Y ≅ P.ι ⋙ Y :=
      NatIso.ofComponents (fun K ↦ asIso (Y.map
        ((DerivedCategory.TStructure.t.truncLEι 0).app K.obj)))
        (fun f ↦ (Functor.whiskerLeft P.ι
          (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι 0) Y)).naturality f)
    let b : P.ι ⋙ U ⋙ Y ≅ W :=
      NatIso.ofComponents (fun K ↦ asIso (Y.map
        ((DerivedCategory.TStructure.t.truncGEπ (-(d C' : ℤ))).app (U.obj K.obj))))
        (fun f ↦ (Functor.whiskerLeft (P.ι ⋙ U)
          (Functor.whiskerRight
            (DerivedCategory.TStructure.t.truncGEπ (-(d C' : ℤ))) Y)).naturality f)
    refine ⟨hS, compact_of_window_comparison P.ι S' W (a.symm ≪≫ b) ?_⟩
    intro I K
    let c : Cofan (fun i ↦ (K i).obj) :=
      Cofan.mk (P.ι.obj (∐ K)) (fun i ↦ P.ι.map (Sigma.ι K i))
    have hc : IsColimit c := (isColimitMapCoconeCofanMkEquiv P.ι K _).1
      (isColimitOfPreserves P.ι (coproductIsCoproduct K))
    have hw := hwindow C' (d C') I
      (fun i ↦ (K i).obj) c hc
    exact hw
  refine ⟨⟨hlim, hcolim, Φ, hΦ₀, hΦfil, hΦlim, hΦcolim, hΦfull, hΦfaith,
    hΦimage, ?_, ?_, hbound⟩, ⟨?_, ?_, hLP, ?_⟩, ⟨inferInstance, ?_⟩⟩
  · intro S hS h₁ h₃
    exact H.ind.prop_X₂_of_shortExact hS h₁ h₃
  · intro M N f hM hN
    exact ⟨H.ind.prop_kernel f hM hN, H.ind.prop_cokernel f hM hN⟩
  · intro I K hK
    refine ⟨Cofan.mk (∐ K) (Sigma.ι K), coproductIsCoproduct K, ?_⟩
    exact P.prop_colimit _ (fun i ↦ hK i.as)
  · intro K hK m n
    exact ⟨(htrunc K hK m).1 n, (htrunc K hK m).2 n⟩
  · intro C K hK m
    exact ⟨upperWindowIso C.obj K m, lowerWindowIso H C.obj (d C) (htail C) K hK m⟩
  · intro K hK
    exact compact_devissage_and_restrict H P L hLP hsingle K (hB _ hK)


/-- Integral constructible complexes are compact in their localizing closure, together
with the exact Ind realization, extension/kernel/cokernel closure, uniform Ext bound,
and canonical finite-window assertions. Source: blueprint main-20261015,
sk-prop-int-compactness-compact, all three clauses
(blueprint: det-prop-int-compactness-compact).

Proof plan, following the fifteen DAG steps:
1. Use the internal-module/section-ring-sheaf equivalence and the Grothendieck
   ring-sheaf theorem for exact filtered colimits. The integral heart is essentially
   small, abelian with ambient kernels/cokernels, and extension closed. Integral Ext
   continuity gives Hom and Ext^1 continuity; singleFunctor is fully faithful.
2. Compute Hom between two realized filtered diagrams as lim_i colim_j Hom(C_i,D_j).
   This proves full faithfulness and the stated essential image. The presheaf
   universal property and lem-sfb-ind-filtered-colimits give filtered-colimit
   preservation and the realization isomorphism on representables.
3. Finite sums are realized over products of the filtered indices. An arbitrary
   sum is the filtered colimit of its finite partial sums; include the empty sum.
4. Present an Ind arrow over one filtered index using lem-sfb-ind-arrow-presentation.
   Exact filtered colimits identify its kernel/cokernel with the colimits of their
   constructible counterparts. The image is abelian with ambient exact structure;
   transport that structure through the fully faithful realization for exactness.
5. Pull an extension back along each stage C_a of its quotient. Ext^1 continuity
   lifts its class to an extension by one constructible stage D_i. The Yoneda/derived
   Ext comparison, pushout-short-exact-sequence theorem and short five lemma identify
   the pulled-back extension with the pushout of that finite-stage extension.
6. Over i/I, the pushouts D_j amalgamated with its constructible middle term are
   constructible and have colimit the pulled-back extension. The undercategory is
   filtered and its diagram of D_j still has the original kernel as colimit.
7. The colimit of the pulled-back extensions is the original extension, by exact
   filtered colimits and the short five lemma. This proves extension closure.
8. Ext continuity extends the chosen bound d_C from constructible sheaves to
   their filtered colimits. Finite partial sums give continuity for arbitrary sums.
9. Long exact cohomology, kernel/cokernel/extension closure make Dic triangulated.
   Truncations retain or kill cohomology; termwise derived sums commute with
   cohomology. Thus Dic is sum closed and contains Dbc and hence its localizing closure.
10. For bounded lower tails, remove the highest cohomology successively. Each Hom
    layer vanishes by the Ext bound; exact Hom into the truncation triangle gives zero.
11. For unbounded lower tails use pro-etale left completeness and derived products.
    In the Milnor sequence the Hom limit is zero. The degree -1 tower becomes
    isomorphisms beyond d_C; recursively solving 1-T gives zero cokernel and zero Hom.
12. The upper truncation triangle has Hom-zero outer terms in degrees 1 and 2 by
    t-structure orthogonality. The lower triangle has tails ending at -d_C-1 and
    -d_C-2 after shift; step 11 kills both. Hence both canonical Hom arrows are isos.
13. Represent a family in one finite cohomological interval by complexes with a
    common lower bound. Ext continuity for the filtered diagram of finite partial
    sums gives the direct-sum comparison, with its actual coprojection maps.
14. Apply the finite-window reduction simultaneously to each summand and its sum.
    Exact sums commute with both truncations. Naturality makes the coprojection
    square commute, giving compactness of constructible sheaves without a bound
    on the original family.
15. Compact objects are thick (lem-sc-compact-objects-thick). Shifts and finite
    truncation devissage extend compactness to every bounded constructible complex. -/
theorem integralConstructibleCompactness
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X → ℕ)
    (hd : ∀ (C N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (q : ℤ), (d C : ℤ) < q →
        Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧)) :
    IntegralConstructibleCompactnessAssertions
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) d := by
  exact compactness_from_integral_inputs _ _ d
    (integralIndHeartRealization ℓ E k p hp hpℓ X)
    (integralIndLowerTail ℓ E k p hp hpℓ X d hd)
    (integralWindowCoproductComparison ℓ E k p hp hpℓ X)
    (localizingClosure_exists (Profinite.padicIntegersRingObj ℓ E) X _).2.2.2.1
    (fun _ h ↦ h)

end AlgebraicGeometry.ProEtale
