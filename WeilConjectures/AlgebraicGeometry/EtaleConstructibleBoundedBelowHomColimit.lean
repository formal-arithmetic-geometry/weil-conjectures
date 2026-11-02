/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.AlgebraicGeometry.EtaleConstructibleStratumFiltration
import WeilConjectures.AlgebraicGeometry.EtaleStratumHomContinuity
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Category.Grp.AB

/-! # Constructible global derived Hom and bounded-below filtered colimits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14,
Remark 6.3.15 and the filtered-colimit argument of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit).

Global Hom is the recorded `ExternalRHom.globalHom` (def-pur-external-rhom-pairing-interface):
the existing derived internal Hom followed by derived global sections.
For a functorial complex model `E` with its natural identification `e`, the comparison
is localization of `colimit.post`, followed by `e` at the colimit. Thus its domain is
the exact filtered colimit of the compatible complex representatives, not a colimit
chosen in the ordinary triangulated category. The model-free cohomology clause below
also states continuity without making a choice of functorial representatives.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

private theorem homColimit_iso
    {C : Type*} [Category.{u + 1} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ C) (c : Cocone D) {K L : C} (e : K ≅ L)
    (h : homColimitProperty D c K) : homColimitProperty D c L := by
  intro n
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (h n)
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    ⟨IsColimit.mapCoconeEquiv
      (Functor.isoWhiskerLeft (shiftFunctor C n)
        (preadditiveCoyoneda.mapIso e.symm.op)) hc⟩

private theorem homColimit_zero
    {C : Type*} [Category.{u + 1} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ C) (c : Cocone D) {K : C} (hK : IsZero K) :
    homColimitProperty D c K := by
  intro n
  have hz (M : C) : IsZero ((preadditiveCoyoneda.obj (op K)).obj M) := by
    apply (IsZero.iff_id_eq_zero _).2
    ext f
    exact hK.eq_of_src _ _
  apply IsZero.isIso
  · exact (colimit.isColimit _).isZero_pt ((Functor.isZero_iff _).2 (fun j ↦ hz _))
  · exact hz _

private theorem constructible_homColimit
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ b c : ℤ, DerivedCategory.hasTorAmplitudeIn A X b c K)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : ℤ) (hN : ∀ j : J, (_root_.DerivedCategory.Q.obj (N.obj j)).IsGE a) :
    homColimitProperty (N ⋙ _root_.DerivedCategory.Q)
      (_root_.DerivedCategory.Q.mapCocone (colimit.cocone N)) K := by
  obtain ⟨T, hTc, U, c, hc, P, s, F, hcomp, hb, hP, hF₀, ⟨eF⟩, htri⟩ :=
    exists_etaleConstructibleStratumFiltration A X K hK hTor
  let D := N ⋙ _root_.DerivedCategory.Q
  let d := _root_.DerivedCategory.Q.mapCocone (colimit.cocone N)
  have hgrade (i : Fin T.n) : homColimitProperty D d
      (((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj (P i))⟦s i⟧) := by
    have hlocal : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage (T.domain i),
        ∀ k : 𝒰.I₀, ∃ C : _root_.DerivedCategory (ModuleCat.{u + 1} A),
          _root_.DerivedCategory.IsPerfectRingComplex C ∧
          Nonempty ((ExternalRHom.pull A (𝒰.f k)).obj (P i) ≅
            (ExternalRHom.constant A (𝒰.X k)).obj C) := by
      obtain ⟨𝒰, h𝒰⟩ := hP i
      refine ⟨𝒰, fun k ↦ ?_⟩
      obtain ⟨C, hC, ⟨e⟩⟩ := h𝒰 k
      exact ⟨C, hC, ⟨(leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (𝒰.f k)).app (P i) ≪≫ e ≪≫
          ((constantSheaf (𝒰.X k).smallEtaleTopology
            (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.app C).symm⟩⟩
    have ha : Topology.IsConstructible (Set.range (c i ≫ (U i).ι)) := by
      rw [hcomp i, T.range_immersion]
      exact hTc i
    have H : homColimitProperty D d
        ((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj ((P i)⟦s i⟧)) := by
      intro q
      obtain ⟨hq⟩ := @etaleStratum_shiftedHom_isColimit _ _ _ _ _ _ _ _
        (c i) (hc i) (U i).ι inferInstance ha (P i) (hb i) hlocal (s i) _ _ _ N a hN q
      exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1 ⟨hq⟩
    exact homColimit_iso D d
      (((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).commShiftIso
        (s i)).app (P i)) H
  have hF : ∀ i : Fin (T.n + 1), homColimitProperty D d (F i) := by
    apply Fin.induction
    · exact homColimit_zero D d hF₀
    · intro i hi
      obtain ⟨f, g, h, ht⟩ := htri i
      exact homColimitProperty_extensions D d (Pretriangulated.Triangle.mk f g h)
        ht hi (hgrade i)
  exact homColimit_iso D d eF (hF (Fin.last T.n))

/-- The same continuity assertion on the original cocone, without a choice of model.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit).
Proof: use exact filtered colimits, finite perfect-stratum devissage, stratum continuity,
then extension closure of homColimitProperty. The global-Hom adjunction identifies
Hom(K,N[q]) with Hom(A[0],globalHom(K,N)[q]); the natural free-module/cohomology
equivalence identifies the latter with H^q. Transfer the colimit cocone through these
natural additive isomorphisms and reflect it along the forgetful functor from modules. -/
theorem constructibleGlobalHom_cohomology_isColimit
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hTor : ∃ b c : ℤ, DerivedCategory.hasTorAmplitudeIn A X b c K)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : ℤ) (_hN : ∀ j : J, (_root_.DerivedCategory.Q.obj (N.obj j)).IsGE a) (q : ℤ) :
    Nonempty (IsColimit
      ((_root_.DerivedCategory.Q ⋙ (ExternalRHom.globalHom A X).obj (op K) ⋙
        _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).mapCocone
          (colimit.cocone N))) := by
  let F := (ExternalRHom.globalHom A X).obj (op K)
  let P := ModuleCat.of A A
  let P₀ := (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj P
  let adj := ExternalRHom.globalAdjunction A K
  let : (ExternalRHom.constant A X).Additive :=
    Functor.additive_of_iso
      (constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.symm
  let : (ExternalRHom.constant A X).CommShift ℤ :=
    Functor.CommShift.ofIso
      (constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let : F.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let ε : (ExternalRHom.constant A X).obj P₀ ≅ 𝟙_ (DerivedCategoryModule A X) :=
    (Functor.singleFunctorCompLeftDerivedFunctorIso
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).app P ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (Functor.Monoidal.εIso
          (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).symm ≪≫
      _root_.DerivedCategory.singleFunctorObjUnitIso _
  let εK : (ExternalRHom.constant A X ⋙ tensorLeft K).obj P₀ ≅ K :=
    whiskerLeftIso K ε ≪≫ ρ_ K
  obtain ⟨e₀, he₀⟩ := AlgebraicGeometry.derivedFreeModule_hom_homology A
  let δ₀ : preadditiveCoyoneda.obj (op P₀) ≅
      _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0 ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat :=
    NatIso.ofComponents (fun M ↦ (e₀ M).toAddCommGrpIso) (fun f ↦ by
      ext g
      exact he₀ _ _ f g)
  let δ : shiftFunctor (_root_.DerivedCategory (ModuleCat.{u + 1} A)) q ⋙
      preadditiveCoyoneda.obj (op P₀) ≅
      _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat :=
    Functor.isoWhiskerLeft _ δ₀ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0).isoShift q) _
  let γ : F ⋙ _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat ≅
      shiftFunctor (DerivedCategoryModule A X) q ⋙ preadditiveCoyoneda.obj (op K) :=
    Functor.isoWhiskerLeft F δ.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.commShiftIso q).symm
        (preadditiveCoyoneda.obj (op P₀)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (shiftFunctor (DerivedCategoryModule A X) q)
        (adj.preadditiveCoyonedaObjIso P₀).symm ≪≫
      Functor.isoWhiskerLeft (shiftFunctor (DerivedCategoryModule A X) q)
        (preadditiveCoyoneda.mapIso εK.symm.op)
  have h := constructible_homColimit A X K _hK _hTor N a _hN q
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 h
  refine ⟨isColimitOfReflects (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat) ?_⟩
  exact IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft _root_.DerivedCategory.Q γ.symm) hc

end AlgebraicGeometry.Etale
