/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.EtaleConstructibleStratumFiltration
import WeilConjectures.AlgebraicGeometry.EtaleStratumHomContinuity
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

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

/-- The cocone-induced comparison on compatible functorial complex representatives.
`e` identifies the model as global derived Hom, including its transition maps.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit). -/
def constructibleGlobalHomColimitComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X)
    (E : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K))
    {J : Type (u + 1)} [SmallCategory J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    _root_.DerivedCategory.Q.obj (colimit (N ⋙ E)) ⟶
      ((ExternalRHom.globalHom A X).obj (op K)).obj
        (_root_.DerivedCategory.Q.obj (colimit N)) :=
  _root_.DerivedCategory.Q.map (colimit.post N E) ≫ e.hom.app (colimit N)

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

/-- The canonical global derived-Hom comparison is invertible for every compatible
functorial complex model, for a bounded constructible finite-Tor source and a target
diagram with one common cohomological lower bound. No condition is imposed on the
constructibility of the targets or the cohomological dimension of the scheme.
Source: Bhatt--Scholze, Lemma 6.3.14, Remark 6.3.15 and Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit).

Proof:
1. Filtered colimits of etale module sheaves are exact by the Grothendieck property.
Hence homology preserves these colimits
(src-weil-homology-preserves-exact-colimits), as do changes by compatible quasi-isomorphisms.
2. Apply lem-per-etale-constructible-stratum-filtration to obtain a finite triangle
filtration of K with shifted locally closed extensions of locally constant perfect factors.
3. Apply lem-per-etale-stratum-hom-continuity to every factor and every shift. This is
homColimitProperty for the image under Q of the given termwise-colimit cocone.
4. By lem-weil-pbc-hom-colimit-extension and exact filtered colimits of abelian groups,
this property is closed under extensions. Induction on the finite filtration gives it for K.
5. Use the global-Hom adjunction, preservation of the unit by the constant-sheaf
functor, and lem-pc-derived-free-module-hom-homology to identify H^q globalHom(K,N)
with Hom(K,N[q]), naturally in N. The preceding cohomology-cocone theorem transports
this colimit property to any model E. Exactness of coefficient-module colimits and
src-weil-homology-preserves-exact-colimits identify the cohomology of the source.
The actual comparison is therefore invertible on every cohomology object, hence is an
isomorphism in D(A) by def-weil-abstract-derived-category. The identification e transports
this calculation to any compatible functorial model E. -/
theorem isIso_constructibleGlobalHomColimitComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hTor : ∃ b c : ℤ, DerivedCategory.hasTorAmplitudeIn A X b c K)
    (E : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K))
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : ℤ) (_hN : ∀ j : J, (_root_.DerivedCategory.Q.obj (N.obj j)).IsGE a) :
    IsIso (constructibleGlobalHomColimitComparison A X K E e N) := by
  have hpost : QuasiIso (colimit.post N E) := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q
    let ε : E ⋙ H ≅ _root_.DerivedCategory.Q ⋙
        (ExternalRHom.globalHom A X).obj (op K) ⋙
          _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q :=
      (Functor.isoWhiskerLeft E
        (_root_.DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q)).symm ≪≫
        Functor.isoWhiskerRight e
          (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q)
    obtain ⟨hc⟩ := constructibleGlobalHom_cohomology_isColimit A X K _hK _hTor N a _hN q
    have : IsIso (colimit.post N (E ⋙ H)) :=
      (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
        ⟨IsColimit.mapCoconeEquiv ε.symm hc⟩
    have : IsIso (colimit.post (N ⋙ E) H ≫ H.map (colimit.post N E)) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (N ⋙ E) H) (H.map (colimit.post N E))
  have : IsIso (_root_.DerivedCategory.Q.map (colimit.post N E)) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hpost
  dsimp only [constructibleGlobalHomColimitComparison]
  infer_instance

/-- Naturality in the source (contravariantly) and the target diagram (covariantly).
The compatibility equation says η represents precisely precomposition with f.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit).
Proof: precompose with each colimit injection. The defining equation of colimit.post
reduces the square to naturality of η and e, the stated compatibility with f, and
bifunctoriality of derived internal Hom. Uniqueness in the colimit universal property
then gives the equality. This is the formal naturality clause of DAG step 5. -/
theorem constructibleGlobalHomColimitComparison_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K K' : DerivedCategoryModule A X) (f : K' ⟶ K)
    (E E' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K))
    (e' : E' ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K'))
    (η : E ⟶ E')
    (_hη : Functor.whiskerRight η _root_.DerivedCategory.Q ≫ e'.hom =
      e.hom ≫ Functor.whiskerLeft _root_.DerivedCategory.Q
        ((ExternalRHom.globalHom A X).map f.op))
    {J : Type (u + 1)} [SmallCategory J]
    (N N' : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (α : N ⟶ N') :
    _root_.DerivedCategory.Q.map
        (colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E')) ≫
      constructibleGlobalHomColimitComparison A X K' E' e' N' =
    constructibleGlobalHomColimitComparison A X K E e N ≫
      ((ExternalRHom.globalHom A X).map f.op).app
        (_root_.DerivedCategory.Q.obj (colimit N)) ≫
      ((ExternalRHom.globalHom A X).obj (op K')).map
        (_root_.DerivedCategory.Q.map (colim.map α)) := by
  have hpost :
      colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E') ≫
        colimit.post N' E' =
      colimit.post N E ≫ η.app (colimit N) ≫ E'.map (colim.map α) := by
    apply colimit.hom_ext
    intro j
    simp only [colimit.ι_map_assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, colimit.ι_post,
      colimit.ι_post_assoc]
    rw [η.naturality_assoc]
    simp only [← E'.map_comp, colimit.ι_map]
  have hη := NatTrans.congr_app _hη (colimit N)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hη
  dsimp only [constructibleGlobalHomColimitComparison]
  rw [← Category.assoc, ← _root_.DerivedCategory.Q.map_comp, hpost]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e'.hom.naturality (colim.map α)
  change _root_.DerivedCategory.Q.map (E'.map (colim.map α)) ≫
      e'.hom.app (colimit N') = e'.hom.app (colimit N) ≫
        ((ExternalRHom.globalHom A X).obj (op K')).map
          (_root_.DerivedCategory.Q.map (colim.map α)) at hn
  rw [hn, ← Category.assoc (_root_.DerivedCategory.Q.map (η.app (colimit N))), hη]
  simp only [Category.assoc]

/-- Compatible quasi-isomorphic representatives give isomorphic exact filtered colimits,
both for the target and for its functorial global-Hom representatives. Together with the
naturality square this identifies the comparison arrows, hence also along any zigzag.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-constructible-bounded-below-hom-colimit).
Proof: filtered colimits of sheaves and coefficient modules are exact. By
src-weil-homology-preserves-exact-colimits they preserve objectwise quasi-isomorphisms.
The natural identification e makes E invert quasi-isomorphisms, and η is objectwise a
quasi-isomorphism by assumption. Two-out-of-three applies to their composites.
Localization sends the resulting colimit quasi-isomorphisms to isomorphisms.
The preceding naturality square, with the identity source map, identifies the comparisons.
This proves representative independence in DAG steps 1 and 5. -/
theorem constructibleGlobalHomColimitComparison_representative_independence
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K : DerivedCategoryModule A X)
    (E E' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K))
    (η : E ⟶ E')
    (_hη : ∀ M : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      QuasiIso (η.app M))
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N N' : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (α : N ⟶ N') (_hα : ∀ j : J, QuasiIso (α.app j)) :
    IsIso (_root_.DerivedCategory.Q.map (colim.map α)) ∧
      IsIso (_root_.DerivedCategory.Q.map
        (colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E'))) := by
  have hE (M M' : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (g : M ⟶ M') (hg : QuasiIso g) : QuasiIso (E.map g) := by
    have : IsIso (_root_.DerivedCategory.Q.map g) :=
      (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
    have hn := e.hom.naturality g
    dsimp only [Functor.comp_map] at hn
    have : IsIso (_root_.DerivedCategory.Q.map (E.map g) ≫ e.hom.app M') := by
      rw [hn]
      infer_instance
    apply (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    exact IsIso.of_isIso_comp_right _ (e.hom.app M')
  have hE' (M M' : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (g : M ⟶ M') (hg : QuasiIso g) : QuasiIso (E'.map g) := by
    have : QuasiIso (E.map g) := hE M M' g hg
    have : QuasiIso (η.app M) := _hη M
    have : QuasiIso (η.app M') := _hη M'
    have : QuasiIso (η.app M ≫ E'.map g) := by
      rw [← η.naturality g]
      infer_instance
    exact quasiIso_of_comp_left (η.app M) (E'.map g)
  have hα : QuasiIso (colim.map α) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).colimMap α _hα
  have hβ : QuasiIso
      (colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E')) := by
    apply (HomologicalComplex.quasiIso _ (.up ℤ)).colimMap
    intro j
    have : QuasiIso (η.app (N.obj j)) := _hη _
    have : QuasiIso (E'.map (α.app j)) := hE' _ _ _ (_hα j)
    exact inferInstanceAs (QuasiIso (η.app (N.obj j) ≫ E'.map (α.app j)))
  exact ⟨(_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hα,
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hβ⟩

end AlgebraicGeometry.Etale
