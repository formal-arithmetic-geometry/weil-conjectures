/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T9
-/
module

public import Sheaf.CategoryTheory.DerivedMorphismPresheaf
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Module.Projective
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Tor descent from finite projective scalar charts

Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tag 06YS.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
namespace AlgebraicGeometry.Scheme

private theorem cover_zero (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (m : ℕ) (U : Fin m → X.ProEt)
    (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 X))
    (hf : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (hz : ∀ c, IsZero ((ProEtale.upperStar (ModuleCat.{u + 1} B) (U c).hom).obj F)) :
    IsZero F := by
  have hw (c : Fin m) : (f c).left = (U c).hom := by
    have h := MorphismProperty.Over.w (f c)
    change (f c).left ≫ 𝟙 X = (U c).hom at h ⊢
    exact (Category.comp_id _).symm.trans h
  have hcover : Presieve.ofArrows (fun c ↦ (U c).left) (fun c ↦ (U c).hom) ∈
      proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun c ↦ (U c).left) (fun c ↦ (f c).left) ∈
      proetalePrecoverage X at hf
    simpa only [hw] using hf
  have (c : Fin m) : WeaklyEtale (U c).hom := (U c).prop
  have h : IsIso (0 : F ⟶ 0) := by
    apply ProEtale.isIso_of_isIso_localizationRestriction
      (ModuleCat.{u + 1} B) _ (fun c ↦ (U c).hom) hcover
    intro c
    let G := ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U c).hom (U c).prop
    have hG : IsZero (G.obj F) := (hz c).of_iso
      ((ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} B) (U c).hom (U c).prop).app F).symm
    exact isIso_of_source_target_iso_zero _ hG.isoZero
      (((ProEtale.upperStar (ModuleCat.{u + 1} B) (U c).hom).map_isZero
        (isZero_zero _)).of_iso ((ProEtale.upperStarIsoLocalizationRestriction
          (ModuleCat.{u + 1} B) (U c).hom (U c).prop).app 0).symm).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private theorem tor_of_pullbacks (X : Scheme.{u}) (B : Type (u + 1))
    [CommRing B] [Finite B]
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
    (a b : ℤ) {I : Type*} (Y : I → Scheme.{u}) (g : ∀ i, Y i ⟶ X)
    (hzero : ∀ F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B),
      (∀ i, IsZero ((ProEtale.upperStar (ModuleCat.{u + 1} B) (g i)).obj F)) → IsZero F)
    (ht : ∀ i, ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) (Y i) a b
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) (g i)).mapDerivedCategory.obj K)) :
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X a b K := by
  intro N
  let L := K ⊗ (DerivedCategory.singleFunctor _ 0).obj N
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L) := by
    apply hzero
    intro i
    let G := ProEtale.upperStar (ModuleCat.{u + 1} B) (g i)
    let e := ProEtale.mapDerivedCategoryUpperStarTensorSingleIso
      (ModuleCat.{u + 1} B) (g i) K N
    have hc := (DerivedCategory.homologyConcentratedIn a b).prop_of_iso e.symm
      (ht i (G.obj N))
    have hh : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (G.mapDerivedCategory.obj L)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ a).1 hc.1 q hq
      · exact (DerivedCategory.isLE_iff _ b).1 hc.2 q hq
    exact hh.of_iso ((G.mapDerivedCategoryHomologyFunctorIso q).app L)
  exact ⟨(DerivedCategory.isGE_iff L a).2 (fun q hq ↦ hz q (.inl hq)),
    (DerivedCategory.isLE_iff L b).2 (fun q hq ↦ hz q (.inr hq))⟩

private theorem slice_model_tor (X : Scheme.{u}) (B : Type (u + 1))
    [CommRing B] [Finite B] (U : X.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
    (P : CochainComplex (ModuleCat.{u + 1} B) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hp : ∀ q : ℤ, Module.Projective B (P.X q))
    (e : Nonempty ((@derivedSliceRestriction.{u} X.ProEt _
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology X) B _ U).obj K ≅
      DerivedCategory.Q.obj (((constantSheaf ((ProEt.topology X).over U)
        (ModuleCat.{u + 1} B)).mapHomologicalComplex (.up ℤ)).obj P))) :
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) U.left a b
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K) := by
  classical
  have := ProEt.sliceDense X U
  let E := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let F := ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom
  let G := (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) U
  let c := constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  have hcflat (q : ℤ) : ObjectProperty.flat (c.obj (P.X q)) := by
    have := hp q
    exact GrothendieckTopology.flat_presheafToSheaf_obj (ModuleCat.{u + 1} B)
      (ProEt.topology U.left) _ (fun _ ↦
        (ModuleCat.flat_iff_flat _).2
          (Module.Flat.of_projective (R := B) (M := P.X q)))
  have ht : DerivedCategory.torAmplitudeIn _ a b
      (DerivedCategory.Q.obj ((c.mapHomologicalComplex (.up ℤ)).obj P)) := by
    let := ha
    let := hb
    exact DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b hcflat
  let er : G ⋙ E.functor ≅
      ProEtale.localizationRestriction (ModuleCat.{u + 1} B) U.hom U.prop :=
    NatIso.ofComponents (fun M ↦
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))) (by
        intro M N f
        ext V
        rfl)
  let ec : G ⋙ E.functor ≅ F := er ≪≫
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) U.hom U.prop).symm
  let econst := (ProEt.sliceEquiv X U).constantSheafSheafCongrIso
    ((ProEt.topology X).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} B)
      (Over.mkIdTerminal (X := U))
  let emap : E.functor.mapDerivedCategory.obj (G.mapDerivedCategory.obj K) ≅
      DerivedCategory.Q.obj ((c.mapHomologicalComplex (.up ℤ)).obj P) :=
    E.functor.mapDerivedCategory.mapIso e.some ≪≫
      E.functor.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso econst (.up ℤ)).app P)
  let ef : E.functor.mapDerivedCategory.obj (G.mapDerivedCategory.obj K) ≅
      F.mapDerivedCategory.obj K :=
    (Functor.mapDerivedCategoryCompIso G E.functor).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso ec).app K
  exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso ef
    ((DerivedCategory.torAmplitudeIn _ a b).prop_of_iso emap.symm ht)

/-- A fixed term interval for projective scalar models bounds every module tensor test.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tag 06YS
(blueprint: lem-pur-stratified-finite-projective-tor).

Proof: projective scalar terms are flat. Their constant sheaves on each slice are
flat, and the bounded complex of these constant sheaves is K-flat. Tensoring it with
any degree-zero module sheaf is therefore the ordinary termwise tensor complex.
The zero terms outside [a,b] remain zero, proving the Tor bound on each chart.
Take a flat K-flat resolution of the global object. Exact stratum inverse image
and slice restriction commute with homology, preserve flatness, and commute with
tensor. The chart isomorphisms consequently make the restriction of every global
tensor test vanish outside [a,b]. Cover detection gives the same bound on each
stratum. Noetherian finite-stratum detection applied to the cohomology sheaves of
the global tensor test gives the global bound. The interval is fixed throughout;
no cohomological bound is used as a substitute for a Tor bound. Empty covers and
empty schemes are covered by the same zero-detection statements. -/
theorem stratified_finite_projective_tor
    (T : Scheme.{u}) [IsNoetherian T]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} B)))
    (a b : ℤ) (S : Stratification T)
    (hmodels : ∀ r : Fin S.n,
      ∃ (m : ℕ) (U : Fin m → (S.domain r).ProEt)
        (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 (S.domain r)))
        (P : Fin m → CochainComplex (ModuleCat.{u + 1} B) ℤ),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain r)).coverings _ ∧
        ∀ c : Fin m,
          ((P c).IsStrictlyGE a ∧ (P c).IsStrictlyLE b) ∧
          (∀ q : ℤ, Module.Projective B ((P c).X q)) ∧
          Nonempty
            ((@CategoryTheory.derivedSliceRestriction.{u} (S.domain r).ProEt _
              (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology (S.domain r)) B _
                (U c)).obj
                  (((ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion r))
                    |>.mapDerivedCategory).obj K) ≅
              (DerivedCategory.Q (C := Sheaf ((ProEt.topology (S.domain r)).over (U c))
                (ModuleCat.{u + 1} B))).obj
                  (((constantSheaf ((ProEt.topology (S.domain r)).over (U c))
                    (ModuleCat.{u + 1} B)).mapHomologicalComplex (.up ℤ)).obj (P c)))) :
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) T a b K ∧
      ∀ r : Fin S.n,
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) (S.domain r) a b
          (((ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion r))
            |>.mapDerivedCategory).obj K) := by
  classical
  have hstr (r : Fin S.n) :
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) (S.domain r) a b
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion r)).mapDerivedCategory.obj K) := by
    obtain ⟨m, U, f, P, hf, hP⟩ := hmodels r
    apply tor_of_pullbacks (S.domain r) B _ a b
      (fun c : Fin m ↦ (U c).left) (fun c ↦ (U c).hom)
      (fun F h ↦ cover_zero _ B m U f hf F h)
    intro c
    exact slice_model_tor _ B (U c) _ (P c) a b
      (hP c).1.1 (hP c).1.2 (hP c).2.1 (hP c).2.2
  have : ∀ r : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain r) :=
    fun r ↦ (S.immersion r).isEmbedding.noetherianSpace
  have : ∀ r : Fin S.n, QuasiCompact (S.immersion r) := fun r ↦ inferInstance
  refine ⟨?_, hstr⟩
  apply tor_of_pullbacks T B K a b S.domain S.immersion ?_ hstr
  intro F hF
  apply (IsZero.iff_id_eq_zero F).2
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero B S.immersion
  · intro x
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨r, (S.range_immersion r).symm ▸ hr⟩
  · intro r
    rw [CategoryTheory.Functor.map_id]
    exact (hF r).eq_of_src _ _

end AlgebraicGeometry.Scheme
