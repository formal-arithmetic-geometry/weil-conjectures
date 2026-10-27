/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.ConstructibleAlgClTopologyComparison
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.KFlatScalarComparisonNormalization
import all Sheaf.Paper.NormalizedScalarRestrictionPush
import Sheaf.Paper.InternalScalarPullbackNormalization
import Sheaf.Paper.ConstantModelTorAmplitude
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.PullbackFiniteConstantLocalModel
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Hom action of the normalized topology-change counit mate

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
returned coefficient-change input, Hom-adjunction calculation
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection).

All Hom types are in the ordinary ambient derived categories. Only the three
source objects M, L and Rf_*L are required to be bounded constructible.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Profinite.padicAlgClCondensedRing Profinite.continuousMapRingSheaf
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStarComp
set_option allowUnsafeReducibility true
attribute [local reducible] AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.QuotientChange.D
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The restriction/action identification, transported from exact termwise pullback
to the specified total left derived pullback. Source: direct-image stability (3),
scalar comparison (blueprint: lem-sfb-algcl-topology-mate-hom-bijection). -/
def algClTopologyDerivedAction (ℓ : ℕ) [Fact ℓ.Prime]
    {Z T : Scheme.{u}} (f : Z ⟶ T) :=
  Functor.isoWhiskerLeft
      (Mod.comap (coefficientMap (algClTopologyInclusion ℓ) T)).mapDerivedCategory
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ℓ) f) ≪≫
    (CondensedRing.derivedComapUpperStarIso (algClTopologyInclusion ℓ) f).symm ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).symm
      (Mod.comap (coefficientMap (algClTopologyInclusion ℓ) Z)).mapDerivedCategory

/-- The inverse scalar-adjunction mate of the canonical action identification.
Source: direct-image stability (3), theta
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection). -/
def algClTopologyPullbackTheta (ℓ : ℕ) [Fact ℓ.Prime]
    {Z T : Scheme.{u}} (f : Z ⟶ T) :=
  SheafOfModules.ScalarPullback.mate
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (algClTopologyInclusion ℓ) T))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (algClTopologyInclusion ℓ) Z))
    (algClTopologyDerivedAction ℓ f).hom

set_option maxHeartbeats 800000 in
-- The normalization theorem transports four module-category interfaces.
private theorem scalarPullback_mate_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (SheafOfModules.ScalarPullback.mate
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (Functor.isoWhiskerLeft (Mod.comap (coefficientMap a Y)).mapDerivedCategory
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f) ≪≫
        (CondensedRing.derivedComapUpperStarIso a f).symm ≪≫
        Functor.isoWhiskerRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm
          (Mod.comap (coefficientMap a X)).mapDerivedCategory).hom) := by
  let (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj R] [IsCommMonObj R] (S : Scheme.{u}) :
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R S) :=
    @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
      (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
        (Scheme.ProEt.topology S) _)
  obtain ⟨_, _, b, _, _, _, _, hb, _⟩ :=
    QuotientChange.internal_scalar_pullback_normalization a f
  have h := QuotientChange.normalized_inverse a f b hb
  have hi : IsIso b.inv := inferInstance
  rw [h] at hi
  have he : (QuotientChange.scalarRestrictionPull a f).inv =
      (Functor.isoWhiskerLeft (Mod.comap (coefficientMap a Y)).mapDerivedCategory
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f) ≪≫
        (CondensedRing.derivedComapUpperStarIso a f).symm ≪≫
        Functor.isoWhiskerRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm
          (Mod.comap (coefficientMap a X)).mapDerivedCategory).hom := by
    ext M
    simp only [QuotientChange.scalarRestrictionPull, QuotientChange.V,
      QuotientChange.V₀, id_eq, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
      Iso.symm_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Category.assoc]
  rw [he] at hi
  exact hi

/-- This specified mate is invertible, without coefficient flatness. Its inverse
is the pullback/tensor comparison normalized on flat-term K-flat representatives.
Source: direct-image stability (3), normalized scalar comparison
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection).

Proof: apply the recorded module/ringed-topos comparison to the coefficient rings
and their inclusion. The coefficient pullback isomorphisms identify the transported
ring sheaves with the inverse-image rings. The action identification above becomes
`aD_h`: both are localization of the identical underlying section action, transported
along the exact-pullback/left-derived comparison. Apply
`kflat_scalar_comparison_normalization` to these actual K-flat models. Its last
clause makes theta invertible, and its representative equation identifies its inverse
with the balanced coequalizer comparison preserving insertion of the scalar unit.
Transport back along the module equivalences; these preserve adjunctions and mates. -/
theorem algClTopologyPullbackTheta_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    {Z T : Scheme.{u}} (f : Z ⟶ T) :
    IsIso (algClTopologyPullbackTheta ℓ f) := by
  exact scalarPullback_mate_isIso (algClTopologyInclusion ℓ) f

/-- The canonical sigma, the inverse of the specified scalar-adjunction mate.
Source: direct-image stability (3), sigma
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection). -/
def algClTopologyPullbackSigma (ℓ : ℕ) [Fact ℓ.Prime]
    {Z T : Scheme.{u}} (f : Z ⟶ T) :=
  @asIso _ _ _ _ (algClTopologyPullbackTheta ℓ f)
    (algClTopologyPullbackTheta_isIso ℓ f) |>.symm


/-- The specified chi is the B-geometric adjunct of sigma followed by scalar
extension of the C-geometric counit. No properness or constructibility is needed
for the definition. Source: direct-image stability proof (3), displayed chi
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection). -/
def algClTopologyCounitMate (ℓ : ℕ) [Fact ℓ.Prime]
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f).homEquiv _ _
      ((algClTopologyPullbackSigma ℓ f).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward
            (Profinite.padicAlgClRingObj ℓ) f).obj L) ≫
        (algClTopologyScalarExtension ℓ Z).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) f).counit.app L))

private theorem constantModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ g).obj M) := by
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
  let e := ((CondensedRing.upperStarComp Λ (T.immersion i) g).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) comm.symm) ≪≫
    (CondensedRing.upperStarComp Λ q (S.immersion i)).app M
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun j ↦ by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f j)).mapIso e ≪≫ eP⟩⟩⟩

private theorem bounded_constantModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ N, IsConstantModelConstructible Λ Y N →
      IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ f).obj N))
    (M : ConstantModelBoundedConstructible Λ Y) :
    constantModelBoundedConstructible Λ X
      ((CondensedRing.moduleObjectDerivedPullback Λ f).obj M.obj) := by
  let F := CondensedRing.upperStar Λ f
  let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.symm.app M.obj)
      (F.bounded_mapDerivedCategory_obj M.property.1)
  · exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((F.mapDerivedCategoryHomologyFunctorIso n).app M.obj ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso (e.symm.app M.obj))
      (h _ (M.property.2 n))

private theorem restricted_map_bijective
    {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty A) (Q : ObjectProperty B) (J : A ⥤ B)
    (h : ∀ M : P.FullSubcategory, Q (J.obj M.obj))
    (he : (Q.lift (P.ι ⋙ J) h).IsEquivalence) (M N : P.FullSubcategory) :
    Function.Bijective (J.map : (M.obj ⟶ N.obj) → _) := by
  let G := Q.lift (P.ι ⋙ J) h
  let : G.IsEquivalence := he
  exact (P.fullyFaithfulι.homEquiv.symm.trans
    (Functor.FullyFaithful.ofFullyFaithful (G ⋙ Q.ι)).homEquiv).bijective

private theorem counitMate_hom
    {A X B Y : Type*} [Category A] [Category X] [Category B] [Category Y]
    {F : A ⥤ X} {G : X ⥤ A} {F' : B ⥤ Y} {G' : Y ⥤ B}
    (a : F ⊣ G) (b : F' ⊣ G') (J : A ⥤ B) (K : X ⥤ Y)
    (s : J ⋙ F' ≅ F ⋙ K) (M : A) (L : X) (u : M ⟶ G.obj L) :
    b.homEquiv _ _ (s.hom.app M ≫ K.map ((a.homEquiv _ _).symm u)) =
      J.map u ≫ b.homEquiv _ _
        (s.hom.app (G.obj L) ≫ K.map (a.counit.app L)) := by
  rw [Adjunction.homEquiv_counit, K.map_comp, ← Category.assoc]
  have hn := s.hom.naturality u
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]
  exact b.homEquiv_naturality_left (J.map u)
    (s.hom.app (G.obj L) ≫ K.map (a.counit.app L))

private theorem counitMate_bijective
    {A X B Y : Type*} [Category A] [Category X] [Category B] [Category Y]
    {F : A ⥤ X} {G : X ⥤ A} {F' : B ⥤ Y} {G' : Y ⥤ B}
    (a : F ⊣ G) (b : F' ⊣ G') (J : A ⥤ B) (K : X ⥤ Y)
    (s : J ⋙ F' ≅ F ⋙ K) (M : A) (L : X)
    (hT : Function.Bijective (J.map : (M ⟶ G.obj L) → _))
    (hZ : Function.Bijective (K.map : (F.obj M ⟶ L) → _)) :
    ∃ (eT : (M ⟶ G.obj L) ≃ (J.obj M ⟶ J.obj (G.obj L)))
      (eZ : (F.obj M ⟶ L) ≃ (K.obj (F.obj M) ⟶ K.obj L)),
      (∀ u, eT u = J.map u) ∧ (∀ v, eZ v = K.map v) ∧
      Function.Bijective (fun v : J.obj M ⟶ J.obj (G.obj L) ↦
        v ≫ b.homEquiv _ _ (s.hom.app (G.obj L) ≫ K.map (a.counit.app L))) ∧
      (∀ v, v ≫ b.homEquiv _ _ (s.hom.app (G.obj L) ≫ K.map (a.counit.app L)) =
        b.homEquiv _ _ (s.hom.app M ≫ eZ ((a.homEquiv _ _).symm (eT.symm v)))) ∧
      (∀ u : M ⟶ G.obj L,
        b.homEquiv _ _ (s.hom.app M ≫ K.map ((a.homEquiv _ _).symm u)) =
          J.map u ≫ b.homEquiv _ _
            (s.hom.app (G.obj L) ≫ K.map (a.counit.app L))) := by
  classical
  let eT := Equiv.ofBijective J.map hT
  let eZ := Equiv.ofBijective K.map hZ
  have formula (v : J.obj M ⟶ J.obj (G.obj L)) :
      v ≫ b.homEquiv _ _ (s.hom.app (G.obj L) ≫ K.map (a.counit.app L)) =
        b.homEquiv _ _ (s.hom.app M ≫ eZ ((a.homEquiv _ _).symm (eT.symm v))) := by
    calc
      _ = J.map (eT.symm v) ≫ b.homEquiv _ _
          (s.hom.app (G.obj L) ≫ K.map (a.counit.app L)) :=
        congrArg (fun w ↦ w ≫ b.homEquiv _ _
          (s.hom.app (G.obj L) ≫ K.map (a.counit.app L)))
          (eT.apply_symm_apply v).symm
      _ = _ := (counitMate_hom a b J K s M L (eT.symm v)).symm
  let e := eT.symm.trans ((a.homEquiv _ _).symm.trans
    (eZ.trans (((s.app M).symm.homCongr (Iso.refl _)).trans (b.homEquiv _ _))))
  refine ⟨eT, eZ, (fun _ ↦ rfl), (fun _ ↦ rfl), ?_, formula,
    counitMate_hom a b J K s M L⟩
  have he : (fun v ↦ v ≫
      b.homEquiv _ _ (s.hom.app (G.obj L) ≫ K.map (a.counit.app L))) = e := by
    funext v
    change _ = b.homEquiv _ _
      (s.hom.app M ≫ eZ ((a.homEquiv _ _).symm (eT.symm v)) ≫ 𝟙 _)
    simpa only [Category.comp_id] using formula v
  rw [he]
  exact e.bijective

attribute [local irreducible] algClTopologyPullbackSigma algClTopologyPullbackTheta
  algClTopologyDerivedAction
  CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  CondensedRing.upperStar Mod.extendScalars

set_option maxHeartbeats 800000 in
-- The ambient derived Hom equivalences contain the fixed coefficient comparisons.
/-- Postcomposition by the specified mate is bijective and is exactly the
four-stage Hom bijection. The witnesses eT and eZ have forward maps equal to the
actual scalar-extension maps; their inverses therefore encode the specified
inverse Hom bijections, rather than arbitrary equivalences.

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
returned proper coefficient-change input, Hom-adjunction calculation
(blueprint: lem-sfb-algcl-topology-mate-hom-bijection).

Proof plan:
1. The exact module pullback (det-prop-sfb-module-pullback-exact-main) computes its
left derived functor termwise (lem-weil-pbc-exact-functor-derived-functor and
lem-weil-pbc-exact-functor-bounded-below). Its homology is pullback of homology,
so it is bounded. Pullback of finite constant models is constructible by
lem-sfb-pullback-constant-model-constructible, giving the first conjunct.
2. Apply lem-sfb-constructible-algcl-topology-comparison on T and Z. Full
faithfulness on the full constructible subcategories gives eT and eZ with exactly
the displayed forward maps. The C and B geometric adjunctions give the other
Hom bijections. The normalized sigma is invertible by
lem-sfb-kflat-scalar-comparison-normalization. Thus the four-stage function is bijective.
3. For u:M -> P, the C-adjunction inverse is f_C^*(u) followed by its counit
(lem-weil-pbc-adjunction-of-natural-bijection). Naturality of sigma and functoriality
of J identify sigma_M followed by J(f_C^*(u) followed by epsilon) with
f_B^*(J(u)) followed by sigma_P and J(epsilon).
4. The B-geometric homEquiv transpose-square identity
(lem-sfb-adjunction-transpose-square) identifies its adjunct with J(u) followed
by chi. Every arrow in the first B-Hom set is uniquely J(u), by step 2. Hence
postcomposition by chi equals the four-stage bijection on every arrow and is
bijective. This proves the last formula too, with no assumption on Q and no
properness or coefficient-flatness assumption. -/
theorem algClTopologyMate_hom_bijection
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (Z T : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (f : Z ⟶ T)
    (L : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Z.left)
    (hP : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T.left
      ((CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj))
    (M : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) T.left) :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Z.left
      ((CondensedRing.moduleObjectDerivedPullback
        (Profinite.padicAlgClRingObj ℓ) f.left).obj M.obj) ∧
    ∃ (eT : (M.obj ⟶ (CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj) ≃
        ((algClTopologyScalarExtension ℓ T.left).obj M.obj ⟶
          (algClTopologyScalarExtension ℓ T.left).obj
            ((CondensedRing.moduleObjectDerivedPushforward
              (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj)))
      (eZ : ((CondensedRing.moduleObjectDerivedPullback
          (Profinite.padicAlgClRingObj ℓ) f.left).obj M.obj ⟶ L.obj) ≃
        ((algClTopologyScalarExtension ℓ Z.left).obj
            ((CondensedRing.moduleObjectDerivedPullback
              (Profinite.padicAlgClRingObj ℓ) f.left).obj M.obj) ⟶
          (algClTopologyScalarExtension ℓ Z.left).obj L.obj)),
      (∀ u, eT u = (algClTopologyScalarExtension ℓ T.left).map u) ∧
      (∀ v, eZ v = (algClTopologyScalarExtension ℓ Z.left).map v) ∧
      Function.Bijective (fun v :
        (algClTopologyScalarExtension ℓ T.left).obj M.obj ⟶
          (algClTopologyScalarExtension ℓ T.left).obj
            ((CondensedRing.moduleObjectDerivedPushforward
              (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj) ↦
        v ≫ algClTopologyCounitMate ℓ f.left L.obj) ∧
      (∀ v, v ≫ algClTopologyCounitMate ℓ f.left L.obj =
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f.left).homEquiv _ _
            ((algClTopologyPullbackSigma ℓ f.left).hom.app M.obj ≫
              eZ ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (Profinite.padicAlgClRingObj ℓ) f.left).homEquiv _ _ |>.symm
                  (eT.symm v)))) ∧
      (∀ u : M.obj ⟶ (CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj,
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f.left).homEquiv _ _
            ((algClTopologyPullbackSigma ℓ f.left).hom.app M.obj ≫
              (algClTopologyScalarExtension ℓ Z.left).map
                ((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (Profinite.padicAlgClRingObj ℓ) f.left).homEquiv _ _ |>.symm u)) =
          (algClTopologyScalarExtension ℓ T.left).map u ≫
            algClTopologyCounitMate ℓ f.left L.obj) := by
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  suffices hFM : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Z.left
      ((CondensedRing.moduleObjectDerivedPullback
        (Profinite.padicAlgClRingObj ℓ) f.left).obj M.obj) by
    have hom_bijective (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
        [QuasiCompact X.hom] [IsSeparated X.hom]
        (A D : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left) :
        Function.Bijective ((algClTopologyScalarExtension ℓ X.left).map :
          (A.obj ⟶ D.obj) → _) := by
      obtain ⟨_, _, h, he, _⟩ :=
        constructible_algCl_topology_comparison ℓ p k hp hpℓ X
      exact restricted_map_bijective
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X.left)
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X.left)
        (algClTopologyScalarExtension ℓ X.left) h he A D
    refine ⟨hFM, ?_⟩
    have hCat := counitMate_bijective
      (F := CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ) f.left)
      (G := CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) f.left)
      (F' := CondensedRing.moduleObjectDerivedPullback
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f.left)
      (G' := CondensedRing.moduleObjectDerivedPushforward
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f.left)
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
      (CondensedRing.derivedUpperStarLowerStarAdjunction
        (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) f.left)
      (algClTopologyScalarExtension ℓ T.left) (algClTopologyScalarExtension ℓ Z.left)
      (algClTopologyPullbackSigma ℓ f.left) M.obj L.obj
      (hom_bijective T M
        ⟨(CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) f.left).obj L.obj, hP⟩)
      (hom_bijective Z
        ⟨(CondensedRing.moduleObjectDerivedPullback
          (Profinite.padicAlgClRingObj ℓ) f.left).obj M.obj, hFM⟩ L)
    exact hCat
  exact bounded_constantModel_pullback (Profinite.padicAlgClRingObj ℓ) f.left
    (fun N hN ↦ constantModel_pullback (Profinite.padicAlgClRingObj ℓ) f.left N hN) M

end AlgebraicGeometry.ProEtale
