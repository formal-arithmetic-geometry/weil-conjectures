/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups A2, A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.AlgebraicGeometry.EllAdicAffineCompactSupportRepresentable

/-! # Constructibility of the cohomology of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem localizing_map_of_leftAdjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X Y : Scheme.{u})
    (F : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsLeftAdjoint]
    (hF : ∀ K, boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ Y) (F.obj K)) :
    boundedConstructibleLocalizingClosure Λ X ≤
      (boundedConstructibleLocalizingClosure Λ Y).inverseImage F := by
  apply boundedConstructibleLocalizingClosure_map_of_preservesOnClosure Λ X Y F
  · intro I
    let : HasColimitsOfSize.{u + 1, u + 1} (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
      IsGrothendieckAbelian.hasColimits _
    let : HasCoproducts.{u + 1} (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
      fun J ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)
    let : HasCoproducts.{u + 1} (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
      CategoryTheory.derived_hasCoproducts
    have : PreservesColimitsOfShape (Discrete I)
        (boundedConstructibleLocalizingClosure Λ X).ι := inferInstance
    have : PreservesColimitsOfShape (Discrete I) F := inferInstance
    exact comp_preservesColimitsOfShape _ _
  · exact hF

private theorem localizing_openLowerShriek_obj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    boundedConstructibleLocalizingClosure Λ U.left ≤
      (boundedConstructibleLocalizingClosure Λ X.left).inverseImage
        D((j.left)_!open⟦Λ⟧) := by
  exact localizing_map_of_leftAdjoint Λ U.left X.left D((j.left)_!open⟦Λ⟧)
    (boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j)

private theorem localizing_upperStar_obj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) :
    boundedConstructibleLocalizingClosure Λ X.left ≤
      (boundedConstructibleLocalizingClosure Λ U.left).inverseImage D((j.left)^*⟦Λ⟧) := by
  have : D((j.left)^*⟦Λ⟧).IsLeftAdjoint :=
    ((derivedUpperStarLowerStarAdjunction Λ j.left).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ j.left)).isLeftAdjoint
  apply localizing_map_of_leftAdjoint Λ X.left U.left D((j.left)^*⟦Λ⟧)
  intro K hK
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ j.left).app K
  have h := boundedConstructible_leftDerivedUpperStar_obj Λ ℓ j K hK
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e h.1,
    fun n ↦ constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩

private theorem isIso_of_postcomp_on_property
    {C : Type*} [Category C] (P : ObjectProperty C) {L B : C}
    (hL : P L) (hB : P B) (t : L ⟶ B)
    (h : ∀ M, P M → Function.Bijective (fun a : M ⟶ L ↦ a ≫ t)) : IsIso t := by
  obtain ⟨s, hs⟩ := (h B hB).2 (𝟙 B)
  have ht : t ≫ s = 𝟙 L := (h L hL).1 (by simp [Category.assoc, hs])
  exact ⟨⟨s, ht, hs⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_generator_postcomp
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsStableUnderShift ℤ] {L B : C}
    (hL : P.rightOrthogonal.leftOrthogonal L)
    (hB : P.rightOrthogonal.leftOrthogonal B) (t : L ⟶ B)
    (h : ∀ M, P M → Function.Bijective (fun a : M ⟶ L ↦ a ≫ t)) : IsIso t := by
  classical
  obtain ⟨Q, s, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle t
  have hQ : P.rightOrthogonal Q := by
    intro M f hM
    have hinj : Function.Injective (fun a : M ⟶ L⟦(1 : ℤ)⟧ ↦ a ≫ t⟦(1 : ℤ)⟧') := by
      let a := (shiftEquiv C (1 : ℤ)).symm.toAdjunction
      intro x y hxy
      obtain ⟨x, rfl⟩ := (a.homEquiv M L).surjective x
      obtain ⟨y, rfl⟩ := (a.homEquiv M L).surjective y
      apply congrArg (a.homEquiv M L)
      apply (h _ (P.le_shift (-1) M hM)).1
      apply (a.homEquiv M B).injective
      rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right]
      exact hxy
    have hf : f ≫ δ = 0 := hinj (by
      simpa only [Pretriangulated.Triangle.mk, Category.assoc, zero_comp, comp_zero] using
        congrArg (f ≫ ·) (Pretriangulated.comp_distTriang_mor_zero₃₁ _ hT))
    obtain ⟨a, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hT f hf
    obtain ⟨b, rfl⟩ := (h M hM).2 a
    have hz := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
    dsimp only [Pretriangulated.Triangle.mk] at hz ⊢
    rw [Category.assoc, hz, comp_zero]
  have ht : P.rightOrthogonal.trW t := ⟨Q, s, δ, hT, hQ⟩
  apply isIso_of_postcomp_on_property P.rightOrthogonal.leftOrthogonal hL hB t
  intro M hM
  have hM' : P.rightOrthogonal.trW.isColocal M := by
    rwa [ObjectProperty.isColocal_trW]
  exact hM' t ht

private theorem boundedConstructible_stableUnderShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (boundedConstructible (condensedRingObj Λ X)).IsStableUnderShift ℤ := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ X)) :=
    ⟨fun e h ↦ constructible_of_iso e h⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty
      (IsConstructibleModuleObject (condensedRingObj Λ X))).IsStableUnderShift ℤ
  infer_instance

private theorem localizing_le_doubleOrthogonal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    boundedConstructibleLocalizingClosure Λ X ≤
      (boundedConstructible (condensedRingObj Λ X)).rightOrthogonal.leftOrthogonal := by
  let P := boundedConstructible (condensedRingObj Λ X)
  have : P.IsStableUnderShift ℤ := boundedConstructible_stableUnderShift Λ X
  have (I : Type (u + 1)) :
      P.rightOrthogonal.leftOrthogonal.IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    rintro M ⟨c⟩ Y f hY
    apply c.isColimit.hom_ext
    intro i
    rw [comp_zero]
    exact c.prop_diag_obj i (c.ι.app i ≫ f) hY
  apply boundedConstructibleLocalizingClosure_le
  intro M hM Y f hY
  exact hY f hM

private theorem constructible_comap_iff
    {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    IsConstructibleModuleObject S ((Mod.comap φ).obj M) ↔ IsConstructibleModuleObject R M := by
  refine ⟨fun h ↦ ?_, fun h ↦ constructible_comap φ h⟩
  exact constructible_of_iso
    (((Mod.comapComp (inv φ) φ).symm ≪≫
      Mod.comapCongr (IsIso.inv_hom_id φ) ≪≫ Mod.comapId R).app M)
    (constructible_comap (inv φ) h)

private theorem constructible_pullback_comp_iff
    {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    IsConstructibleModuleObject ((ProEtale.upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    IsConstructibleModuleObject
      ((ProEtale.upperStar Ab.{u + 1} f).obj ((ProEtale.upperStar Ab.{u + 1} g).obj R))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj
        (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := ProEtale.upperStar Ab.{u + 1} g
  let G := ProEtale.upperStar Ab.{u + 1} f
  let e := ProEtale.upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ constructible_of_iso i.symm (constructible_comap φ h),
    fun h ↦ (constructible_comap_iff φ _).mp (constructible_of_iso i h)⟩

private theorem raw_constructible_of_finite_openCover (n : ℕ) :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (U : Fin n → X.Opens) (_ : ⨆ a, U a = ⊤)
      (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      (∀ a, IsConstructibleModuleObject
        ((ProEtale.upperStar Ab.{u + 1} (U a).ι).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U a).ι).mapMod R).obj M)) →
      IsConstructibleModuleObject R M := by
  induction n with
  | zero =>
    intro X _ U hU R _ M _
    have : IsEmpty X := by
      refine ⟨fun x ↦ ?_⟩
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at hx
      simp at hx
    apply constructible_of_isZero R M
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Mod.hom_ext
    have hz : IsZero M.X := by
      refine Sheaf.isZero_of_isZero_obj _ ?_
      rintro ⟨T⟩
      have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty X).false (T.hom t)⟩
      exact (isZero_zero _).of_iso
        ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).uniqueUpToIso
          HasZeroObject.zeroIsTerminal)
    exact hz.eq_of_src _ _
  | succ n ih =>
    intro X _ U hU R _ M hM
    obtain ⟨Z, i, _, hi⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i.base = (Set.range (U 0).ι.base)ᶜ :=
      ⟨_, _, inferInstance, (U 0).ι.range_closedComplement⟩
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := {}
    apply constructible_of_restrictions (U 0).ι i hi R M (hM 0)
    refine ih (fun a ↦ i ⁻¹ᵁ U a.succ) ?_
      ((ProEtale.upperStar Ab.{u + 1} i).obj R)
      (((ProEtale.upperStar Ab.{u + 1} i).mapMod R).obj M) (fun a ↦ ?_)
    · refine top_le_iff.1 fun z _ ↦ ?_
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (Set.mem_univ (i z)))
      have hz : i z ∉ Set.range (U 0).ι := by
        rw [← Set.mem_compl_iff, ← hi]
        exact ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero (n := n) (i := m) (by
        rintro rfl
        exact hz (by simpa using hm))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hm⟩
    · have h := constructible_pullback (i ∣_ U a.succ) (hM a.succ)
      have h' := (constructible_pullback_comp_iff (i ∣_ U a.succ) (U a.succ).ι R M).mpr h
      rw [morphismRestrict_ι] at h'
      exact (constructible_pullback_comp_iff (i ⁻¹ᵁ U a.succ).ι i R M).mp h'

private theorem constructible_of_finite_openCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsNoetherian X]
    (n : ℕ) (U : Fin n → X.Opens) (hU : ⨆ a, U a = ⊤)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ a, IsConstructibleModuleObject (condensedRingObj Λ (U a).toScheme)
      (((U a).ι)^*⟦Λ⟧.obj M)) : IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  apply raw_constructible_of_finite_openCover n U hU (condensedRingObj Λ X) M
  intro a
  let φ := condensedPullbackHom Λ (U a).ι
  let A := ((ProEtale.upperStar Ab.{u + 1} (U a).ι).mapMod _).obj M
  have h := constructible_comap φ
    (constructible_of_iso ((Mod.extendScalarsIsoComapInv φ).app A) (hM a))
  exact constructible_of_iso
    (((Mod.comapComp φ (inv φ)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId _).app A) h

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- On an affine open of the source, the supplied right adjoint is bounded constructible.

Source: blueprint `sk-thm-restriction/sk-thm-restriction-local.proof.md`, factorization.
Proof: the open adjunction and the supplied proper adjunction give the compact-support
Hom equivalence on the localizing hull. Transpose the affine representative's counit.
Naturality identifies postcomposition with that map on the bounded constructible
generators. The cone is right orthogonal to these generators, whereas both its source
and target belong to their double orthogonal. The resulting map is an isomorphism.
(blueprint: lem-sfb-adic-affine-restriction-bounded-constructible) -/
theorem affine_restriction_boundedConstructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory)
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [IsAffine U.left] (j : U ⟶ Z) [IsOpenImmersion j.left] :
    boundedConstructible (condensedRingObj Λ U.left)
      (D((j.left)^*⟦Λ⟧).obj
        (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj) := by
  let c : Compactification (j ≫ g).left :=
    { Z := Z.left
      i := j.left
      g := g.left
      comm := rfl
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  obtain ⟨L, ε, hε⟩ := affine_compactSupport_representable Λ ℓ hΛ (j ≫ g) c K
  let A := G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)
  let B := D((j.left)^*⟦Λ⟧).obj A.obj
  have hB : boundedConstructibleLocalizingClosure Λ U.left B :=
    localizing_upperStar_obj Λ ℓ j A.obj A.property
  let J (M : (boundedConstructibleLocalizingClosure Λ U.left).FullSubcategory) :
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory :=
    ⟨D((j.left)_!open⟦Λ⟧).obj M.obj,
      localizing_openLowerShriek_obj Λ ℓ j M.obj M.property⟩
  let E (M : (boundedConstructibleLocalizingClosure Λ U.left).FullSubcategory) :
      ((rightDerivedLowerShriekOfCompactification Λ c).obj M.obj ⟶ K.obj) ≃
        (M.obj ⟶ B) :=
    (ObjectProperty.fullyFaithfulι (boundedConstructibleLocalizingClosure Λ Y.left)).homEquiv.symm
      |>.trans (adj.homEquiv (J M) ((boundedConstructibleToLocalizing Λ Y.left).obj K))
      |>.trans
        (ObjectProperty.fullyFaithfulι (boundedConstructibleLocalizingClosure Λ Z.left)).homEquiv
      |>.trans ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).homEquiv M.obj A.obj)
  let L' : (boundedConstructibleLocalizingClosure Λ U.left).FullSubcategory :=
    (boundedConstructibleToLocalizing Λ U.left).obj L
  let t : L.obj ⟶ B := E L' ε
  have ht (M : (boundedConstructibleLocalizingClosure Λ U.left).FullSubcategory)
      (a : M.obj ⟶ L.obj) :
      E M ((rightDerivedLowerShriekOfCompactification Λ c).map a ≫ ε) = a ≫ t := by
    change (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).homEquiv M.obj A.obj
      (adj.homEquiv (J M) ((boundedConstructibleToLocalizing Λ Y.left).obj K)
        (ObjectProperty.homMk
          ((rightDerivedLowerShriekOfCompactification Λ c).map a ≫ ε))).hom = _
    have hnat := adj.homEquiv_naturality_left
      (ObjectProperty.homMk (D((j.left)_!open⟦Λ⟧).map a) : J M ⟶ J L')
      (ObjectProperty.homMk ε :
        (ellAdicLocalizingLowerStar Λ ℓ g hΛ).obj (J L') ⟶
          (boundedConstructibleToLocalizing Λ Y.left).obj K)
    have hnat' := congrArg (fun z ↦ z.hom) hnat
    change (adj.homEquiv (J M) ((boundedConstructibleToLocalizing Λ Y.left).obj K)
      (ObjectProperty.homMk
        ((rightDerivedLowerShriekOfCompactification Λ c).map a ≫ ε))).hom =
        D((j.left)_!open⟦Λ⟧).map a ≫
          (adj.homEquiv (J L') ((boundedConstructibleToLocalizing Λ Y.left).obj K)
            (ObjectProperty.homMk ε)).hom at hnat'
    rw [hnat']
    exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).homEquiv_naturality_left
      a _
  have htbij (M : (boundedConstructible (condensedRingObj Λ U.left)).FullSubcategory) :
      Function.Bijective (fun a : M.obj ⟶ L.obj ↦ a ≫ t) := by
    let M' := (boundedConstructibleToLocalizing Λ U.left).obj M
    have he : (fun a : M.obj ⟶ L.obj ↦ a ≫ t) =
        E M' ∘ (fun a ↦ (rightDerivedLowerShriekOfCompactification Λ c).map a ≫ ε) :=
      funext (fun a ↦ (ht M' a).symm)
    rw [he]
    exact (E M').bijective.comp (hε M)
  have : (boundedConstructible (condensedRingObj Λ U.left)).IsStableUnderShift ℤ :=
    boundedConstructible_stableUnderShift Λ U.left
  have : IsIso t := isIso_of_generator_postcomp
    (boundedConstructible (condensedRingObj Λ U.left))
    (localizing_le_doubleOrthogonal Λ U.left _ L'.property)
    (localizing_le_doubleOrthogonal Λ U.left _ hB) t (fun M hM ↦ htbij ⟨M, hM⟩)
  let e := asIso t
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e L.property.1,
    fun n ↦ constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)
      (L.property.2 n)⟩

private theorem affine_restriction_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory)
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [IsAffine U.left] (j : U ⟶ Z) [IsOpenImmersion j.left] (n : ℤ) :
    IsConstructibleModuleObject (condensedRingObj Λ U.left)
      ((j.left)^*⟦Λ⟧.obj ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  have h := affine_restriction_boundedConstructible Λ ℓ g hΛ G adj K j
  exact constructible_of_iso
    (((j.left)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app
      (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj).symm
    (h.2 n)

omit [Fact (ringChar k).Prime] in
private theorem affine_open_geometry (W : Z.left.Opens) (ha : IsAffineOpen W) :
    LocallyOfFiniteType (W.ι ≫ Z.hom) ∧
      QuasiCompact (W.ι ≫ Z.hom) ∧ IsSeparated (W.ι ≫ Z.hom) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsAffine W.toScheme := ha
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem affine_open_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory)
    (W : Z.left.Opens) (ha : IsAffineOpen W) (n : ℤ) :
    IsConstructibleModuleObject (condensedRingObj Λ W.toScheme)
      ((W.ι)^*⟦Λ⟧.obj ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  let Ua : Over (Spec (.of k)) := Over.mk (W.ι ≫ Z.hom)
  let j : Ua ⟶ Z := Over.homMk W.ι rfl
  obtain ⟨hfinite, hqc, hsep⟩ := affine_open_geometry W ha
  have : LocallyOfFiniteType Ua.hom := hfinite
  have : QuasiCompact Ua.hom := hqc
  have : IsSeparated Ua.hom := hsep
  have : IsAffine Ua.left := ha
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have h := affine_restriction_homology_constructible Λ ℓ g hΛ G adj K j n
  simpa only [j, Ua, Over.homMk_left, Over.mk_left] using h

/-- Every cohomology object of the supplied localizing right adjoint on a bounded
constructible input is constructible.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: choose a finite affine open cover of the source. On a chart, compact support is
extension by zero followed by the given proper pushforward. Compose the supplied adjunction
with the open adjunction. The affine compact-support representative therefore maps to the
restriction of `G K`, inducing Hom bijections from every bounded constructible generator.
Its cone is right orthogonal to those generators. Both objects lie in their double
orthogonal, so that map is an isomorphism. Exact pullback commutes with cohomology.
Finally, constructibility descends along the finite open cover by induction using the
open/closed criterion. This argument uses the general stratified finite-presentation
predicate directly and imposes no completeness or finite constant-model hypothesis.
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  classical
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  let C := Z.left.affineCover.finiteSubcover
  let e := (Fintype.equivFin C.I₀).symm
  let U (a : Fin (Fintype.card C.I₀)) : Z.left.Opens := (C.f (e a)).opensRange
  have hU : ⨆ a, U a = ⊤ := by
    exact (e.surjective.iSup_comp (fun a ↦ (C.f a).opensRange)).trans C.iSup_opensRange
  intro n
  apply constructible_of_finite_openCover Λ _ U hU
  intro a
  exact affine_open_homology_constructible Λ ℓ g hΛ G adj K (U a)
    (isAffineOpen_opensRange (C.f (e a))) n

end AlgebraicGeometry.ProEtale.CondensedRing
