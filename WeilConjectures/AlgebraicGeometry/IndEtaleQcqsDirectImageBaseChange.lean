/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
import WeilConjectures.CategoryTheory.DerivedCategory.HeartTestBoundedBelow
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Ind-etale base change for ordinary etale derived direct image

Source: Stacks Project, etale-cohomology.tex, Tag 03Q9 and remark-stalk-fibre;
sites-cohomology.tex, Tag 07A7; algebra.tex, Tags 05WR and 0GIP.
(blueprint: lem-per-ind-etale-qcqs-direct-image-base-change).

The square is the chosen scheme fibre product. The exchange is the existing
module-linear derived base-change map on ordinary bounded-below derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem indEtale_of_acrossUniverses
    {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
    (hf : RingHom.IndEtaleAcrossUniverses f) : f.IndEtale := by
  let eR := (ULift.ringEquiv : ULift.{u} R ≃+* R).toCommRingCatIso
  let eT := (ULift.ringEquiv : ULift.{u} T ≃+* T).toCommRingCatIso
  have h : CommRingCat.ofHom (RingHom.ulift.{u, u} f) =
      eR.hom ≫ CommRingCat.ofHom f ≫ eT.inv := rfl
  change (RingHom.ulift.{u, u} f).IndEtale at hf
  have ht := (RingHom.IndEtale.iff_ind_etale _).mp hf
  rw [h] at ht
  have ht' := ((MorphismProperty.ind.{u} CommRingCat.etale).cancel_left_of_respectsIso
    eR.hom (CommRingCat.ofHom f ≫ eT.inv)).mp ht
  exact (RingHom.IndEtale.iff_ind_etale f).mpr
    (((MorphismProperty.ind.{u} CommRingCat.etale).cancel_right_of_respectsIso
      (CommRingCat.ofHom f) eT.inv).mp ht')

private theorem bijective_conjugate
    {A B C D : Type*} (f : A → B) (g : C → D)
    (e : A ≃ C) (e' : B ≃ D) (h : ∀ x, e' (f x) = g (e x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hh : e' ∘ f = g ∘ e := funext h
  rw [← Function.Bijective.of_comp_iff' e'.bijective f, hh]
  exact Function.Bijective.of_comp_iff g e.bijective

-- The stated stalk criterion chooses the reversed pullback. Its underlying comparison
-- works for any Cartesian square, so repeat its proof with that square as a parameter.
private theorem exchange_stalk_criterion
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    {Y : Scheme.{u}} {p : Y ⟶ T} {r : Y ⟶ X}
    (sq : IsPullback p r g f)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (α : (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (f)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((p)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (r)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hα : α = (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
    (heval : Scheme.strictHenselizationPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationPointEvaluation x).comp a.hom)
    (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map α) ↔
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q) := by
  classical
  subst α
  obtain ⟨hA, hsA⟩ := strictHenselizationLocalStructure (x ≫ f)
  obtain ⟨hB, hsB⟩ := strictHenselizationLocalStructure x
  let := hA
  let := hB
  have := hsA
  have := hsB
  have := evaluation_local (x ≫ f)
  have := evaluation_local x
  have : IsLocalHom ((Scheme.strictHenselizationPointEvaluation x).comp a.hom) :=
    heval ▸ evaluation_local (x ≫ f)
  have : IsLocalHom a.hom :=
    isLocalHom_of_comp a.hom (Scheme.strictHenselizationPointEvaluation x)
  let jA := Scheme.strictHenselizationStructuralMap (x ≫ f)
  let jB := Scheme.strictHenselizationStructuralMap x
  let eA : Spec (Scheme.strictHenselizationRing (x ≫ f)) ≅
      Scheme.strictLocalization (x ≫ f) :=
    asIso (Spec.map (Scheme.smallStrictHenselizationColimitIso (x ≫ f)).inv)
  let eB : Spec (Scheme.strictHenselizationRing x) ≅ Scheme.strictLocalization x :=
    asIso (Spec.map (Scheme.smallStrictHenselizationColimitIso x).inv)
  have heA : eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f) = jA :=
    Scheme.smallStrictHenselizationColimitIso_toBase (x ≫ f)
  have heB : eB.hom ≫ Scheme.strictLocalizationToBase x = jB :=
    Scheme.smallStrictHenselizationColimitIso_toBase x
  let ρA := Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.lift (Scheme.strictHenselizationPointEvaluation (x ≫ f))))
  let ρB := Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.lift (Scheme.strictHenselizationPointEvaluation x)))
  have hρA : ρA ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Scheme.strictHenselizationRing (x ≫ f)))) ≫
      eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f) = x ≫ f := by
    rw [heA, ← Spec.map_comp_assoc]
    exact Scheme.strictHenselizationClosedLift_over (x ≫ f)
  have hρB : ρB ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Scheme.strictHenselizationRing x))) ≫
      eB.hom ≫ Scheme.strictLocalizationToBase x = x := by
    rw [heB, ← Spec.map_comp_assoc]
    exact Scheme.strictHenselizationClosedLift_over x
  have hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map a.hom)) =
      𝟙 (Spec (.of Ω)) ≫ ρA := by
    rw [Category.id_comp]
    dsimp only [ρA, ρB]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact heval.symm
  let p₀ := pullback.snd jA g
  let f₀ := pullback.fst jA g
  let p₁ := pullback.map (jB ≫ f) g jA g (Spec.map a) (𝟙 T) (𝟙 S)
    ((Category.comp_id _).trans ha.symm)
    ((Category.comp_id g).trans (Category.id_comp g).symm)
  let f₁ := pullback.fst (jB ≫ f) g
  have sq₀ : IsPullback p₀ f₀ g (eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f)) := by
    rw [heA]
    exact (IsPullback.of_hasPullback jA g).flip
  have sq₁ : IsPullback p₁ f₁ f₀ (Spec.map a) := by
    refine IsPullback.of_right ?_ (by simp [p₁, f₁, f₀])
      (IsPullback.of_hasPullback jA g).flip
    have hp : p₁ ≫ pullback.snd jA g = pullback.snd (jB ≫ f) g := by simp [p₁]
    rw [hp, ha]
    exact (IsPullback.of_hasPullback (jB ≫ f) g).flip
  obtain ⟨eA', heA'⟩ := localization_model_transport (x ≫ f)
    (𝟙 (Spec (.of Ω)) ≫ 𝟙 (Spec (.of Ω)) ≫ (x ≫ f)) (by simp) eA
  obtain ⟨eB', heB'⟩ := localization_model_transport x
    (𝟙 (Spec (.of Ω)) ≫ x) (by simp) eB
  have hA' : eA'.hom ≫ Scheme.strictLocalizationToBase
      (𝟙 (Spec (.of Ω)) ≫ 𝟙 (Spec (.of Ω)) ≫ (x ≫ f)) = jA := heA'.trans heA
  have hB' : eB'.hom ≫ Scheme.strictLocalizationToBase
      (𝟙 (Spec (.of Ω)) ≫ x) = jB := heB'.trans heB
  obtain ⟨c₁, c₂, hc⟩ := exists_addEquiv_strictHenselization_abelian_stalkExchange
    (A := Scheme.strictHenselizationRing (x ≫ f))
    (B := Scheme.strictHenselizationRing x)
    sq (x ≫ f) x (𝟙 _) (by simp) (𝟙 _)
    eA' eB' a.hom ρA ρB
    (by simpa only [Category.assoc, hA', reassoc_of% hB', jA, jB] using! ha)
    (by rw [hA']; simpa only [heA] using hρA)
    (by rw [hB']; simpa only [heB] using hρB)
    hρ p₀ f₀ (by rw [hA']; simpa only [heA] using sq₀) p₁ f₁ sq₁ F q
  obtain ⟨b₁, b₂, hb⟩ := exists_addEquiv_strictLocal_abelian_total_exchange
    a.hom f₀ f₁ p₁ sq₁ ((upperStar AddCommGrpCat.{u + 1} p₀).obj F) q
  rw [ConcreteCategory.isIso_iff_bijective]
  apply bijective_conjugate _ _ (c₁.trans b₁).toEquiv (c₂.trans b₂).toEquiv
  intro z
  change b₂ (c₂ _) = cohomologyMap p₁ _ q (b₁ (c₁ z))
  rw [hc]
  exact hb (c₁ z)


private theorem exchange_source_zero
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) [L.IsGE n] {q : ℤ} (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj L)) := by
  exact ((upperStar AddCommGrpCat.{u + 1} g).map_isZero
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar AddCommGrpCat.{u + 1} f) L n hq)).of_iso
    (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _).symm

private theorem exchange_target_zero
    {X X' T : Scheme.{u}} (v : X' ⟶ X) (f' : X' ⟶ T)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) [L.IsGE n] {q : ℤ} (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (((v)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj L)) := by
  have : ((upperStar AddCommGrpCat.{u + 1} v).mapDerivedCategoryPlus.obj L).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    intro i hi
    exact ((upperStar AddCommGrpCat.{u + 1} v).map_isZero
      (DerivedCategory.Plus.isZero_homology_of_isGE L n i hi)).of_iso
      (((upperStar AddCommGrpCat.{u + 1} v).mapDerivedCategoryPlusHomologyFunctorIso
        i).app _).symm
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    (lowerStar AddCommGrpCat.{u + 1} f') _ n hq

/-- Affine locally ind-etale base change commutes with the ordinary bounded-below
etale derived direct image of a quasi-compact quasi-separated morphism.
The affine-chart condition uses the induced map of global section rings, with the
existing canonical common-universe transport of the ind-etale predicate. Sheaves
with values in `ModuleCat A` are the existing encoding of modules over the constant
ring sheaf. The exchange map is the canonical adjunction mate, computed on
resolutions by `derivedExchangeTermwise`, rather than a chosen comparison arrow.

Source: Stacks Project, Tag 03Q9 and remark-stalk-fibre, Tag 07A7, Tags 05WR and 0GIP.
(blueprint: lem-per-ind-etale-qcqs-direct-image-base-change).

Proof:
1. By lem-weil-pbc-exchange-forget-coefficients, forgetting A identifies inverse
   images, derived direct images and their exchange, and reflects invertibility.
   It suffices to prove the assertion for arbitrary bounded-below abelian complexes.
2. For a geometric point t of S', use the same algebraically closed field for its
   image s in S. The affine-chart hypothesis and
   lem-trf-ind-etale-strict-local-invariance identify S'_(t) with S_(s) over S.
   The fibre-product universal property then identifies the two strict-local
   pullbacks of X by an isomorphism over X; its inverse is induced by the inverse
   strict-local isomorphism, with both inverse equations checked on projections.
3. The cohomology pullback along this isomorphism is invertible in every degree,
   with inverse induced by its inverse, using lem-weil-pbc-site-cohomology-pullback.
   Apply lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion and
   lemma-weil-pbc-geometric-stalk-conservative to obtain the higher-direct-image
   exchange isomorphism for every abelian sheaf F and q >= 0. The morphism f is
   qcqs, exactly as required by the strict-local criterion; F need not be torsion.
4. The augmentations of lem-weil-pbc-left-exact-injective-resolution-degree-zero
   identify the degree-zero comparison with the underived exchange: use
   lem-weil-pbc-derived-exchange-termwise and the unit equation of
   lem-sbc-right-derived-base-change-zero-unit. The augmentations are invertible,
   so the underived exchange is invertible naturally in F. Direct images are
   additive and left exact, and inverse images are exact by
   prop-weil-pbc-inverse-image-exact, as required for this degree-zero argument.
5. For an injective I, lem-weil-pbc-derived-functor-injective-vanishing and step 3
   imply that the inverse image of I is acyclic for the base-changed direct image
   in the sense of def-sp-acyclic. Preservation of injectives is not needed.
6. Choose a bounded-below injective representative I of the given complex by
   lem-weil-pbc-dplus-injective-representative. Its inverse image P is bounded below
   and termwise acyclic by step 5. Thus src-right-derived-functor-plus-acyclic-unit
   makes the derived-functor unit on P invertible. Choose an injective representative
   J of QP and lift its derived isomorphism to j : P -> J by
   lem-weil-pbc-kinjective-hom-derived. Naturality of the unit, invertibility of its
   components on P and J, and invertibility of Qj imply invertibility of Q(f'_*(j)).
   Step 4 gives a termwise exchange isomorphism of complexes, whose inverse commutes
   with differentials by naturality. By lem-weil-pbc-derived-exchange-termwise the
   actual derived exchange is this isomorphism followed by Q(f'_*(j)), conjugated
   by the canonical invertible representative comparisons. It is therefore
   invertible for every bounded-below abelian complex. Step 1 gives the A-linear
   assertion for every K.
-/
theorem isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale
    (A : Type (u + 1)) [CommRing A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffineHom g]
    (hlocal : ∀ (t : S'), ∃ (V : S'.Opens) (U : S.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ g ∧ RingHom.IndEtaleAcrossUniverses e.appTop.hom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq).app K) := by
  classical
  have hl : ∀ (t : S'), ∃ (V : S'.Opens) (U : S.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ g ∧ proAffineEtale e := by
    intro t
    obtain ⟨V, U, ht, hV, hU, e, he, hi⟩ := hlocal t
    let := hV
    let := hU
    exact ⟨V, U, ht, hV, hU, e, he,
      proAffineEtale_iff_appTop.mpr (indEtale_of_acrossUniverses e.appTop.hom hi)⟩
  -- Strict-local invariance proves the sheaf case in every degree. The generic heart
  -- test then extends it to D+, avoiding underived exchange and acyclic resolutions.
  let sq := IsPullback.of_hasPullback f g
  let τ := derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  have hsingle (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      IsIso (τ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
    apply (DerivedCategory.Plus.isIso_iff _).mpr
    intro q
    by_cases hq : 0 ≤ q
    · lift q to ℕ using hq
      let α := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        (τ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
      apply Scheme.isIso_of_isIso_sheafFiber_map α
      intro t
      let x := S'.algClosurePoint t
      obtain ⟨e, he, hp, _⟩ := Scheme.indEtale_strictLocal_invariance g hl x (x ≫ g) rfl
      let a := Spec.preimage e.hom
      have ha : Spec.map a = e.hom := Spec.map_preimage e.hom
      have heval : Scheme.strictHenselizationPointEvaluation (x ≫ g) =
          (Scheme.strictHenselizationPointEvaluation x).comp a.hom := by
        have hh : a ≫ CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation x) =
            CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation (x ≫ g)) := by
          apply Spec.map_injective
          rw [Spec.map_comp, ha]
          exact hp
        exact (congrArg CommRingCat.Hom.hom hh).symm
      have hstruct : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ g) =
          Scheme.strictHenselizationStructuralMap x ≫ g := by rw [ha]; exact he
      have : IsIso (Spec.map a) := by rw [ha]; infer_instance
      have hi := (exchange_stalk_criterion g f sq F q α rfl x a heval hstruct).mpr
        (cohomologyMap_bijective _ _ _)
      rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
        ((Scheme.pointSmallEtale x).uliftSheafFiberIso AddCommGrpCat.{u + 1})]
      exact hi
    · have hlt : q < 0 := lt_of_not_ge hq
      exact ⟨⟨0, (exchange_source_zero f g _ 0 hlt).eq_of_src _ _,
        (exchange_target_zero (pullback.fst f g) (pullback.snd f g) _ 0 hlt).eq_of_src
          _ _⟩⟩
  let csq : ChosenCartesianSquare (pullback.fst f g) (pullback.snd f g) f g :=
    { toCommSq := sq.toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  apply (exchange_forget_coefficients A csq K).2.2.2.2.2.2.2.2.2.mpr
  apply (DerivedCategory.Plus.heart_test_bounded_below _ _ τ
    (fun L ↦ (NatTrans.shift_app_comm τ (1 : ℤ) L).symm)
    ?_ ?_ _ (fun _ ↦ hsingle _)).1
  · intro L n hL q hq
    have : L.IsGE n := by
      rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
      exact hL
    exact exchange_source_zero f g L n hq
  · intro L n hL q hq
    have : L.IsGE n := by
      rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
      exact hL
    exact exchange_target_zero (pullback.fst f g) (pullback.snd f g) L n hq

end AlgebraicGeometry.Etale
