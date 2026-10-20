/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Amplitude of open direct image on classical finite-coefficient sheaves

Source: blueprint main-20261015, sec-six-functors-basics,
sk-cor-geo-open-finiteness-ii/det-geo-open-finiteness-ii-amplitude.md;
Stacks Project, Tags 0F10, 0D6J and 09A6
(blueprint: det-geo-open-finiteness-ii-amplitude).

Fixed-ring module sheaves present modules over the specified coefficient ring sheaves,
via `finiteCoefficientEtaleRealization` and `finiteCoefficientRealization`. The comparison
is the recorded inverse image of `proEtaleSiteComparisonModules`. The derived images here
are its exact derived functor followed by the bounded below right derived direct image.
-/

@[expose] public section

set_option autoImplicit false
-- Elaborate the coefficient and derived comparison proofs sequentially.
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private abbrev coefficientForget (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

private instance (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    (coefficientForget Λ X).Additive where
  map_add := by intro F G f g; ext U; rfl

private instance (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (coefficientForget Λ X) := by
  have : PreservesFiniteLimits (coefficientForget Λ X ⋙
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
    change PreservesFiniteLimits (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) ⋙
        (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

private instance (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (coefficientForget Λ X) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  let e : Sheaf.composeAndSheafify X.smallEtaleTopology U ≅
      sheafCompose X.smallEtaleTopology U :=
    Functor.isoWhiskerLeft (sheafCompose X.smallEtaleTopology U)
      (sheafificationNatIso X.smallEtaleTopology AddCommGrpCat.{u + 1}).symm ≪≫
      Functor.rightUnitor (sheafCompose X.smallEtaleTopology U)
  have : (Sheaf.composeAndSheafify X.smallEtaleTopology U).IsLeftAdjoint := inferInstance
  have : (sheafCompose X.smallEtaleTopology U).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso e
  exact inferInstanceAs (PreservesFiniteColimits (sheafCompose X.smallEtaleTopology U))

/-- The finite-ring realization and the universe-correct Čech criterion prove evaluation
acyclicity without assuming that forgotten injectives remain injective (Stacks 03FD). -/
private theorem coefficientForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((coefficientForget Λ X).obj G)) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let E := finiteCoefficientEtaleRealization X Λ
  have : E.IsEquivalence := finiteCoefficientEtaleRealization_isEquivalence X Λ
  let O := finiteCoefficientEtaleRingSheaf X Λ
  let I : SheafOfModules.{u + 1} O := E.obj G
  have : Injective I := E.injective_obj G
  let eAb : (SheafOfModules.toSheaf O).obj I ≅ (coefficientForget Λ X).obj G :=
    asIso ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).counit.app
      ((coefficientForget Λ X).obj G))
  let J := X.smallEtaleTopology.toPrecoverage
  have hcech (U : X.Etale) (T : Type (u + 1)) (V : T → X.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := CategoryTheory.SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨c⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso c.symm)
  have hvan := Scheme.isZero_rightDerived_etale_of_cech_vanishing X Set.univ
    (fun W _ V f ↦ Sieve.ofArrows V f ∈ X.smallEtaleTopology W)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech W (Set.mem_univ _) (n + 1) (Nat.zero_lt_succ n)
  exact hvan.of_iso
    (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).mapIso eAb.symm)

/-- The sheafified section-cohomology formula and acyclic base change give the
coefficient comparison for finite associative rings (Stacks 072W and 0D6J(3)). -/
private theorem coefficientForget_directImage_comparison
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
          (coefficientForget Λ Y).mapDerivedCategoryPlus ≅
        (coefficientForget Λ X).mapDerivedCategoryPlus ⋙
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus) := by
  let e : Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ coefficientForget Λ Y ≅
      coefficientForget Λ X ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} f := Iso.refl _
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange e.hom) := by
    apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic e
    intro I hI n
    let G := (coefficientForget Λ X).obj I
    let c := higherDirectImageSheafifiedPresheaf f G (n + 1)
    have hz : IsZero ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
          { obj := fun W ↦
              ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj W).rightDerived
                  (n + 1)).obj G
            map := fun h ↦ (NatTrans.rightDerived
              (Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                ((evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map h)) (n + 1)).app G
            map_id := fun W ↦ by
              simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                NatTrans.rightDerived_id, NatTrans.id_app]
            map_comp := fun h k ↦ by
              simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                NatTrans.rightDerived_comp, NatTrans.comp_app] })) := by
      apply Functor.map_isZero
      apply Functor.isZero
      intro W
      exact coefficientForget_injective_evaluation_acyclic Λ X I _ n
    have hH := hz.of_iso c.symm
    exact hH.of_iso
      ((((Etale.lowerStar AddCommGrpCat.{u + 1} f)
        |>.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
          (n + 1)).app G).symm)
  exact ⟨asIso (Functor.rightDerivedFunctorPlusBaseChange e.hom)⟩

/-- An open immersion of finite-type schemes over a field has finite torsion etale
cohomological dimension, bounds higher etale and classical pro-etale images of module
sheaves by that dimension, and sends the cohomological interval `[a,b]` to `[a,b+d]`.
The existential natural number is exactly the recorded dimension, so it asserts its
finiteness, rather than merely choosing an unspecified upper bound.
Source: blueprint main-20261015, det-geo-open-finiteness-ii-amplitude, clauses (1)-(3);
Stacks Project, Tags 0F10, 0D6J and 09A6
(blueprint: det-geo-open-finiteness-ii-amplitude).

Proof:
1. Finite-type schemes over a field are Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Their opens are quasi-compact by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Thus X, Y and j are qcqs.
   Apply lem-kun-0f10 to get finite cd(j); def-kun-cd gives its natural-number value d,
   including the empty source case.
2. The ring-sheaf module categories are Grothendieck by
   lem-weil-pbc-ring-sheaves-grothendieck. Functorial injective embeddings and
   lem-weil-pbc-dplus-injective-representative give injective resolutions, starting in
   degree zero for sheaves. The K-injective computation is def-sfb-right-derived-functor.
   Underived direct image evaluates on fibre products. Exact forgetting of scalars
   (lem-weil-pbc-module-sheaves-colimits-forgetful) commutes with cohomology and reflects
   zero objects; no commutativity of the coefficient ring is used.
3. For a module injective I, the ringed-site evaluation comparison
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and injective acyclicity
   from lemma-weil-pbc-leray-acyclicity show positive abelian section cohomology vanishes.
   By lem-weil-pbc-higher-direct-image-sheafified-presheaf the forgotten I is acyclic for
   abelian direct image. The acyclic-resolution criterion of Leray therefore identifies
   module higher images with abelian higher images after forgetting. This does not
   assume forgetting preserves injectives. The degree-zero resolutions also give
   negative-degree vanishing.
4. Every module sheaf is torsion after forgetting: the stipulated power annihilates it;
   alternatively a positive additive exponent of the finite ring annihilates all
   modules. The defining bound def-kun-cd and step 3 give clause (1).
5. The canonical qcqs comparison prop-weil-pbc-comparison-direct-image identifies the
   pro-etale image of the comparison pullback with the comparison pullback of the
   etale image. Exactness from prop-weil-pbc-site-comparison-finite-level commutes with
   kernels, images and cokernels, hence cohomology. Step 4 gives clause (2), and step 3
   supplies its lower bound zero.
6. Apply thm-sp-truncation-e2 to etale direct image and M. Its convergent truncation
   spectral sequence has E2 terms R^p j_* H^q(M), zero outside 0 <= p <= d and
   a <= q <= b. For n outside [a,b+d] every associated graded object of the finite
   exhaustive separated abutment filtration is zero. Successive equality of its terms
   identifies the whole abutment with its zero end term. Apply step 5 to M to obtain
   clause (3). This includes a > b, missing cohomology degrees, and the zero complex;
   no constructibility, separatedness over k or invertibility in k is required. -/
theorem openDirectImage_classical_amplitude
    (k : Type u) [Field k] (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (ℓ : ℕ) (hΛ : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : Λ, (ℓ ^ r) • x = 0)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] :
    ∃ d : ℕ,
      (@Scheme.Hom.torsionEtaleCohomologicalDimension _ _ j
        (@quasiCompact_of_compactSpace X Y j
          ((quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance)
          (@IsLocallyNoetherian.quasiSeparatedSpace Y
            (LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k)))))
        (@QuasiSeparated.of_quasiSeparatedSpace X Y j
          (@IsLocallyNoetherian.quasiSeparatedSpace X
            (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k)))))) = (d : ℕ∞) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ),
        (d : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) j).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)))) ∧
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ),
        (d : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) q).obj
            ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))))) ∧
      (∀ (a b : ℤ)
        (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ q : ℤ, (q < a ∨ b < q) →
          IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj M)) →
        ∀ q : ℤ, (q < a ∨ b + (d : ℤ) < q) →
          IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) q).obj
              ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
                ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj M)))) :=
by
  classical
  have _hΛ := hΛ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : QuasiCompact j := quasiCompact_of_compactSpace j
  have : QuasiSeparated j := QuasiSeparated.of_quasiSeparatedSpace j
  have hfin := (torsionEtaleCohomologicalDimension_finite_of_finiteType k X Y j).1
  unfold Scheme.Hom.torsionEtaleCohomologicalDimension at hfin ⊢
  have hs : {d : ℕ∞ | ∃ n : ℕ, d = (n : ℕ∞) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion →
        ∀ q : ℤ, (n : ℤ) < q →
          IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j).obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, sInf_empty] at hfin
    exact (lt_irrefl _ hfin)
  obtain ⟨d, hd, hab⟩ := csInf_mem hs
  have heta (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
      (hq : (d : ℤ) < q) :
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
    let TX := coefficientForget Λ X
    let TY := coefficientForget Λ Y
    let RF := (Etale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus
    let RA := (Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus
    let S := (DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
    have htor : (TX.obj F).IsTorsion :=
      Sheaf.IsTorsion.of_forall_isAddTorsion fun U ↦
        IsAddTorsion.module_of_finite Λ (F.obj.obj U)
    have hz := hab (TX.obj F) htor q hq
    obtain ⟨e⟩ := coefficientForget_directImage_comparison Λ j
    let c : TY.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj (RF.obj S)) ≅
        (DerivedCategory.Plus.homologyFunctor _ q).obj
          (RA.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj (TX.obj F))) :=
      (TY.mapDerivedCategoryPlusHomologyFunctorIso q).app (RF.obj S) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (e.app S ≪≫ RA.mapIso ((TX.mapDerivedCategoryPlusSingleFunctor 0).app F))
    have hz' := hz.of_iso c
    change IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj (RF.obj S))
    apply (IsZero.iff_id_eq_zero _).2
    apply TY.map_injective
    rw [TY.map_id, TY.map_zero]
    exact hz'.eq_of_src _ _
  have htransfer
      (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (q : ℤ)
      (hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) j).obj M))) :
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj M))) := by
    let V := comparisonUpperStar (ModuleCat.{u + 1} Λ) Y
    have : PreservesFiniteLimits V := (siteComparison_finiteLevel Y Λ).1
    have : PreservesFiniteColimits V := (siteComparison_finiteLevel Y Λ).2.1
    have := isIso_comparisonDirectImagePlus Λ j
    let e := asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange j (ModuleCat.{u + 1} Λ)))
    exact (V.map_isZero hz).of_iso
      ((V.mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso (e.app M)).symm
  refine ⟨d, hd, heta, fun F q hq ↦ htransfer _ q (heta F q hq), ?_⟩
  intro a b M hM q hq
  apply htransfer
  let f := Etale.lowerStar (ModuleCat.{u + 1} Λ) j
  have hge : (DerivedCategory.Plus.ι.obj M).IsGE a :=
    (DerivedCategory.isGE_iff _ a).2 fun i hi ↦ hM i (Or.inl hi)
  have hle : (DerivedCategory.Plus.ι.obj M).IsLE b :=
    (DerivedCategory.isLE_iff _ b).2 fun i hi ↦ hM i (Or.inr hi)
  rcases hq with hq | hq
  · have : M.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff M a).1 hge
    exact f.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE M a hq
  · have hsingle (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
        (f.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE d := by
      apply (DerivedCategory.isLE_iff _ _).2
      intro i hi
      exact (heta F i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso
          (f.rightDerivedFunctorPlusCompatibility.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm)
    let : f.rightDerivedFunctor.CommShift ℤ :=
      Functor.CommShift.ofIso f.rightDerivedFunctorIsoKInjectives.symm ℤ
    have : f.rightDerivedFunctor.IsTriangulated := by
      have := Functor.CommShift.ofIso_compatibility
        f.rightDerivedFunctorIsoKInjectives.symm ℤ
      exact Functor.isTriangulated_of_iso f.rightDerivedFunctorIsoKInjectives.symm
    have hbound := DerivedCategory.isLE_obj_of_isLE f.rightDerivedFunctor (d : ℤ)
      hsingle (DerivedCategory.Plus.ι.obj M) ⟨⟨a, hge⟩, ⟨b, hle⟩⟩ b
    exact ((DerivedCategory.isLE_iff _ _).1 hbound q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (f.rightDerivedFunctorPlusCompatibility.app M))

end AlgebraicGeometry.ProEtale
