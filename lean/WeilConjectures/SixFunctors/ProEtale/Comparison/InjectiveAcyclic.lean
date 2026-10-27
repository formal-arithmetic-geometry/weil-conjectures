/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineFiniteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineLift
public import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
public import WeilConjectures.CategoryTheory.Sites.CechComplexTransport
public import WeilConjectures.CategoryTheory.Sites.CechCriterionLift
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Acyclicity of pulled-back injective étale sheaves

Let `I` be an injective sheaf of abelian groups on the small étale site of a scheme `X`. The
comparison pullback `ν^* I` to the small pro-étale site is acyclic for the restriction `ν_*`:
`R^q ν_* (ν^* I) = 0` for `q > 0`.

The proof follows [Stacks, Tag 099U] and the blueprint
(`lem-weil-pbc-comparison-injective-acyclicity`, `prop-weil-pbc-site-comparison-finite-level`).
On an affine scheme `W`, the higher cohomology of `ν^* I` on `W_proét` is computed on the affine
pro-étale site and vanishes by the Čech criterion: every section of an epimorphism of sheaves
lifts along a single surjection, and the Čech complex of `ν^* I` for a surjection `q` of affine
pro-étale `W`-schemes is the filtered colimit of the Čech complexes of `I` for étale morphisms of
affine schemes presenting `q`, which are exact since `I` is injective. Testing the higher direct
images on affine étale `X`-schemes reduces the general case to the affine one.

## Main statements

- `AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar`: the Čech complexes of
  `ν^* I` for surjections of affine pro-étale schemes are exact in positive degrees.
- `AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar`:
  `H^q(W_proét, ν^* I) = 0` for `q > 0` and `W` affine.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {W : Scheme.{u}}

/-- The restriction to the affine pro-étale site of the comparison pullback of an étale sheaf
sends cofiltered limits of affine étale schemes to filtered colimits. -/
instance preservesRelativeFilteredColimits_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt W)
      ((AffineProEt.toProEt W).op ⋙ ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I).obj)
    where
  nonempty_isColimit {_} _ _ K c hc := by
    let c' : Cone ((K ⋙ AffineEtale.Spec W) ⋙ toProEt W) := (AffineProEt.toProEt W).mapCone c
    have hc' : IsLimit ((ProEt.forget W ⋙ CategoryTheory.Over.forget W).mapCone c') :=
      AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc
    have (j : _) : IsAffine ((K ⋙ AffineEtale.Spec W).obj j).left :=
      inferInstanceAs (IsAffine (Spec _))
    exact isColimit_comparisonUpperStar_mapCocone_of_isAffine AddCommGrpCat.{u + 1} I _ c' hc'

/-- On affine étale `W`-schemes, the comparison pullback `ν^* I` of an étale sheaf `I` has the
sections of `I`: the unit `I ⟶ ν_* ν^* I` is an isomorphism. -/
noncomputable def affineEtaleSectionsComparisonUpperStarIso
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (AffineEtale.Spec W).op ⋙ I.obj ≅ (AffineEtale.toAffineProEt W).op ⋙
      (AffineProEt.toProEt W).op ⋙ ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I).obj :=
  have := isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} W
  asIso ((AffineEtale.Spec W).op.whiskerLeft
    ((comparisonAdjunction AddCommGrpCat.{u + 1} W).unit.app I).hom)

variable [IsAffine W]

/-- The Čech complex of the comparison pullback of an injective étale sheaf, restricted to the
affine étale site, for a single morphism of affine étale schemes is exact in positive degrees.
-/
lemma exactAt_cechComplex_stage_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I]
    {X Y : W.AffineEtale} (α : X ⟶ Y) (q : ℕ) :
    ((Presheaf.cechComplex fun _ : Fin 1 ↦ CategoryTheory.Over.mk α).obj
      ((AffineEtale.toAffineProEt W).op ⋙ (AffineProEt.toProEt W).op ⋙
        ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I).obj)).ExactAt (q + 1) := by
  refine HomologicalComplex.ExactAt.of_iso ?_
    ((Presheaf.cechComplex _).mapIso (affineEtaleSectionsComparisonUpperStarIso I))
  rw [Presheaf.exactAt_cechComplex_comp_iff]
  exact Sheaf.exactAt_cechComplex_of_injective I _ q

/-- **Čech acyclicity of pulled-back injectives.** The Čech complex of the comparison pullback
`ν^* I` of an injective étale sheaf `I`, for a morphism `q` of affine pro-étale `W`-schemes, is
exact in positive degrees. Presenting `q` as a cofiltered limit of morphisms of affine étale
`W`-schemes, this Čech complex is the filtered colimit of the Čech complexes of `I` for these
morphisms, which are exact since `I` is injective.
(blueprint: `lem-weil-pbc-comparison-injective-acyclicity`) -/
theorem exactAt_cechComplex_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I]
    {V V' : W.AffineProEt} (f : V' ⟶ V) (q : ℕ) :
    ((Presheaf.cechComplex fun _ : Fin 1 ↦ CategoryTheory.Over.mk f).obj
      ((AffineProEt.toProEt W).op ⋙
        ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I).obj)).ExactAt (q + 1) := by
  obtain ⟨J, _, _, pV', pV, h, rfl⟩ := AffineProEt.exists_relativeLimitPresentation_hom W f
  exact Presheaf.exactAt_cechComplex_of_relativeLimitPresentation h _
    (fun j q ↦ exactAt_cechComplex_stage_comparisonUpperStar I _ q) q

/-- **Higher cohomology of pulled-back injectives on affine schemes.** Let `W` be affine and `I`
an injective étale sheaf on `W`. Then `H^q(W_proét, ν^* I) = 0` for `q > 0`: on the affine
pro-étale site, every section of an epimorphism of sheaves lifts along a single surjection and
the Čech complexes of `ν^* I` for surjections are exact in positive degrees
(`exactAt_cechComplex_comparisonUpperStar`), so the Čech criterion applies.
(blueprint: `lem-weil-pbc-comparison-injective-acyclicity`) -/
theorem isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] (q : ℕ) :
    IsZero (((globalSectionsFunctor AddCommGrpCat.{u + 1} W).rightDerived (q + 1)).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I)) := by
  have : LocallySmall.{u + 1} W.AffineProEt :=
    ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  have : EssentiallySmall.{u + 1} W.AffineProEt := essentiallySmall_of_small_of_locallySmall _
  have : HasSheafify (AffineProEt.topology W) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall _ _
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (AffineProEt.topology W) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  let Φ := (AffineProEt.toProEt W).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (AffineProEt.topology W) (ProEt.topology W)
  have : Φ.Additive := ⟨rfl⟩
  let G := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I
  -- the Čech criterion on the affine pro-étale site
  have hH : Subsingleton (Sheaf.H (Φ.obj G) (q + 1)) := by
    refine Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_lift
      (AffineProEt.isTerminalTop W) (fun _ ↦ True) trivial
      (fun V n U ↦ ∃ (V' : W.AffineProEt) (f : V' ⟶ V) (_ : n = 1),
        Surjective f.left ∧ ∀ a, U a = CategoryTheory.Over.mk f) ?_ ?_ _ ?_ q
    · rintro V n U ⟨V', f, rfl, hf, hU⟩
      obtain rfl : U = fun _ ↦ CategoryTheory.Over.mk f := funext hU
      exact ⟨fun _ _ ↦ trivial, AffineProEt.ofArrows_mem_topology_of_surjective f hf⟩
    · intro V _ G H g _ s
      obtain ⟨V', f, hf, ht⟩ := AffineProEt.exists_surjective_over_lift_of_epi V g s
      exact ⟨1, _, ⟨V', f, rfl, hf, fun _ ↦ rfl⟩, ht⟩
    · rintro V - n U ⟨V', f, rfl, hf, hU⟩ q
      obtain rfl : U = fun _ ↦ CategoryTheory.Over.mk f := funext hU
      exact exactAt_cechComplex_comparisonUpperStar I f q
  have h₁ := (Sheaf.subsingleton_H_iff_isZero_rightDerived (AffineProEt.topology W)
    (AffineProEt.isTerminalTop W) (q + 1) (Φ.obj G)).1 hH
  -- transport along the equivalence between sheaves on the two sites
  let e : globalSectionsFunctor AddCommGrpCat.{u + 1} W ≅
      Φ ⋙ Sheaf.sectionsFunctorAt (AffineProEt.topology W) (AffineProEt.top W) :=
    Iso.refl _
  have : Φ.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      Φ.asEquivalence.symm.toAdjunction
  exact h₁.of_iso ((NatIso.rightDerived e (q + 1)).app G ≪≫
    (Functor.rightDerivedCompIsoOfExact Φ _ (q + 1)).app G)

/-- A short complex of étale sheaves of abelian groups is exact if the short complexes of
sections over all affine étale schemes are exact. -/
lemma _root_.AlgebraicGeometry.Etale.exact_of_exact_affineEtale_sections
    {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (h : ∀ U : X.AffineEtale, (S.map (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op ((AffineEtale.Spec X).obj U)))).Exact) :
    S.Exact := by
  let Φ := (AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (AffineEtale.topology X) X.smallEtaleTopology
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  -- the presheaves underlying the restriction to the affine site form an exact short complex
  let T := (S.map Φ).map (sheafToPresheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1})
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact fun U ↦ h U.unop
  -- sheafifying it gives back the restriction, sheafification being exact
  have : (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1}).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{u + 1})
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm

omit [IsAffine W] in
/-- **Acyclicity of pulled-back injectives.** For an injective sheaf `I` of abelian groups on the
small étale site of a scheme `X`, the comparison pullback `ν^* I` is acyclic for the restriction
`ν_*`: `R^q ν_* (ν^* I) = 0` for `q > 0`. The higher direct images are computed on affine étale
`X`-schemes `U`, where they are the higher cohomology groups of `ν^* (I|_U)` on `U_proét`, which
vanish (`isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar`).
(blueprint: `prop-weil-pbc-site-comparison-finite-level`, acyclicity, for abelian groups) -/
theorem rightAcyclic_comparisonUpperStar_obj_of_injective_addCommGrpCat
    (I : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    (comparisonLowerStar AddCommGrpCat.{u + 1} W).rightAcyclic
      ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I) := by
  intro q
  let G := (comparisonUpperStar AddCommGrpCat.{u + 1} W).obj I
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine Etale.exact_of_exact_affineEtale_sections _ fun U ↦ ?_
  let T : W.ProEt := (toProEt W).obj ((AffineEtale.Spec W).obj U)
  have hT : IsZero (((sectionsFunctor AddCommGrpCat.{u + 1} T).rightDerived (q + 1)).obj G) := by
    refine isZero_rightDerived_sectionsFunctor_of_upperStar _ T G (q + 1) ?_
    refine IsZero.of_iso ?_ (((globalSectionsFunctor _ T.left).rightDerived (q + 1)).mapIso
      ((comparisonUpperStarCompUpperStarIso _ T.hom).app I))
    have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
    have : Etale T.hom := ((AffineEtale.Spec W).obj U).prop
    have : Injective ((Etale.upperStar AddCommGrpCat.{u + 1} T.hom).obj I) :=
      Etale.injective_upperStar_obj_of_etale' _ T.hom I
    exact isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar _ q
  have h' := hT.of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

omit [IsAffine W] in
/-- **Comparison of global cohomology for abelian sheaves.** The derived global sections of the
comparison pullback `ν^* M` of an étale sheaf of abelian groups are those of `M`:
`RΓ(W_proét, ν^* M) ≅ RΓ(W_ét, M)` in the bounded below derived category, by
`rightAcyclic_comparisonUpperStar_obj_of_injective_addCommGrpCat`. -/
noncomputable def rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoAddCommGrpCat
    (M : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (globalSectionsFunctor AddCommGrpCat.{u + 1} W).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj M)) ≅
      (Etale.sectionsFunctor AddCommGrpCat.{u + 1} W).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) :=
  rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoOfRightAcyclic _ W
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective_addCommGrpCat I) M

omit [IsAffine W] in
/-- **Comparison of global cohomology for abelian sheaves.** The derived global sections of the
comparison pullback `ν^* M` of an étale sheaf of abelian groups are those of `M` in each degree:
`R^qΓ(W_proét, ν^* M) ≅ R^qΓ(W_ét, M)`, the cohomology in degree `q` of
`rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoAddCommGrpCat`. -/
noncomputable def rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIsoAddCommGrpCat
    (M : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((globalSectionsFunctor AddCommGrpCat.{u + 1} W).rightDerived q).obj
        ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj M) ≅
      ((Etale.sectionsFunctor AddCommGrpCat.{u + 1} W).rightDerived q).obj M :=
  ((globalSectionsFunctor _ W).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).symm.app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoAddCommGrpCat M) ≪≫
    ((Etale.sectionsFunctor _ W).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app M

end AlgebraicGeometry.ProEtale
