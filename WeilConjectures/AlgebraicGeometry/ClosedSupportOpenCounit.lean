/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The actual open counit on a closed pushforward supported in the open

Source: Stacks Project, etale-cohomology.tex, Tags 03S3, 03S5 and 095L;
derived.tex, Tag 015F (blueprint: lem-pur-closed-support-open-counit).

The restriction isomorphism is normalized on sections by the unique fibre-product
identification over both factors. The derived arrows use the specified localization
of the original sheaf adjunction, including the standard degree-zero comparisons.

## Main definitions

- `openCounitRestrictionLift`: the inverse restriction map in the derived category.
- `closedSupportOpenCounitArrow`: its image under extension by zero followed by the counit.

## Main statement

- `closedSupport_openCounit`: normalized restriction, vanishing, invertibility and naturality.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v w h

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

section ExactFunctor

variable {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

/-- Transport an inverse comparison to degree zero using the standard exact-functor
comparison. Source: Stacks 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def exactRestrictionLift (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : D) (G : C) (ρ : R.obj F ≅ G) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj G ⟶
      R.mapDerivedCategory.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
  (_root_.DerivedCategory.singleFunctor _ 0).map ρ.inv ≫
    (R.mapDerivedCategorySingleFunctor 0).inv.app F

/-- The counit composite after the inverse degree-zero comparison.
Source: Stacks 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def exactCounitComposite {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (F : D) (G : C) (ρ : R.obj F ≅ G) :
    L.mapDerivedCategory.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj F :=
  L.mapDerivedCategory.map (exactRestrictionLift R F G ρ) ≫
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)

end ExactFunctor

/-- The inverse restriction isomorphism on degree-zero sheaves, with the standard
exact-functor comparison identifying the target with the derived inverse image.
Source: Stacks 03S3 and 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def openCounitRestrictionLift (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj G ⟶
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
  exactRestrictionLift (upperStar (ModuleCat.{u + 1} A) j) F G ρ

/-- The actual arrow `Dj_! G → F`: apply `Dj_!` to the normalized inverse
restriction map and then apply the counit of the localized original sheaf adjunction.
Source: Stacks 03S3, 095L and 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def closedSupportOpenCounitArrow (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj F :=
  exactCounitComposite
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) F G ρ

private noncomputable def supportPullbackIso {Y U Z : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U) (V : U.Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ i).obj V ≅
      (MorphismProperty.Over.pullback @Etale ⊤ (i ≫ j)).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V) := by
  let e : pullback V.hom i ≅ pullback (V.hom ≫ j) (i ≫ j) :=
    { hom := pullback.lift (pullback.fst V.hom i) (pullback.snd V.hom i)
        (by simpa only [← Category.assoc] using
          congrArg (fun f ↦ f ≫ j) (pullback.condition (f := V.hom) (g := i)))
      inv := pullback.lift (pullback.fst (V.hom ≫ j) (i ≫ j))
        (pullback.snd (V.hom ≫ j) (i ≫ j))
        (by apply (cancel_mono j).1; simpa only [Category.assoc] using
          pullback.condition (f := V.hom ≫ j) (g := i ≫ j))
      hom_inv_id := by
        apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp] }
  exact MorphismProperty.Over.isoMk e (pullback.lift_snd _ _ _)

private theorem supportPullbackIso_fst {Y U Z : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U) (V : U.Etale) :
    (supportPullbackIso j i V).hom.left ≫ pullback.fst (V.hom ≫ j) (i ≫ j) =
      pullback.fst V.hom i := pullback.lift_fst _ _ _

private theorem supportPullbackIso_snd {Y U Z : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U) (V : U.Etale) :
    (supportPullbackIso j i V).hom.left ≫ pullback.snd (V.hom ≫ j) (i ≫ j) =
      pullback.snd V.hom i := pullback.lift_snd _ _ _

attribute [irreducible] supportPullbackIso

private noncomputable def supportPullbackNatIso {Y U Z : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U) :
    MorphismProperty.Over.pullback @Etale ⊤ i ≅
      MorphismProperty.Over.map ⊤ (inferInstance : Etale j) ⋙
        MorphismProperty.Over.pullback @Etale ⊤ (i ≫ j) := by
  refine NatIso.ofComponents (supportPullbackIso j i) ?_
  intro V W f
  apply MorphismProperty.Over.Hom.ext
  change ((MorphismProperty.Over.pullback @Etale ⊤ i).map f).left ≫
    (supportPullbackIso j i W).hom.left =
      (supportPullbackIso j i V).hom.left ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ (i ≫ j)).map
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).map f)).left
  apply pullback.hom_ext
  · change _ ≫ pullback.fst (W.hom ≫ j) (i ≫ j) =
      _ ≫ pullback.fst (W.hom ≫ j) (i ≫ j)
    rw [Category.assoc, supportPullbackIso_fst]
    rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    rw [Category.assoc]
    change _ = (supportPullbackIso j i V).hom.left ≫
      pullback.lift (pullback.fst (V.hom ≫ j) (i ≫ j) ≫ f.left)
        (pullback.snd (V.hom ≫ j) (i ≫ j)) _ ≫
          pullback.fst (W.hom ≫ j) (i ≫ j)
    rw [pullback.lift_fst, ← Category.assoc, supportPullbackIso_fst]
  · change _ ≫ pullback.snd (W.hom ≫ j) (i ≫ j) =
      _ ≫ pullback.snd (W.hom ≫ j) (i ≫ j)
    rw [Category.assoc, supportPullbackIso_snd]
    rw [MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
    rw [Category.assoc]
    change _ = (supportPullbackIso j i V).hom.left ≫
      pullback.lift (pullback.fst (V.hom ≫ j) (i ≫ j) ≫ f.left)
        (pullback.snd (V.hom ≫ j) (i ≫ j)) _ ≫
          pullback.snd (W.hom ≫ j) (i ≫ j)
    rw [pullback.lift_snd, supportPullbackIso_snd]

private noncomputable def supportRestrictionIso (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U)
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
      ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B) ≅
        (lowerStar (ModuleCat.{u + 1} A) i).obj B :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op (supportPullbackNatIso j i)) B.obj)

private theorem supportRestrictionIso_hom_app (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U)
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (V : U.Etale) :
    (supportRestrictionIso A j i B).hom.hom.app (op V) =
      B.obj.map (supportPullbackIso j i V).hom.op := rfl

attribute [irreducible] supportRestrictionIso

private theorem supportSectionsZero (A : Type (u + 1)) [CommRing A]
    {Y Z : Scheme.{u}} (k : Z ⟶ Y)
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (T : Y.Etale) (h : Disjoint (Set.range T.hom) (Set.range k)) :
    IsZero (((lowerStar (ModuleCat.{u + 1} A) k).obj B).obj.obj (op T)) := by
  have : IsEmpty ↥((MorphismProperty.Over.pullback @Etale ⊤ k).obj T).left :=
    Scheme.isEmpty_pullback T.hom k h
  exact IsTerminal.isZero (Scheme.Etale.isTerminalSectionsOfIsEmpty B
    ((MorphismProperty.Over.pullback @Etale ⊤ k).obj T))

private theorem supportCounitIsIso (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U)
    [IsClosedImmersion (i ≫ j)]
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit.app
      ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)) := by
  let C := ModuleCat.{u + 1} A
  let F := (lowerStar C (i ≫ j)).obj B
  let ε := (openImmersionLowerShriekUpperStarAdjunction C j).counit.app F
  change IsIso ε
  refine Scheme.isIso_of_isIso_sheafFiber_map ε fun x ↦ ?_
  let s := Y.algClosurePoint x
  by_cases hs : s.base (IsLocalRing.closedPoint _) ∈ Set.range j.base
  · have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map C j ε
      (inferInstance) (IsOpenImmersion.lift j s
        (Scheme.range_base_subset_of_closedPoint_mem s hs))
    rw [IsOpenImmersion.lift_fac] at h
    exact h
  · have hsrc := isZero_uliftSheafFiber_openImmersionLowerShriek_obj C j s hs
      ((upperStar C j).obj F)
    let W : Y.Opens :=
      ⟨(Set.range (i ≫ j))ᶜ, (i ≫ j).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hdisj : Disjoint (Set.range W.ι.base) (Set.range (i ≫ j).base) := by
      rw [Scheme.Opens.range_ι]
      exact disjoint_compl_left
    have hmem : s.base (IsLocalRing.closedPoint _) ∈ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      change s.base (IsLocalRing.closedPoint _) ∉ Set.range (i ≫ j)
      rintro ⟨z, hz⟩
      apply hs
      exact ⟨i.base z, hz⟩
    let t := IsOpenImmersion.lift W.ι s
      (Scheme.range_base_subset_of_closedPoint_mem s hmem)
    have hz := isZero_upperStar_lowerStar_of_disjoint_range C W.ι (i ≫ j) hdisj B
    have htgt := (Functor.map_isZero
      ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber hz).of_iso
        ((upperStarCompUliftSheafFiberIso C W.ι t).app F).symm
    dsimp only [t] at htgt
    rw [IsOpenImmersion.lift_fac] at htgt
    exact ⟨htgt.to_ _, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩

private theorem supportDerivedCounitIsIso (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U)
    [IsClosedImmersion (i ≫ j)]
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).counit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B))) := by
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let R := upperStar (ModuleCat.{u + 1} A) j
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let F := (lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B
  let K := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F
  change IsIso ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app
    (_root_.DerivedCategory.Q.obj K))
  let : CatCommSq (L.mapHomologicalComplex (.up ℤ)) _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (.up ℤ)) _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  have hc : IsIso ((a.mapHomologicalComplex (.up ℤ)).counit.app K) := by
    have hi (n : ℤ) : IsIso (((a.mapHomologicalComplex (.up ℤ)).counit.app K).f n) := by
      rw [Adjunction.mapHomologicalComplex_counit_app_f]
      by_cases hn : n = 0
      · subst n
        have := supportCounitIsIso A j i B
        exact (NatTrans.isIso_app_iff_of_iso a.counit
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F)).2 this
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F n hn
        have hsrc := Functor.map_isZero (R ⋙ L) hz
        exact ⟨hz.to_ _, hsrc.eq_of_src _ _, hz.eq_of_src _ _⟩
    exact HomologicalComplex.Hom.isIso_of_components _
  unfold SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_counit_app]
  infer_instance

private theorem supportRestrictionNormalized (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ U)
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ∃ ρ : (upperStar (ModuleCat.{u + 1} A) j).obj
        ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B) ≅
          (lowerStar (ModuleCat.{u + 1} A) i).obj B,
      ∀ V : U.Etale,
        ∃ τ : (MorphismProperty.Over.pullback @Etale ⊤ i).obj V ≅
            (MorphismProperty.Over.pullback @Etale ⊤ (i ≫ j)).obj
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V),
          τ.hom.left ≫ pullback.fst (V.hom ≫ j) (i ≫ j) = pullback.fst V.hom i ∧
          (((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv.app
              ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)) ≫ ρ.hom).hom.app (op V) =
            B.obj.map τ.hom.op := by
  let e := (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app
    ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)
  refine ⟨e ≪≫ supportRestrictionIso A j i B, ?_⟩
  intro V
  refine ⟨supportPullbackIso j i V, supportPullbackIso_fst j i V, ?_⟩
  have h : e.inv ≫ (e ≪≫ supportRestrictionIso A j i B).hom =
      (supportRestrictionIso A j i B).hom := by
    rw [Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact (congrArg (fun f ↦ f.hom.app (op V)) h).trans
    (supportRestrictionIso_hom_app A j i B V)

private theorem counitDegreeZeroProperties
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (F : D) (G : C) (ρ : R.obj F ≅ G)
    (hc : IsIso ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :
    IsIso (exactCounitComposite a F G ρ) ∧
      ∀ (M : _root_.DerivedCategory D)
      (c : (_root_.DerivedCategory.singleFunctor _ 0).obj F ⟶ M),
      L.mapDerivedCategory.map
          (exactRestrictionLift R F G ρ ≫ R.mapDerivedCategory.map c) ≫
        (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app M =
          exactCounitComposite a F G ρ ≫ c := by
  unfold exactCounitComposite exactRestrictionLift
  let := hc
  refine ⟨inferInstance, ?_⟩
  intro M c
  rw [Functor.map_comp, Category.assoc,
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit_naturality c,
    Category.assoc]

/-- A closed pushforward supported in an open is recovered by the actual open counit,
with its section normalization and naturality for all morphisms in the unbounded
ordinary derived category. This includes targets that are shifted sheaves in any degree.

Source: Stacks, etale-cohomology.tex, Tags 03S3, 03S5 and 095L; derived.tex, Tag 015F
(blueprint: lem-pur-closed-support-open-counit).

Proof plan:
1. By def-weil-pbc-direct-image and lem-weil-pbc-extension-by-zero-adjunction,
restriction evaluates `F` at `V → U → Y`. Since `j` is mono, the two projections
identify `V ×_U Z` with `V ×_Y Z`; applying `B` gives the normalized natural `ρ`.
2. Off the closed image of `i ≫ j`, the fibre product with `Z` is empty. The
empty-cover sheaf axiom makes its sections zero, hence the restriction is zero.
3. The sheaf counit is invertible on geometric stalks: inside `U`, pointed
neighbourhoods factoring through `U` are cofinal, by intersecting with `U`, so its
map is the identity on the same germs. Outside `U`, both stalks vanish, using step 2
and lem-weil-pbc-extension-by-zero-stalks. Apply
lemma-weil-pbc-geometric-stalk-conservative; the inverse is automatically A-linear.
4. The exactness nodes lem-weil-pbc-extension-by-zero-exact and
prop-weil-pbc-inverse-image-modules-exact permit def-weil-exact-derived-adjunction.
Its counit on degree-zero sheaves localizes the original counit. Localization
preserves its inverse and the inverse of `ρ`, so their displayed composite is invertible.
5. For arbitrary derived `c : F → M`, counit naturality says
`Dj_! D(j⁻¹)(c) ≫ ε_M = ε_F ≫ c`. Precompose by `Dj_!(ρ⁻¹)` and use functoriality.
No chain-map representative, boundedness, or resolution assumption on `M` is needed. -/
theorem closedSupport_openCounit (A : Type (u + 1)) [CommRing A]
    {Y U Z : Scheme.{u}} (j : U ⟶ Y) (i : Z ⟶ U)
    [IsOpenImmersion j] [IsClosedImmersion i] [IsClosedImmersion (i ≫ j)]
    (B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ∃ ρ : (upperStar (ModuleCat.{u + 1} A) j).obj
        ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B) ≅
          (lowerStar (ModuleCat.{u + 1} A) i).obj B,
      (∀ V : U.Etale,
        ∃ τ : (MorphismProperty.Over.pullback @Etale ⊤ i).obj V ≅
            (MorphismProperty.Over.pullback @Etale ⊤ (i ≫ j)).obj
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj V),
          τ.hom.left ≫ pullback.fst (V.hom ≫ j) (i ≫ j) = pullback.fst V.hom i ∧
          (((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv.app
              ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)) ≫ ρ.hom).hom.app (op V) =
            B.obj.map τ.hom.op) ∧
      (∀ T : Y.Etale, Disjoint (Set.range T.hom) (Set.range (i ≫ j)) →
        IsZero (((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B).obj.obj (op T))) ∧
      IsIso (closedSupportOpenCounitArrow A j
        ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)
        ((lowerStar (ModuleCat.{u + 1} A) i).obj B) ρ) ∧
      (∀ (M : DerivedCategoryModule A Y)
        (c : (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B) ⟶ M),
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
            (openCounitRestrictionLift A j
              ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)
              ((lowerStar (ModuleCat.{u + 1} A) i).obj B) ρ ≫
              (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map c) ≫
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).counit.app
              M =
          closedSupportOpenCounitArrow A j
            ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)
            ((lowerStar (ModuleCat.{u + 1} A) i).obj B) ρ ≫ c) := by
  obtain ⟨ρ, hρ⟩ := supportRestrictionNormalized A j i B
  have he := counitDegreeZeroProperties
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    ((lowerStar (ModuleCat.{u + 1} A) (i ≫ j)).obj B)
    ((lowerStar (ModuleCat.{u + 1} A) i).obj B) ρ (supportDerivedCounitIsIso A j i B)
  exact ⟨ρ, hρ, supportSectionsZero A (i ≫ j) B, he⟩

end AlgebraicGeometry.Etale
