/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedRefinementModels
public import Sheaf.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-! Canonical clopen refinement construction, mate squares, and shift assembly. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v h w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Ring compositors induced by the fibre-product associator, on every section.
Source: Stacks 03D7, 09A5 (blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalCoefficients (m : Mode) (T : Scheme.{u}) : Coefficients m T where
  directTriangle {U V} f :=
    Functor.sheafPushforwardContinuousComp' (siteTriangle m f).symm
      CommRingCat.{u + 1} (topology m T) (topology m V.left) (topology m U.left)
  sections f R W := by rfl

/-- The clopen pullback shape of a proper refinement.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0F7B
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalShape {T : Scheme.{u}} {X Y Z : Over T} (u : Y ⟶ Z)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) [IsProper u.left]
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left] (h : j₁ ≫ u = j₂) :
    Shape u j₁ j₂ := by
  let V := Over.mk (pullback.fst u.left j₂.left ≫ Y.hom)
  have hs : j₁.left ≫ u.left = j₂.left := congrArg (fun f ↦ f.left) h
  let s := Etale.properOpenSection u.left j₁.left j₂.left hs
  have geom := Etale.properOpenSectionProperties u.left j₁.left j₂.left hs
  let b : V ⟶ Y := Over.homMk (pullback.fst u.left j₂.left)
  let q : V ⟶ X := Over.homMk (pullback.snd u.left j₂.left) (by
    dsimp [V]
    rw [← Over.w j₂, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w u])
  let secMap : X ⟶ V := Over.homMk s (by
    dsimp [V, s, Etale.properOpenSection]
    rw [← Category.assoc, pullback.lift_fst, Over.w j₁])
  refine {
    V := V
    b := b
    q := q
    s := secMap
    pullback := ?_
    schemePullback := IsPullback.of_hasPullback _ _
    retraction := ?_
    openFactor := ?_
    b_open := geom.2.2.2.2.1
    s_open := geom.1
    clopen := geom.2.2.1 }
  · exact IsPullback.of_map (Over.forget T) (by
      ext
      exact pullback.condition)
      (IsPullback.of_hasPullback u.left j₂.left)
  · ext1
    exact geom.2.1
  · ext1
    exact pullback.lift_fst _ _ _

/-- The three geometric factors form a natural transformation before taking mates.
Source: Bhatt--Scholze 6.7.6--6.7.7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def OpenComparisons.hom {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) (R : Rings m T) :
    o.shriek j₂ R ⋙ (o.operation u R).left ⟶ o.shriek j₁ R :=
  (e.beta d.b d.q u j₂ d.pullback R).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
      (o.shriek d.b R) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (p.sectionPull d R).hom (o.shriek d.s R))
      (o.shriek d.b R) ≫
    (p.openFactor d.s d.b j₁ d.openFactor R).hom

/-- The specified refinement is the adjunct of its constructed three factors.
Source: Bhatt--Scholze 6.7.6--6.7.7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def canonicalRefinements {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p) : Refinements e where
  map u j₁ j₂ _ _ _ _ _ h d R :=
    Functor.whiskerLeft (o.shriek j₂ R) (o.operation u R).derivedAdjunction.unit ≫
      Functor.whiskerRight (e.hom d R) (o.operation u R).right
  adjunct u j₁ j₂ _ _ _ _ _ h d R M := by rfl

private theorem mate_square
    {CA DA CB DB : Type*} [Category CA] [Category DA] [Category CB] [Category DB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) {S : CA ⥤ CB} {T : DA ⥤ DB}
    (α : S ⋙ LB ⟶ LA ⋙ T)
    {X : CA} {Y : DA} {X' : CB} {Y' : DB}
    (hA : LA.obj X ⟶ Y) (hB : LB.obj X' ⟶ Y')
    (δX : S.obj X ⟶ X') (δY : T.obj Y ⟶ Y')
    (hc : α.app X ≫ T.map hA ≫ δY = LB.map δX ≫ hB) :
    S.map (aA.homEquiv _ _ hA) ≫
        (mateEquiv aA aB (TwoSquare.mk _ _ _ _ α)).app Y ≫ RB.map δY =
      δX ≫ aB.homEquiv _ _ hB := by
  have ht : LA.map (aA.homEquiv _ _ hA) ≫ aA.counit.app Y = hA :=
    (aA.homEquiv _ _).symm_apply_apply hA
  apply (aB.homEquiv _ _).symm.injective
  rw [← Category.assoc, aB.homEquiv_naturality_right_symm,
    aB.homEquiv_naturality_left_symm, aB.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, mateEquiv_counit]
  change (LB.map (S.map (aA.homEquiv _ _ hA)) ≫
    α.app (RA.obj Y) ≫ T.map (aA.counit.app Y)) ≫ δY = _
  rw [← Category.assoc, ← Functor.comp_map S LB, α.naturality,
    Functor.comp_map]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← T.map_comp, ht]
  exact hc

/-- Coherences before taking proper-adjunction mates. The square is asserted
only for the three explicitly prescribed geometric factors; naturality and the
commuting coefficient square will be consequences, rather than new assumptions.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, steps 3--10
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
structure ElementaryCoherences {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) (ac : ScalarComposition o)
    {p : Spatial o} {e : OpenComparisons p} (r : Refinements e) : Prop where
  h_compatible : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂)
    (d : Shape u j₁ j₂) {A B : Rings m T} (a : A ⟶ B) (M : category c X A),
    (sc.pull u a).hom.app ((o.shriek j₂ A).obj M) ≫
        (o.scalar Y a).T.map (e.h d A M) ≫ (sc.delta j₁ a).hom.app M =
      (o.operation u B).left.map ((sc.delta j₂ a).hom.app M) ≫
        e.h d B ((o.scalar X a).T.obj M)
  coefficient : ∀ {U V : Over T} (f : U ⟶ V) {A B C : Rings m T}
    (a : A ⟶ B) (b : B ⟶ C) (N : category c U A),
    (ac.derived V a b).hom.app ((o.operation f A).right.obj N) ≫
        (sc.chi f (a ≫ b)).app N =
      (o.scalar V b).T.map ((sc.chi f a).app N) ≫
        (sc.chi f b).app ((o.scalar U a).T.obj N) ≫
        (o.operation f C).right.map ((ac.derived U a b).hom.app N)
  open_coefficient : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) (M : category c U A),
    (ac.derived V a b).hom.app ((o.shriek j A).obj M) ≫ (sc.delta j (a ≫ b)).hom.app M =
      (o.scalar V b).T.map ((sc.delta j a).hom.app M) ≫
        (sc.delta j b).hom.app ((o.scalar U a).T.obj M) ≫
        (o.shriek j C).map ((ac.derived U a b).hom.app M)
  coefficient_identity : ∀ {U V : Over T} (f : U ⟶ V) (A : Rings m T)
    (N : category c U A),
    (sc.chi f (𝟙 A)).app N ≫
        (o.operation f A).right.map ((ac.unit U A).hom.app N) =
      (ac.unit V A).hom.app ((o.operation f A).right.obj N)
  open_identity : ∀ {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (A : Rings m T) (M : category c U A),
    (sc.delta j (𝟙 A)).hom.app M ≫ (o.shriek j A).map ((ac.unit U A).hom.app M) =
      (ac.unit V A).hom.app ((o.shriek j A).obj M)
  refinements : ∀ {X Y Z W : Over T} (u : Y ⟶ Z) (v : Z ⟶ W)
    (j₁ : X ⟶ Y) (j₂ : X ⟶ Z) (j₃ : X ⟶ W)
    [IsProper u.left] [IsProper v.left] [IsProper (u ≫ v).left]
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left] [IsOpenImmersion j₃.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] [QuasiCompact j₃.left]
    (h₁ : j₁ ≫ u = j₂) (h₂ : j₂ ≫ v = j₃) (h₃ : j₁ ≫ (u ≫ v) = j₃)
    (d₁ : Shape u j₁ j₂) (d₂ : Shape v j₂ j₃) (d₃ : Shape (u ≫ v) j₁ j₃)
    (R : Rings m T) (M : category c X R),
    (r.map (u ≫ v) j₁ j₃ h₃ d₃ R).app M =
      (r.map v j₂ j₃ h₂ d₂ R).app M ≫
        (o.operation v R).right.map ((r.map u j₁ j₂ h₁ d₁ R).app M) ≫
        (p.pushComp u v R).hom.app ((o.shriek j₁ R).obj M)
  refinement_identity : ∀ {X Y : Over T} (j : X ⟶ Y)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    (h : j ≫ 𝟙 Y = j) (d : Shape (𝟙 Y) j j) (R : Rings m T)
    (M : category c X R),
    (r.map (𝟙 Y) j j h d R).app M =
      (o.operation (𝟙 Y) R).derivedAdjunction.homEquiv _ _
        ((p.pullId Y R).hom.app ((o.shriek j R).obj M))
  spatial_coefficient : ∀ {U V W : Over T} (f : U ⟶ V) (g : V ⟶ W)
    {A B : Rings m T} (a : A ⟶ B) (N : category c U A),
    (o.scalar W a).T.map ((p.pushComp f g A).hom.app N) ≫
        (sc.chi (f ≫ g) a).app N =
      (sc.chi g a).app ((o.operation f A).right.obj N) ≫
        (o.operation g B).right.map ((sc.chi f a).app N) ≫
        (p.pushComp f g B).hom.app ((o.scalar U a).T.obj N)


private theorem successive_eq {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} {e : OpenComparisons p} {r : Refinements e}
    {sc : ScalarComparisons o} {ac : ScalarComposition o}
    (hc : ElementaryCoherences sc ac r) {U V : Over T} (f : U ⟶ V)
    {A B C : Rings m T} (a : A ⟶ B) (b : B ⟶ C) (N : category c U A) :
    successive sc ac f a b N = (sc.chi f (a ≫ b)).app N := by
  dsimp only [successive]
  rw [← hc.coefficient f a b N]
  simp

/-- Passing to proper-adjunction mates gives the coefficient square; the other
formal equations follow from naturality and the balanced coefficient cocycle.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, steps 5--9
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
theorem laws_of_coherences {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} {e : OpenComparisons p} {r : Refinements e}
    {sc : ScalarComparisons o} {ac : ScalarComposition o}
    (hc : ElementaryCoherences sc ac r) : Laws sc ac r := by
  refine {
    square := ?_
    natural := ?_
    coefficient := hc.coefficient
    open_coefficient := hc.open_coefficient
    coefficient_identity := hc.coefficient_identity
    coefficient_square := ?_
    open_identity := hc.open_identity
    refinements := hc.refinements
    refinement_identity := hc.refinement_identity
    spatial_coefficient := hc.spatial_coefficient }
  · intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    ext M
    change (o.scalar Z a).T.map ((r.map u j₁ j₂ h d A).app M) ≫
        (sc.chi u a).app ((o.shriek j₁ A).obj M) ≫
        (o.operation u B).right.map ((sc.delta j₁ a).hom.app M) =
      (sc.delta j₂ a).hom.app M ≫
        (r.map u j₁ j₂ h d B).app ((o.scalar X a).T.obj M)
    rw [← r.adjunct u j₁ j₂ h d A M,
      ← r.adjunct u j₁ j₂ h d B ((o.scalar X a).T.obj M)]
    exact mate_square (o.operation u A).derivedAdjunction
      (o.operation u B).derivedAdjunction (sc.pull u a).hom
      (e.h d A M) (e.h d B ((o.scalar X a).T.obj M))
      ((sc.delta j₂ a).hom.app M) ((sc.delta j₁ a).hom.app M)
      (hc.h_compatible u j₁ j₂ h d a M)
  · intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a M N f
    exact (left sc r u j₁ j₂ h d a).naturality f
  · intro U V f A B C D a b a' b' h N
    rw [successive_eq hc, successive_eq hc]
    generalize a ≫ b = x at h ⊢
    generalize a' ≫ b' = y at h ⊢
    cases h
    simp

private theorem exactShift {C D : Type v} [Category.{h} C] [Category.{h} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    (exactDerivedAdjunction a).CommShift ℤ := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  apply Adjunction.CommShift.mk'
  have he : Functor.whiskerLeft DerivedCategory.Q (exactDerivedAdjunction a).unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (a.mapHomologicalComplex (.up ℤ)).unit DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        G.mapDerivedCategoryFactors.inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id]
    exact Adjunction.localization_unit_app _ _ _ _ _ _ _ X
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (exactDerivedAdjunction a).unit) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
    (fun X ↦ ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩)

private theorem complexIdShift {C : Type v} [Category.{h} C] [Abelian C] :
    NatTrans.CommShift (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_id_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    simp [Functor.mapHomologicalComplexIdIso]

private theorem homotopyIdShift {C : Type v} [Category.{h} C] [Abelian C] :
    NatTrans.CommShift (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom ℤ := by
  have := complexIdShift (C := C)
  have he : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom =
      ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom
        (HomotopyCategory.quotient C (.up ℤ)) ≫
      (Functor.leftUnitor (HomotopyCategory.quotient C (.up ℤ))).hom ≫
      (Functor.rightUnitor (HomotopyCategory.quotient C (.up ℤ))).inv := by
    ext K
    simp only [Functor.comp_obj, Functor.id_obj, Functor.whiskerLeft_app,
      Functor.mapHomotopyCategoryIdIso_hom_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸ inferInstance⟩)

private theorem exactIdShift {C : Type v} [Category.{h} C] [Abelian C]
    [HasDerivedCategory.{w} C] :
    NatTrans.CommShift (Functor.mapDerivedCategoryIdIso C).hom ℤ := by
  have := homotopyIdShift (C := C)
  have he : Functor.whiskerLeft DerivedCategory.Qh
      (Functor.mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom
        DerivedCategory.Qh ≫
      (Functor.leftUnitor DerivedCategory.Qh).hom ≫
      (Functor.rightUnitor DerivedCategory.Qh).inv := by
    have h := congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh (C := C))
    apply (cancel_mono (Functor.rightUnitor DerivedCategory.Qh).hom).1
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh
      (Functor.mapDerivedCategoryIdIso C).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

private theorem eqIsoShift {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] {I : Sort*} (F : I → C ⥤ D)
    [∀ i, (F i).CommShift ℤ] {i j : I} (h : i = j) :
    NatTrans.CommShift (eqToIso (congrArg F h)).hom ℤ := by
  cases h
  change NatTrans.CommShift (𝟙 (F i)) ℤ
  infer_instance

private theorem adjunctShift
    {A C D : Type*} [Category A] [Category C] [Category D]
    [HasShift A ℤ] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {K : A ⥤ C} {H : A ⥤ D}
    [L.CommShift ℤ] [R.CommShift ℤ] [K.CommShift ℤ] [H.CommShift ℤ]
    (a : L ⊣ R) [a.CommShift ℤ] (τ : K ⋙ L ⟶ H) (α : K ⟶ H ⋙ R)
    [NatTrans.CommShift α ℤ]
    (h : ∀ X, a.homEquiv _ _ (τ.app X) = α.app X) :
    NatTrans.CommShift τ ℤ := by
  have he : τ = Functor.whiskerRight α L ≫
      (Functor.associator H R L).hom ≫
      Functor.whiskerLeft H a.counit ≫ (Functor.rightUnitor H).hom := by
    ext X
    have hx := (a.homEquiv _ _).symm_apply_apply (τ.app X)
    rw [h] at hx
    simpa only [Adjunction.homEquiv_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Functor.map_id, Category.id_comp,
      Category.comp_id] using hx.symm
  rw [he]
  infer_instance

private theorem normalizedComparisonShift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {U : F ⥤ D} {Q : E ⥤ C}
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [U.CommShift ℤ] [Q.CommShift ℤ]
    (a : L ⊣ R) (b : L' ⊣ R') [a.CommShift ℤ] [b.CommShift ℤ]
    (d : U ⋙ R ≅ R' ⋙ Q) [NatTrans.CommShift d.hom ℤ]
    (e : L' ⋙ U ≅ Q ⋙ L)
    (h : ∀ M, a.homEquiv _ _ (e.inv.app M) =
      Q.map (b.unit.app M) ≫ d.inv.app (L'.obj M)) :
    NatTrans.CommShift e.hom ℤ := by
  let α : Q ⟶ (L' ⋙ U) ⋙ R :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight b.unit Q ≫
      (Functor.associator L' R' Q).hom ≫
      Functor.whiskerLeft L' d.inv ≫ (Functor.associator L' U R).inv
  have : NatTrans.CommShift d.inv ℤ := NatTrans.CommShift.of_iso_inv d ℤ
  have : NatTrans.CommShift α ℤ := by dsimp only [α]; infer_instance
  have hα : ∀ M, a.homEquiv _ _ (e.inv.app M) = α.app M := by
    intro M
    simpa only [α, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using h M
  have : NatTrans.CommShift e.symm.hom ℤ := adjunctShift a e.inv α hα
  exact NatTrans.CommShift.of_iso_inv e.symm ℤ


private theorem pullCompShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (R : Rings m T) :
    NatTrans.CommShift (p.pullComp f g R).hom ℤ := by
  dsimp only [Spatial.pullComp]
  simp only [Iso.trans_hom, Iso.symm_hom]
  have := NatTrans.CommShift.of_iso_inv
    ((o.operation g R).pullback.mapDerivedCategoryCompIso (o.operation f R).pullback) ℤ
  infer_instance

private theorem pullIdShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) (W : Over T) (R : Rings m T) :
    NatTrans.CommShift (p.pullId W R).hom ℤ := by
  dsimp only [Spatial.pullId]
  simp only [Iso.trans_hom]
  have := exactIdShift (C := Scheme.ProjectionRestriction.Mod ((c.rings W).obj R))
  infer_instance

private theorem openAdjShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (R : Rings m T) : (o.openAdjunction j R).CommShift ℤ := by
  exact exactShift (o.openModel j R).adjunction

private theorem leftUniqShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F F' : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F'.CommShift ℤ]
    [G.CommShift ℤ] (a : F ⊣ G) (b : F' ⊣ G) [a.CommShift ℤ] [b.CommShift ℤ] :
    NatTrans.CommShift (a.leftAdjointUniq b).hom ℤ := by
  have he : (a.leftAdjointUniq b).hom =
      (Functor.leftUnitor F).inv ≫ Functor.whiskerRight b.unit F ≫
      (Functor.associator F' G F).hom ≫ Functor.whiskerLeft F' a.counit ≫
      (Functor.rightUnitor F').hom := by
    ext X
    apply (a.homEquiv X (F'.obj X)).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id]
    simpa only [Adjunction.homEquiv_counit] using
      ((a.homEquiv X (F'.obj X)).apply_symm_apply (b.unit.app X)).symm
  rw [he]
  infer_instance

private theorem ofNatIsoRightShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G G' : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ]
    [G'.CommShift ℤ] (a : F ⊣ G) (e : G ≅ G') [a.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] : (a.ofNatIsoRight e).CommShift ℤ where
  commShift_unit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance
  commShift_counit := by dsimp only [Adjunction.ofNatIsoRight]; infer_instance

private theorem squareShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {V X Y Z : Over T}
    {b : V ⟶ Y} {q : V ⟶ X} {u : Y ⟶ Z} {j : X ⟶ Z}
    (h : b ≫ u = q ≫ j) (R : Rings m T) :
    NatTrans.CommShift (p.square h R).hom ℤ := by
  have := pullCompShift p b u R
  have := pullCompShift p q j R
  have := NatTrans.CommShift.of_iso_inv (p.pullComp q j R) ℤ
  have := eqIsoShift (fun f ↦ (o.operation f R).left) h
  dsimp only [Spatial.square]
  simp only [Iso.trans_hom]
  infer_instance

private theorem sectionShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {X Y Z : Over T} {u : Y ⟶ Z}
    {j₁ : X ⟶ Y} {j₂ : X ⟶ Z} (d : Shape u j₁ j₂) (R : Rings m T) :
    NatTrans.CommShift (p.sectionPull d R).hom ℤ := by
  have := pullCompShift p d.s d.q R
  have := pullIdShift p X R
  have := eqIsoShift (fun f ↦ (o.operation f R).left) d.retraction
  dsimp only [Spatial.sectionPull]
  simp only [Iso.trans_hom]
  infer_instance

private theorem factorShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (p : Spatial o) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] [IsOpenImmersion k.left]
    (h : f ≫ g = k) (R : Rings m T) :
    NatTrans.CommShift (p.openFactor f g k h R).hom ℤ := by
  have := openAdjShift (o := o) f R
  have := openAdjShift (o := o) g R
  have := openAdjShift (o := o) k R
  have := pullCompShift p f g R
  have := eqIsoShift (fun a ↦ (o.operation a R).left) h
  have : NatTrans.CommShift
      (p.pullComp f g R ≪≫ eqToIso (congrArg (fun a ↦ (o.operation a R).left) h)).hom ℤ := by
    simp only [Iso.trans_hom]
    infer_instance
  dsimp only [Spatial.openFactor]
  have := ofNatIsoRightShift
    ((o.openAdjunction f R).comp (o.openAdjunction g R))
    (p.pullComp f g R ≪≫ eqToIso (congrArg (fun a ↦ (o.operation a R).left) h))
  exact leftUniqShift _ _


private theorem betaShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
    (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
    (sq : IsPullback b q u j) (R : Rings m T) :
    NatTrans.CommShift (e.beta b q u j sq R).hom ℤ := by
  have := openAdjShift (o := o) b R
  have := openAdjShift (o := o) j R
  have := squareShift p sq.w R
  exact normalizedComparisonShift (o.openAdjunction b R) (o.openAdjunction j R)
    (p.square sq.w R) (e.beta b q u j sq R) (e.beta_inverse b q u j sq R)

private theorem deltaShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} (sc : ScalarComparisons o)
    [∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B), (o.scalar W a).T.CommShift ℤ]
    (hi : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
      NatTrans.CommShift (sc.pull f a).hom ℤ)
    {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B) :
    NatTrans.CommShift (sc.delta j a).hom ℤ := by
  have := openAdjShift (o := o) j A
  have := openAdjShift (o := o) j B
  have := hi j a
  exact normalizedComparisonShift (o.openAdjunction j B) (o.openAdjunction j A)
    (sc.pull j a) (sc.delta j a) (sc.delta_inverse j a)

private theorem hShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    (hb : ∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
      (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
      (sq : IsPullback b q u j) (R : Rings m T),
      NatTrans.CommShift (e.beta b q u j sq R).hom ℤ)
    (hp : ∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
      (hs : IsClopen (Set.range s.left.base)) (R : Rings m T),
      NatTrans.CommShift (e.pi s hs R) ℤ)
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    (d : Shape u j₁ j₂) (R : Rings m T) :
    NatTrans.CommShift (e.hom d R) ℤ := by
  have := hb d.b d.q u j₂ d.pullback R
  have := hp d.s d.clopen R
  have := sectionShift p d R
  have := factorShift p d.s d.b j₁ d.openFactor R
  have he : e.hom d R =
      (e.beta d.b d.q u j₂ d.pullback R).hom ≫
      Functor.whiskerRight (Functor.rightUnitor (o.operation d.q R).left).inv
        (o.shriek d.b R) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
        (o.shriek d.b R) ≫
      Functor.whiskerRight
        (Functor.associator (o.operation d.q R).left (o.operation d.s R).left
          (o.shriek d.s R)).inv (o.shriek d.b R) ≫
      Functor.whiskerRight
        (Functor.whiskerRight (p.sectionPull d R).hom (o.shriek d.s R))
        (o.shriek d.b R) ≫
      Functor.whiskerRight (Functor.leftUnitor (o.shriek d.s R)).hom (o.shriek d.b R) ≫
      (p.openFactor d.s d.b j₁ d.openFactor R).hom := by
    ext M
    simp [OpenComparisons.hom]
  rw [he]
  infer_instance


/-- The universal cochain scalar pair has its uniquely counit-compatible shifts.
The right Kan extension determines each comparison, including its zero and addition
coherence; no arbitrary triangulated shift structure is chosen.
Source: Stacks 05SU, 06YY
(blueprint: lem-pur-ringed-refinement-formal-assembly). -/
@[instance_reducible] def canonicalScalarShifts {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) :
    ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B), (o.scalar W a).T.CommShift ℤ := by
  intro W A B a
  let d := o.scalar W a
  letI := d.universal
  exact (Functor.rightKanExtension_coherentShift
    (d.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q d.T d.ε
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ)))).choose

/-- The cochain counit commutes with the shifts fixed by its universal property.
Source: Stacks 05SU, 06YY
(blueprint: lem-pur-ringed-refinement-formal-assembly). -/
theorem canonicalScalarCounit {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) (W : Over T) {A B : Rings m T} (a : A ⟶ B) :
    letI := canonicalScalarShifts o
    NatTrans.CommShift (o.scalar W a).ε ℤ := by
  let d := o.scalar W a
  have := d.universal
  exact (Functor.rightKanExtension_coherentShift
    (d.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q d.T d.ε
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ)))).choose_spec

private theorem injectiveUnitShift
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] :
    NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let E := HomotopyCategory.KInjectives.equivalence C
  let ι := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let H := ι ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e := F.rightDerivedFunctorIsoKInjectives
  have : NatTrans.CommShift e.inv ℤ :=
    Functor.CommShift.ofIso_compatibility e.symm ℤ
  have he : Functor.whiskerLeft ι F.rightDerivedFunctorUnit =
      (Functor.leftUnitor H).inv ≫
      Functor.whiskerRight E.unitIso.hom H ≫
      (Functor.associator E.functor E.inverse H).hom ≫
      Functor.whiskerLeft E.functor e.inv ≫
      (Functor.associator ι DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    simp only [e, Functor.rightDerivedFunctorIsoKInjectives, Iso.trans_inv,
      Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, asIso_hom,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id]
    have hn := F.rightDerivedFunctorUnit.naturality (ι.map (E.unitIso.hom.app X))
    dsimp only [H, E, ι] at hn ⊢
    erw [Category.id_comp, Category.comp_id, Category.comp_id]
    change _ = (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (ι.map (E.unitIso.hom.app X)) ≫
      F.rightDerivedFunctorUnit.app (ι.obj (E.inverse.obj (E.functor.obj X))) ≫
      F.rightDerivedFunctor.map (E.counitIso.hom.app (E.functor.obj X))
    erw [← Category.assoc, hn]
    erw [Category.assoc]
    change _ = F.rightDerivedFunctorUnit.app X.obj ≫
      F.rightDerivedFunctor.map (E.functor.map (E.unitIso.hom.app X)) ≫
      F.rightDerivedFunctor.map (E.counitIso.hom.app (E.functor.obj X))
    erw [← F.rightDerivedFunctor.map_comp,
      E.functor_unitIso_comp, F.rightDerivedFunctor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft ι F.rightDerivedFunctorUnit) ℤ := by
    rw [he]
    infer_instance
  apply NatTrans.CommShift.of_whiskerLeft _ ι
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨I, hI, f, hf, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  let := hf
  refine ⟨HomotopyCategory.KInjectives.mk I,
    (HomotopyCategory.quotient C (.up ℤ)).map f, ?_⟩
  change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map f))
  infer_instance


private theorem geometricShift
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (a : F ⊣ G) :
    a.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  have := injectiveUnitShift G
  apply Adjunction.CommShift.mk'
  have he : Functor.whiskerLeft DerivedCategory.Qh
      a.mapDerivedCategoryRightDerivedAdjunction.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (a.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) G.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom := by
    ext X
    have hf := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
      G.rightDerivedFunctorUnit X
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj X) ≫ G.rightDerivedFunctor.map
        (F.mapDerivedCategoryFactorsh.hom.app X) = _ at hf
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id]
    apply (cancel_mono (G.rightDerivedFunctor.map
      (F.mapDerivedCategoryFactorsh.hom.app X))).1
    rw [hf]
    simp only [Category.assoc, ← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
    erw [G.rightDerivedFunctor.map_id, Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh
      a.mapDerivedCategoryRightDerivedAdjunction.unit) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

private theorem retraction_unique {C D : Type*} [Category C] [Category D]
    {P H : C ⥤ D} [H.Full] (ε : P ⟶ H) (r s : H ⟶ P)
    (hr : ε ≫ r = 𝟙 P) (hs : ε ≫ s = 𝟙 P) : r = s := by
  ext X
  have hcomm := (r ≫ ε).naturality (H.preimage ((s ≫ ε).app X))
  simp only [Functor.map_preimage, NatTrans.comp_app] at hcomm
  have hrX := congr_app hr X
  have hsX := congr_app hs X
  simp only [NatTrans.comp_app, NatTrans.id_app] at hrX hsX
  have he : r.app X ≫ ε.app X = s.app X ≫ ε.app X := by
    simpa only [Category.assoc, reassoc_of% hrX, reassoc_of% hsX,
      Category.id_comp, Category.comp_id] using hcomm.symm
  calc
    r.app X = (r.app X ≫ ε.app X) ≫ s.app X := by rw [Category.assoc, hsX]; simp
    _ = (s.app X ≫ ε.app X) ≫ s.app X := by rw [he]
    _ = s.app X := by rw [Category.assoc, hsX]; simp

private theorem retractionShift {C : Type*} [Category C] [HasShift C ℤ]
    {P : C ⥤ C} [P.CommShift ℤ] (ε : P ⟶ 𝟭 C) (r : 𝟭 C ⟶ P)
    [NatTrans.CommShift ε ℤ] (hr : ε ≫ r = 𝟙 P) :
    NatTrans.CommShift r ℤ where
  shift_comm n := by
    let H := shiftFunctor C n
    let d := P.commShiftIso n
    let ε' : H ⋙ P ⟶ H :=
      Functor.whiskerLeft H ε ≫ (Functor.rightUnitor H).hom
    let r₁ : H ⟶ H ⋙ P :=
      (Functor.rightUnitor H).inv ≫ Functor.whiskerLeft H r
    let r₂ : H ⟶ H ⋙ P :=
      (Functor.leftUnitor H).inv ≫ Functor.whiskerRight r H ≫ d.inv
    have h₁ : ε' ≫ r₁ = 𝟙 (H ⋙ P) := by
      ext X
      simpa [ε', r₁] using congr_app hr (H.obj X)
    have h₂ : ε' ≫ r₂ = 𝟙 (H ⋙ P) := by
      have he := NatTrans.shift_comm ε n
      have hh : ε' = d.hom ≫ Functor.whiskerRight ε H ≫
          (Functor.leftUnitor H).hom := by
        ext X
        have hx := congr_app he X
        simpa [ε', H, d] using hx.symm
      rw [hh]
      ext X
      simp only [r₂, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp, NatTrans.id_app]
      have hx := congr_app hr X
      simp only [NatTrans.comp_app, NatTrans.id_app] at hx
      have ht := congrArg (fun k ↦ d.hom.app X ≫ H.map k ≫ d.inv.app X) hx
      dsimp [H, d] at ht ⊢
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app] at ht
      simpa only [CategoryTheory.Functor.map_comp, Functor.comp_obj,
        Category.assoc, Category.id_comp,
        Category.comp_id] using ht
    have h := retraction_unique ε' r₁ r₂ h₁ h₂
    ext X
    have hx := congr_app h X
    have hx' := congrArg (fun f ↦ f ≫ d.hom.app X) hx
    simpa [r₁, r₂, H, d, Category.assoc] using hx'.symm

private theorem coreflectionProjectionShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.CommShift ℤ] [R.CommShift ℤ]
    (a : L ⊣ R) [a.CommShift ℤ] (r : 𝟭 D ⟶ R ⋙ L)
    (hr : ∀ X, R.map (r.app X) = a.unit.app (R.obj X)) :
    NatTrans.CommShift r ℤ := by
  apply retractionShift a.counit r
  ext X
  change a.counit.app X ≫ r.app X = 𝟙 _
  have hn := a.counit.naturality (r.app X)
  simp only [Functor.comp_map, Functor.id_map] at hn
  change L.map (R.map (r.app X)) ≫ a.counit.app _ =
    a.counit.app X ≫ r.app X at hn
  rw [← hn]
  change L.map (R.map (r.app X)) ≫ a.counit.app _ = _
  rw [hr]
  exact a.left_triangle_components _

private theorem piShift {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} (e : OpenComparisons p)
    {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
    (hs : IsClopen (Set.range s.left.base)) (R : Rings m T) :
    NatTrans.CommShift (e.pi s hs R) ℤ := by
  have := openAdjShift (o := o) s R
  exact coreflectionProjectionShift (o.openAdjunction s R) (e.pi s hs R)
    (e.pi_image s hs R)

/-- The inverse-scalar comparison commutes with the shifts fixed by the universal scalar
counit. The clopen projection shift equation follows from its image equation. The open comparisons
and the three-factor map,
then their proper-adjunction mates and coefficient-square composites, follow.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 015F, 07A6
(blueprint: lem-pur-ringed-refinement-formal-assembly). -/
structure ElementaryShifts {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {p : Spatial o} (e : OpenComparisons p) where
  inverse_scalar :
    letI := canonicalScalarShifts o
    ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
      NatTrans.CommShift (sc.pull f a).hom ℤ

/-- Shift compatibility of the constructed refinement follows from its unit
formula. Coefficient mates and both square composites then commute with shifts.
Source: Stacks 015F, 07A6
(blueprint: lem-pur-ringed-refinement-formal-assembly). -/
theorem nonempty_shifts_of_elementary {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    {o : Calculus c} {p : Spatial o} {e : OpenComparisons p}
    {sc : ScalarComparisons o} (sh : ElementaryShifts sc e) :
    Nonempty (Shifts sc (canonicalRefinements e)) := by
  let := canonicalScalarShifts o
  have : ∀ {U V : Over T} (f : U ⟶ V) (R : Rings m T),
      (o.operation f R).derivedAdjunction.CommShift ℤ := by
    intro U V f R
    let := (o.operation f R).kInjectives
    exact geometricShift (o.operation f R).moduleAdjunction
  have : ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
      NatTrans.CommShift (sc.pull f a).hom ℤ := sh.inverse_scalar
  have hdelta {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
      {A B : Rings m T} (a : A ⟶ B) :
      NatTrans.CommShift (sc.delta j a).hom ℤ := deltaShift sc sh.inverse_scalar j a
  have hbeta {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X)
      (u : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion b.left] [IsOpenImmersion j.left]
      (sq : IsPullback b q u j) (R : Rings m T) :
      NatTrans.CommShift (e.beta b q u j sq R).hom ℤ := betaShift e b q u j sq R
  have hhom {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
      [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
      (d : Shape u j₁ j₂) (R : Rings m T) : NatTrans.CommShift (e.hom d R) ℤ :=
    hShift e hbeta (piShift e) d R
  have hchi {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B) :
      NatTrans.CommShift (sc.chi f a) ℤ :=
    NatTrans.CommShift.mateEquiv _ _ (TwoSquare.mk _ _ _ _ (sc.pull f a).hom)
  have href {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
      [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
      [QuasiCompact j₁.left] [QuasiCompact j₂.left] (h : j₁ ≫ u = j₂)
      (d : Shape u j₁ j₂) (R : Rings m T) :
      NatTrans.CommShift ((canonicalRefinements e).map u j₁ j₂ h d R) ℤ := by
    have := hhom d R
    have he : (canonicalRefinements e).map u j₁ j₂ h d R =
        (Functor.rightUnitor (o.shriek j₂ R)).inv ≫
        Functor.whiskerLeft (o.shriek j₂ R) (o.operation u R).derivedAdjunction.unit ≫
        (Functor.associator (o.shriek j₂ R) (o.operation u R).left
          (o.operation u R).right).inv ≫
        Functor.whiskerRight (e.hom d R) (o.operation u R).right := by
      ext M
      simp [canonicalRefinements]
    rw [he]
    infer_instance
  refine ⟨{
    scalar := canonicalScalarShifts o
    scalar_counit := canonicalScalarCounit o
    inverse_scalar := sh.inverse_scalar
    delta := hdelta
    chi := hchi
    beta := hbeta
    pi := piShift e
    refinement := href
    square_left := ?_
    square_right := ?_ }⟩
  · intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    have := href u j₁ j₂ h d A
    have := hchi u a
    have he : left sc (canonicalRefinements e) u j₁ j₂ h d a =
        Functor.whiskerRight ((canonicalRefinements e).map u j₁ j₂ h d A) (o.scalar Z a).T ≫
        (Functor.associator (o.shriek j₁ A) (o.operation u A).right (o.scalar Z a).T).hom ≫
        Functor.whiskerLeft (o.shriek j₁ A) (sc.chi u a) ≫
        (Functor.associator (o.shriek j₁ A) (o.scalar Y a).T (o.operation u B).right).inv ≫
        Functor.whiskerRight (sc.delta j₁ a).hom (o.operation u B).right ≫
        (Functor.associator (o.scalar X a).T (o.shriek j₁ B) (o.operation u B).right).hom := by
      ext M
      simp [left]
    rw [he]
    infer_instance
  · intro X Y Z u j₁ j₂ _ _ _ _ _ h d A B a
    have := href u j₁ j₂ h d B
    dsimp only [right]
    infer_instance

/-- Assemble the package from normalized operations and the pre-mate coherences.
The shape and refinement data are constructed explicitly; neither is chosen from
an existence theorem. Source: Bhatt--Scholze 6.7.6--6.7.7
(blueprint: lem-pur-ringed-refinement-coefficient-square). -/
def assemble {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) (p : Spatial o) (sc : ScalarComparisons o) (ac : ScalarComposition o)
    (e : OpenComparisons p) (hc : ElementaryCoherences sc ac (canonicalRefinements e))
    (sh : Shifts sc (canonicalRefinements e)) : Package m T where
  coefficients := c
  operations := o
  spatial := p
  scalars := sc
  associators := ac
  opens := e
  refinements := canonicalRefinements e
  laws := laws_of_coherences hc
  shifts := sh
  shapes u j₁ j₂ _ _ _ _ _ h := canonicalShape u j₁ j₂ h

end SheafOfModules.RingedRefinement

