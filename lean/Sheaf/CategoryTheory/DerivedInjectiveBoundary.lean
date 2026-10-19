/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Normalized connecting maps for a sequence exact on injectives

Source: Stacks Project, Tags 0117, 05TI, 05TH and 070I; Milne,
Lectures on Etale Cohomology, Section 9, Theorem 9.4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe v u w a
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : Type a} [Category.{w} A] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C]

/-- The homology comparison specified by the right derived unit and a representative.
Source: Stacks, Tags 05TI and 05TH. -/
def injectiveHomologyModelIso (F : C ⥤ A) [F.Additive]
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (.up ℤ) q).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj I.obj)) ≅
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).obj K :=
  (DerivedCategory.Plus.homologyFunctorObjQIso (F.mapCochainComplexPlus.obj I) q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj I))) ≪≫
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).mapIso e

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The model comparison respects natural transformations of additive functors.
Source: Stacks, Tags 05TI and 05TH, naturality of the derived unit. -/
@[reassoc]
theorem injectiveHomologyModelIso_natTrans
    {S F : C ⥤ A} [S.Additive] [F.Additive] (τ : S ⟶ F)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I.obj) q ≫
      (injectiveHomologyModelIso F I K e q).hom =
    (injectiveHomologyModelIso S I K e q).hom ≫
      (Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans τ)
        (DerivedCategory.Plus.homologyFunctor A q)).app K := by
  let t : S.mapCochainComplexPlus.obj I ⟶ F.mapCochainComplexPlus.obj I :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I.obj)
  have h₁ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality t q
  have h₂ := Functor.rightDerivedFunctorPlusNatTrans_app τ
    ((HomotopyCategory.Plus.quotient C).obj I)
  have h₃ := (Functor.rightDerivedFunctorPlusNatTrans τ).naturality e.hom
  apply (cancel_epi (DerivedCategory.Plus.homologyFunctorObjQIso
    (S.mapCochainComplexPlus.obj I) q).hom).1
  dsimp [injectiveHomologyModelIso]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h₁]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc]
  erw [← h₂]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((DerivedCategory.Plus.homologyFunctor A q).map) h₃.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem injectiveHomologyModelIso_naturality (F : C ⥤ A) [F.Additive]
    (I L : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (K K' : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj L ≅ K')
    (b : I ⟶ L) (f : K ⟶ K')
    (hf : DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f) (q : ℤ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map b.hom) q ≫
      (injectiveHomologyModelIso F L K' e' q).hom =
    (injectiveHomologyModelIso F I K e q).hom ≫
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).map f := by
  have h₁ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (F.mapCochainComplexPlus.map b) q
  have h₂ := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map b)
  apply (cancel_epi (DerivedCategory.Plus.homologyFunctorObjQIso
    (F.mapCochainComplexPlus.obj I) q).hom).1
  dsimp [injectiveHomologyModelIso]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h₁]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc]
  erw [h₂]
  convert! (congrArg (fun z ↦ (DerivedCategory.Plus.homologyFunctor A q).map
      (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj I)) ≫
        (DerivedCategory.Plus.homologyFunctor A q).map
          (F.rightDerivedFunctorPlus.map z)) hf) using 1 <;>
    simp only [DerivedCategory.Plus.Q, Functor.comp_map, Functor.map_comp, Category.assoc]

variable (S F G : C ⥤ A) [S.Additive] [F.Additive] [G.Additive]
  (ι : S ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)

/-- The row of section complexes associated to a natural three-term sequence.
Source: Stacks, Tag 0117. -/
def injectiveBoundaryRow (I : CochainComplex.Plus C) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex ι (.up ℤ)).app I.obj)
    ((NatTrans.mapHomologicalComplex π (.up ℤ)).app I.obj) (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
      ext n
      simp)

omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in
/-- Termwise exactness on injectives gives a short exact row of complexes.
Source: Stacks, Tag 0117, degreewise criterion. -/
theorem injectiveBoundaryRow_shortExact
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)] :
    (injectiveBoundaryRow S F G ι π w I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact h (I.obj.X n)

/-- A boundary on the derived category agrees with the snake boundary on every
injective representative and every specified identification.
Source: Stacks, Tags 0117, 05TI, 05TH and 070I. -/
def InjectiveBoundaryNormalized
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (δ : ∀ q : ℤ, G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q ⟶
      S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A (q + 1)) : Prop :=
  ∀ (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ),
    (injectiveHomologyModelIso G I K e q).hom ≫ (δ q).app K ≫
      (injectiveHomologyModelIso S I K e (q + 1)).inv =
        (injectiveBoundaryRow_shortExact S F G ι π w h I).δ q (q + 1) rfl

omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in
/-- Exactness transports through a specified commuting triple of isomorphisms.
Source: Stacks, Tag 0117. -/
theorem exact_transport {R : ShortComplex A} (hR : R.Exact)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₁ : R.X₁ ≅ X) (e₂ : R.X₂ ≅ Y) (e₃ : R.X₃ ≅ Z)
    (h₁ : e₁.hom ≫ f = R.f ≫ e₂.hom)
    (h₂ : e₂.hom ≫ g = R.g ≫ e₃.hom) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact := by
  have w : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).1
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, R.zero]
    simp
  exact ⟨w, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂) hR⟩

/-- Normalization alone implies exactness of the three derived arrows.
Source: Stacks, Tag 0117, transported through 05TI and 05TH. -/
theorem injectiveBoundary_exact
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (δ : ∀ q : ℤ, G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q ⟶
      S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A (q + 1))
    (hδ : InjectiveBoundaryNormalized S F G ι π w h δ)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ) :
    let f := (Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans ι)
      (DerivedCategory.Plus.homologyFunctor A q)).app K
    let g := (Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans π)
      (DerivedCategory.Plus.homologyFunctor A q)).app K
    let f' := (Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans ι)
      (DerivedCategory.Plus.homologyFunctor A (q + 1))).app K
    ∃ (w₁ : f ≫ g = 0) (w₂ : g ≫ (δ q).app K = 0)
      (w₃ : (δ q).app K ≫ f' = 0),
      (ShortComplex.mk f g w₁).Exact ∧
      (ShortComplex.mk g ((δ q).app K) w₂).Exact ∧
      (ShortComplex.mk ((δ q).app K) f' w₃).Exact := by
  let H := injectiveBoundaryRow_shortExact S F G ι π w h I
  let eS := injectiveHomologyModelIso S I K e
  let eF := injectiveHomologyModelIso F I K e
  let eG := injectiveHomologyModelIso G I K e
  have hboundary : (eG q).hom ≫ (δ q).app K =
      H.δ q (q + 1) rfl ≫ (eS (q + 1)).hom := by
    rw [← hδ I K e q]
    simp [eS, eG, Category.assoc]
  obtain ⟨w₁, h₁⟩ := exact_transport (H.homology_exact₂ q) _ _
    (eS q) (eF q) (eG q)
    (injectiveHomologyModelIso_natTrans ι I K e q).symm
    (injectiveHomologyModelIso_natTrans π I K e q).symm
  obtain ⟨w₂, h₂⟩ := exact_transport (H.homology_exact₃ q (q + 1) rfl) _ _
    (eF q) (eG q) (eS (q + 1))
    (injectiveHomologyModelIso_natTrans π I K e q).symm hboundary
  obtain ⟨w₃, h₃⟩ := exact_transport (H.homology_exact₁ q (q + 1) rfl) _ _
    (eG q) (eS (q + 1)) (eF (q + 1)) hboundary
    (injectiveHomologyModelIso_natTrans ι I K e (q + 1)).symm
  exact ⟨w₁, w₂, w₃, h₁, h₂, h₃⟩

omit [EnoughInjectives C] in
private theorem exists_model_chainMap
    (I L : CochainComplex.Plus C) [∀ n : ℤ, Injective (L.obj.X n)]
    (K K' : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj L ≅ K')
    (f : K ⟶ K') :
    ∃ b : I ⟶ L, DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f := by
  have : L.obj.IsKInjective := by
    obtain ⟨n, hn⟩ := L.property
    exact CochainComplex.isKInjective_of_injective L.obj n
  obtain ⟨b, hb⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    ((HomotopyCategory.Plus.quotient C).obj I)
    ((HomotopyCategory.Plus.quotient C).obj L)
      (show L.obj.IsKInjective from inferInstance)).2 (e.hom ≫ f ≫ e'.inv)
  obtain ⟨b, rfl⟩ := (HomotopyCategory.Plus.quotient C).map_surjective b
  refine ⟨b, ?_⟩
  change DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map b) ≫
    e'.hom = _
  rw [hb]
  simp

private def modelConnectingMap
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ) :=
  (injectiveHomologyModelIso G I K e q).inv ≫
    (injectiveBoundaryRow_shortExact S F G ι π w h I).δ q (q + 1) rfl ≫
    (injectiveHomologyModelIso S I K e (q + 1)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem modelConnectingMap_naturality
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact)
    (I L : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (K K' : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj L ≅ K')
    (f : K ⟶ K') (q : ℤ) :
    (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).map f ≫
        modelConnectingMap S F G ι π w h L K' e' q =
      modelConnectingMap S F G ι π w h I K e q ≫
        (S.rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor A (q + 1)).map f := by
  obtain ⟨b, hb⟩ := exists_model_chainMap I L K K' e e' f
  let φ : injectiveBoundaryRow S F G ι π w I ⟶
      injectiveBoundaryRow S F G ι π w L :=
    { τ₁ := (S.mapHomologicalComplex (.up ℤ)).map b.hom
      τ₂ := (F.mapHomologicalComplex (.up ℤ)).map b.hom
      τ₃ := (G.mapHomologicalComplex (.up ℤ)).map b.hom
      comm₁₂ := ((NatTrans.mapHomologicalComplex ι (.up ℤ)).naturality b.hom)
      comm₂₃ := ((NatTrans.mapHomologicalComplex π (.up ℤ)).naturality b.hom) }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (injectiveBoundaryRow_shortExact S F G ι π w h I)
    (injectiveBoundaryRow_shortExact S F G ι π w h L) q (q + 1) rfl
  apply (cancel_epi (injectiveHomologyModelIso G I K e q).hom).1
  dsimp only [modelConnectingMap]
  rw [← Category.assoc, ← injectiveHomologyModelIso_naturality G I L K K' e e' b f hb q]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← injectiveHomologyModelIso_naturality S I L K K' e e' b f hb (q + 1)]
  simpa only [φ, Category.assoc] using
    congrArg (fun z ↦ z ≫ (injectiveHomologyModelIso S L K' e' (q + 1)).hom) hδ.symm

/-- Normalized connecting transformations descend from bounded-below injective complexes.

Source: Milne, Section 9, Theorem 9.4, coefficient functoriality; Stacks,
Tags 0117, 070I, 05TI and 05TH.
(blueprint: lem-pur-derived-injective-boundary)

Proof: represent each bounded-below derived object by a bounded-below complex
of injectives. Apply the degreewise short exact row and its snake boundary,
and transport it by the right-derived-unit homology comparisons. A morphism
between two derived objects lifts to a chain map between their injective
representatives by the K-injective Hom bijection. Naturality of the snake
boundary and of the right-derived units gives the naturality square.
Two lifts are homotopic; all three additive functors preserve homotopies,
so their homology maps agree. Changing the representative gives the same
boundary by the same square for the comparison homotopy equivalence. Thus
one obtains natural transformations with the displayed normalization for
all representatives, rather than only the chosen ones. -/
theorem exists_injectiveBoundary
    (h : ∀ (I : C) [Injective I], (ShortComplex.mk (ι.app I) (π.app I)
      (NatTrans.congr_app w I)).ShortExact) :
    ∃ δ : ∀ q : ℤ, G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q ⟶
      S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A (q + 1),
      InjectiveBoundaryNormalized S F G ι π w h δ := by
  classical
  let Q := (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  have model (K : DerivedCategory.Plus C) :
      ∃ I : CochainComplex.Plus C, (∀ n : ℤ, Injective (I.obj.X n)) ∧
        Nonempty (DerivedCategory.Plus.Q.obj I ≅ K) := by
    let M := Q.objPreimage K
    obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
    let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
    exact ⟨I, fun n ↦ inferInstanceAs (Injective (L.obj.X n).obj),
      ⟨Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K⟩⟩
  choose I hI e using model
  let e (K : DerivedCategory.Plus C) := Classical.choice (e K)
  let δ (q : ℤ) :
      G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q ⟶
        S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A (q + 1) :=
    { app := fun K ↦ modelConnectingMap S F G ι π w h (I K) K (e K) q
      naturality := fun {K K'} f ↦
        modelConnectingMap_naturality S F G ι π w h (I K) (I K') K K' (e K) (e K') f q }
  refine ⟨δ, ?_⟩
  intro L hL K eL q
  have heq := modelConnectingMap_naturality S F G ι π w h L (I K)
    K K eL (e K) (𝟙 K) q
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at heq
  change (injectiveHomologyModelIso G L K eL q).hom ≫
    modelConnectingMap S F G ι π w h (I K) K (e K) q ≫
      (injectiveHomologyModelIso S L K eL (q + 1)).inv = _
  rw [heq]
  simp [modelConnectingMap]

end CategoryTheory.Functor
