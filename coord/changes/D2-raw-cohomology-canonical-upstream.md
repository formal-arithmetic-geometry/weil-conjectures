# AlgebraicGeometry.Etale.higherDirectImageRawDiagram

## Reason

The assigned module was quarantined after the 2026-10-20 sync because its
Sheaf raw-pullback imports and the upstream identity/composition proofs loaded
two definitions with the same fully qualified names. The upstream RawDiagram
already proves every clause and constructs the identical raw groups, additive
maps, functor, diagram and cocone, with no sorry in this module. Re-export these
canonical declarations through the existing Sheaf paths and preserve the DAG
attachments by pointing them at their defining upstream modules.

The raw-pullback comparison chain and the abelian/module comparison imports must
use that same source. The upstream ModuleAbelianCoefficientComparison now owns
moduleAbelianForget and the inverse-image comparisons: these declarations were
moved, not removed. Its public import from the upstream derived comparison
preserves the full old API. The rawTriangleSource construction is re-exported verbatim from its upstream
HigherDirectImageRawTrianglePullbackExtension. The private evaluation-acyclicity API used by import all is retained
with a proof from the upstream theorem; a private alias prevents recursive name
resolution. The CartesianHigherImage consumer imports all from the new defining
module to retain access to its private local-bijectivity proof.

All public hypotheses, conclusions, universes and names are preserved. For
rawTriangleMap the upstream parenthesization is right-associated, whereas the old
Sheaf body grouped the first two factors; Category.assoc identifies these exact
morphisms. There is no new choice of data. No source-library file, target
statement or unit route changes. Semantic review of targets using these imported
definitions is reopened to check this canonical identification.

## Old

### Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1, Nailin Guan, SHEAF group A3
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).
The presheaf is written using derived Hom from the free abelian sheaf of an etale
representable. This is the standard representation of restricted hypercohomology:
Hom(Z[U ×_X Y][0], K[q]) = H^q(U ×_X Y, K|). Its restriction maps are precomposition.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/- The following local comparisons adapt the proved module-coefficient argument in
WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf
(the sections DerivedSections and CohomologyPresheaf) to free abelian sheaves.
The local lifting argument is Stacks 072W/03Q8; it avoids restricting injectives to
individual etale schemes by working directly with derived Hom and local cycles. -/


namespace AbelianComparison

section LocalComparison

variable {C : Type (u + 1)} [Category.{u} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

open Opposite

/-- The free sheaf `ℤ[W]` of abelian groups on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ ℤ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(ℤ[W], F)` is the étale cohomology `H^q(W, F|_W)`. -/
private noncomputable def freeSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] :
    C ⥤ Sheaf J (AddCommGrpCat.{u + 1}) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (AddCommGrpCat.free) ⋙
    presheafToSheaf _ _

/-- Evaluation at the generator: for a sheaf `G` of abelian groups on `X_ét`, the natural map
`Hom(ℤ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `ℤ[W]` given by
the identity of `W`. -/
private noncomputable def freeSheafSections
    (G : Sheaf J (AddCommGrpCat.{u + 1})) :
    (freeSheaf J).op ⋙ preadditiveYoneda.obj G ⟶
      G.obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality J
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (AddCommGrpCat.free)))
    have h₂ := congr_arg (fun k ↦ k.hom (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      ((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((AddCommGrpCat.free).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))) =
        ((AddCommGrpCat.free).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify J
          (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))


/-- The free sheaf `ℤ[W]` corepresents sections over `W`. -/
private noncomputable def freeSheafHomEquiv (W : C)
    (G : Sheaf J (AddCommGrpCat.{u + 1})) :
    ((freeSheaf J).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((AddCommGrpCat.adj).whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

private lemma freeSheafHomEquiv_apply (W : C)
    (G : Sheaf J (AddCommGrpCat.{u + 1}))
    (f : (freeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W G f = (freeSheafSections G).app (op W) f := by
  simp [freeSheafHomEquiv, freeSheafSections]
  rfl

private lemma freeSheafHomEquiv_comp (W : C)
    {G G' : Sheaf J (AddCommGrpCat.{u + 1})}
    (f : (freeSheaf J).obj W ⟶ G) (g : G ⟶ G') :
    freeSheafHomEquiv W G' (f ≫ g) =
      g.hom.app (op W) (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply, freeSheafSections]
  rfl

private lemma freeSheafHomEquiv_map {W W' : C} (v : W' ⟶ W)
    (G : Sheaf J (AddCommGrpCat.{u + 1}))
    (f : (freeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W' G ((freeSheaf J).map v ≫ f) =
      G.obj.map v.op (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply]
  exact congrArg (fun k ↦ k f) ((freeSheafSections G).naturality v.op)



variable [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]

/-- For `L ∈ D⁺(X_ét)`, the map `Hom(ℤ[W][0], L) ⟶ Hom(ℤ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`. -/
private noncomputable def derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1}))) :
    (freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (freeSheaf J).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf J (AddCommGrpCat.{u + 1})) 0).inv.naturality
        ((freeSheaf J).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((freeSheaf J).map g.unop) ≫ f) =
      (freeSheaf J).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((freeSheaf J).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

private lemma derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1})))
    (W : Cᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶ L) :
    (derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β :=
  rfl

/-- The sections map of a morphism of sheaves of abelian groups, on the underlying presheaves of
abelian groups. -/
private noncomputable abbrev sectionsMap {G G' : Sheaf J AddCommGrpCat.{u + 1}}
    (g : G ⟶ G') : G.obj ⟶ G'.obj := g.hom

omit [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] in
private lemma freeSheafSections_naturality
    {G G' : Sheaf J (AddCommGrpCat.{u + 1})} (g : G ⟶ G') :
    freeSheafSections G ≫ sectionsMap g =
      Functor.whiskerLeft (freeSheaf J).op (preadditiveYoneda.map g) ≫
        freeSheafSections G' := by
  ext W f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← freeSheafHomEquiv_apply, ← freeSheafHomEquiv_apply]
  exact (freeSheafHomEquiv_comp W.unop f g).symm


section Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]

variable (M : CochainComplex.Plus (Sheaf J (AddCommGrpCat.{u + 1})))

/-- The comparison `H⁰(M) ⟶ H⁰(Q M)` between the homology sheaf of a complex and the homology of
its image in `D⁺`. -/
private noncomputable def homologyComparison :
    M.obj.homology 0 ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M) :=
  (DerivedCategory.homologyFunctorFactors _ 0).inv.app M.obj ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.quotientCompQhIso _).inv.app M.obj)

private instance homologyComparison_isIso : IsIso (homologyComparison M) := by
  unfold homologyComparison
  infer_instance

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private lemma derivedHomToHomology_app_eq {W : Cᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((freeSheaf J).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ homologyComparison M :=
  DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map
    β f hf

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private theorem exists_chainMap_of_cycle {A : Sheaf J AddCommGrpCat.{u + 1}}
    (c' : A ⟶ M.obj.cycles 0) :
    ∃ fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj,
      DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap fM 0 = c' := by
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  let fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj :=
    HomologicalComplex.mkHomFromSingle (inv τ ≫ c' ≫ M.obj.iCycles 0) (by
      intro k _
      simp)
  refine ⟨fM, ?_⟩
  rw [← cancel_mono (M.obj.iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.mkHomFromSingle_f]
  have hτ : DerivedCategory.singleCyclesHom A ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).obj A).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = τ := by
    simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
  rw [reassoc_of% hτ, IsIso.hom_inv_id_assoc]

private theorem isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective J
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  have : Sheaf.IsLocallySurjective (M.obj.homologyπ 0) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  constructor
  intro W σ
  let σ' : ToType ((M.obj.homology 0).obj.obj (op W)) :=
    (inv (homologyComparison M)).hom.app (op W) σ
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem J (M.obj.homologyπ 0).hom σ')
  rintro V g ⟨c, hc⟩
  let A := (freeSheaf J).obj V
  let c' := (freeSheafHomEquiv V (M.obj.cycles 0)).symm c
  obtain ⟨fM, hfM⟩ := exists_chainMap_of_cycle M c'
  obtain ⟨β, hβ⟩ : ∃ β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      DerivedCategory.Plus.Q.obj M, DerivedCategory.Plus.ι.map β =
        DerivedCategory.Q.map fM ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj :=
    ⟨DerivedCategory.Plus.ι.preimage _, Functor.map_preimage _ _⟩
  refine ⟨β, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    derivedHomToHomology_app_eq M (W := op V) β fM hβ, reassoc_of% hfM,
    ← freeSheafHomEquiv_apply, freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    hc]
  erw [NatTrans.naturality_apply (homologyComparison M).hom g.op σ']
  have hσ : (homologyComparison M).hom.app (op W) σ' = σ := by
    simp only [σ']
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]
    rfl
  rw [hσ]

/-- A map from a single complex whose degree-`0` component factors through the differential
`M⁻¹ ⟶ M⁰` is null-homotopic. -/
private noncomputable def homotopyOfSingle {A : Sheaf J (AddCommGrpCat.{u + 1})}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  (Homotopy.ofEq (HomologicalComplex.from_single_hom_ext (j := 0) (by
    rw [hb, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp)]
    simp
    rfl)) :
      Homotopy f (Homotopy.nullHomotopicMap' (fun i j (_ : j + 1 = i) ↦
        if hi : i = 0 then
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 A i hi).hom ≫ b ≫
            eqToHom (by congr 1; lia)
        else 0))).trans (Homotopy.nullHomotopy' _)

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private theorem derivedMap_zero_of_boundary [M.obj.IsKInjective]
    {A A' : Sheaf J AddCommGrpCat.{u + 1}}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶ DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj)
    (φ : A' ⟶ A) (b : A' ⟶ M.obj.X (-1))
    (hb : ((HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫ b ≫ M.obj.d (-1) 0) :
    (DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β = 0 := by
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hβ' : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β) =
        DerivedCategory.Q.map f' ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj := by
    rw [Functor.map_comp, hf, Functor.map_comp, Category.assoc]
    rfl
  exact DerivedCategory.Plus.eq_zero_of_homotopy _ f' hβ'
    (homotopyOfSingle M f' b hb)

private theorem isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective J
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  constructor
  intro W x y hxy
  let β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M := x - y
  have hβ : (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
      freeSheafSections
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).app W β =
      0 := by
    simp only [β, map_sub]
    exact sub_eq_zero.2 hxy
  have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
    exact sub_eq_zero.symm
  rw [hsieve]
  let A := (freeSheaf J).obj W.unop
  obtain ⟨f, hf⟩ := DerivedCategory.Plus.exists_ι_map_eq M β
  let z := DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0
  have hz : z ≫ M.obj.homologyπ 0 = (0 : A ⟶ M.obj.homology 0) := by
    have hm : IsIso (homologyComparison M) := by
      dsimp only [homologyComparison]
      infer_instance
    have h2 : z ≫ M.obj.homologyπ 0 ≫ homologyComparison M = 0 := by
      apply (freeSheafHomEquiv W.unop
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).injective
      rw [freeSheafHomEquiv_apply, freeSheafHomEquiv_apply, map_zero]
      have := derivedHomToHomology_app_eq M β f hf
      simp only [z, Category.assoc]
      rw [← this]
      exact hβ
    calc z ≫ M.obj.homologyπ 0 =
        (z ≫ M.obj.homologyπ 0 ≫ homologyComparison M) ≫
          inv (homologyComparison M) := by
          simp only [Category.assoc, IsIso.hom_inv_id]; erw [Category.comp_id]
      _ = 0 := by rw [h2, Limits.zero_comp]
  let S := ShortComplex.mk (M.obj.toCycles (-1) 0) (M.obj.homologyπ 0) (by simp)
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S (M.obj.homologyIsCokernel (-1) 0 (by simp))
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  let k' := S.liftCycles z hz
  let k := freeSheafHomEquiv W.unop S.cycles k'
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem J S.toCycles.hom k)
  rintro V g ⟨b, hb⟩
  let φ := (freeSheaf J).map g
  let A' := (freeSheaf J).obj V
  let b' := (freeSheafHomEquiv V (M.obj.X (-1))).symm b
  have hφz : φ ≫ z = b' ≫ M.obj.toCycles (-1) 0 := by
    apply (freeSheafHomEquiv V _).injective
    have hz' : z = k' ≫ S.iCycles := (S.liftCycles_i z hz).symm
    rw [hz', freeSheafHomEquiv_map, freeSheafHomEquiv_comp,
      freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    erw [← NatTrans.naturality_apply S.iCycles.hom g.op k, ← hb,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, S.toCycles_i]
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hf'z : DerivedCategory.singleCyclesHom A' ≫ HomologicalComplex.cyclesMap f' 0 =
      b' ≫ M.obj.toCycles (-1) 0 := by
    rw [HomologicalComplex.cyclesMap_comp, ← Category.assoc,
      DerivedCategory.singleCyclesHom_naturality, Category.assoc]
    exact hφz
  let τ' := DerivedCategory.singleCyclesHom A' ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A').hom
  have hτ' : DerivedCategory.singleCyclesHom A' ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).obj A').iCycles 0 =
        τ' ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').inv := by
    simp [τ', HomologicalComplex.singleObjCyclesSelfIso_hom]
  have hf'0 : f'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫
      (inv τ' ≫ b') ≫ M.obj.d (-1) 0 := by
    have h := hf'z =≫ M.obj.iCycles 0
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.toCycles_i, ← Category.assoc, hτ', Category.assoc] at h
    simp only [Category.assoc]
    rw [← h]
    simp
  have h0 := derivedMap_zero_of_boundary M β f hf φ (inv τ' ≫ b') hf'0
  simp only [Presheaf.equalizerSieve_apply, map_zero, map_sub]
  have h0' : (ConcreteCategory.hom (((freeSheaf J ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (DerivedCategory.Plus.Q.obj M)).map g.op)) (x - y) = 0 := h0
  rw [map_sub] at h0'
  exact h0'

end Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- For every `L ∈ D⁺(X_ét)`, the map `W ↦ (Hom(ℤ[W][0], L) ⟶ Γ(W, H⁰(L)))` is locally
injective and locally surjective: classes of maps to `L` are locally determined by the
section of `H⁰(L)` they induce, and every section of `H⁰(L)` locally comes from such a class. -/
private theorem isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1}))) :
    Presheaf.IsLocallyInjective J
        (derivedHomToHomology L ≫
          freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective J
        (derivedHomToHomology L ≫
          freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) := by
  obtain ⟨n, hn⟩ := L.2
  have : L.IsGE n := (L.isGE_ι_obj_iff n).1 hn
  obtain ⟨L', _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso L n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L'
  have : M.obj.IsKInjective := inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj L'.obj))
  have := isLocallyInjective_derivedHomToHomology M
  have := isLocallySurjective_derivedHomToHomology M
  have hfac : derivedHomToHomology L ≫
      freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) =
    (Functor.isoWhiskerLeft (freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
      (preadditiveYoneda.mapIso e.symm)).hom ≫
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) ≫
      ((sheafToPresheaf _ _).mapIso
        ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso e)).hom := by
    simp only [Category.assoc]
    have hnat := freeSheafSections_naturality
      ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    change _ = _ ≫ _ ≫ freeSheafSections _ ≫
      sectionsMap ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    rw [hnat]
    ext W β
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    apply congrArg (fun f : (freeSheaf J).obj W.unop ⟶
        (DerivedCategory.Plus.homologyFunctor _ 0).obj L ↦
      (freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)).app W f)
    change _ = ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map (β ≫ e.inv)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map e.hom
    rw [derivedHomToHomology_app_apply]
    simp
  rw [hfac]
  constructor <;> infer_instance


private noncomputable def sheafifyIsoOfLocallyBijective
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {G : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : P ⟶ G.obj) [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] :
    (presheafToSheaf J AddCommGrpCat.{u + 1}).obj P ≅ G := by
  let ψ := ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).symm φ
  have hfac : toSheafify J P ≫ ψ.hom = φ := by
    have he := ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv
      _ _).apply_symm_apply φ
    rw [Adjunction.homEquiv_unit] at he
    exact he
  have : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨?_, ?_⟩
    · have : Presheaf.IsLocallyInjective J (toSheafify J P ≫ ψ.hom) := by
        rw [hfac]
        infer_instance
      exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
        J (toSheafify J P) ψ.hom
    · have : Presheaf.IsLocallySurjective J (toSheafify J P ≫ ψ.hom) := by
        rw [hfac]
        infer_instance
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J P) ψ.hom
  exact asIso ψ

private theorem nonempty_sheafifyDerivedHomIso
    (L : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{u + 1})) :
    Nonempty ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      ((freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj L) ≅
        (DerivedCategory.Plus.homologyFunctor _ 0).obj L) := by
  obtain ⟨_, _⟩ := isLocallyBijective_derivedHomToHomology L
  exact ⟨sheafifyIsoOfLocallyBijective (derivedHomToHomology L ≫ freeSheafSections _)⟩

end LocalComparison

private noncomputable def adjunctionPresheafIso
    {B D E : Type*} [Category B] [Category.{u + 1} D] [Category.{u + 1} E]
    [Preadditive D] [Preadditive E] (A : B ⥤ D)
    {F : D ⥤ E} {G : E ⥤ D} [F.Additive] (adj : F ⊣ G) (K : E) :
    (A ⋙ F).op ⋙ preadditiveYoneda.obj K ≅ A.op ⋙ preadditiveYoneda.obj (G.obj K) :=
  NatIso.ofComponents (fun W ↦ (adj.homAddEquiv _ _).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      exact adj.homEquiv_naturality_left _ _)

private noncomputable def higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (freeSheaf X.smallEtaleTopology ⋙ upperStar AddCommGrpCat.{u + 1} h ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

/-- The isomorphism `Hom(h^* ℤ[W][0], K[q]) ≅ Hom(ℤ[W][0], Rh_*(K[q]))`, natural in `W`: the
isomorphism `Lh^*(ℤ[W][0]) ≅ (h^* ℤ[W])[0]` and the adjunction `Lh^* ⊣ Rh_*`. -/
private noncomputable def higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (AddCommGrpCat.{u + 1}))) :
    higherDirectImagePresheaf h q K ≅
      (freeSheaf X.smallEtaleTopology ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((h)_*[AddCommGrpCat.{u + 1}]).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (freeSheaf X.smallEtaleTopology)
    (((h)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  adjunctionPresheafIso
    (freeSheaf X.smallEtaleTopology ⋙ DerivedCategory.Plus.singleFunctor _ 0)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus (K⟦q⟧)

private theorem nonempty_mapIso_trans
    {B D : Type*} [Category* B] [Category* D] (F : B ⥤ D)
    {P Q : B} {G H : D} (e : P ≅ Q) (h : Nonempty (F.obj Q ≅ G)) (e' : G ≅ H) :
    Nonempty (F.obj P ≅ H) := by
  obtain ⟨f⟩ := h
  exact ⟨F.mapIso e ≪≫ f ≪≫ e'⟩

private noncomputable def homologyShiftIso
    {D E : Type*} [Category.{u + 1} D] [Category.{u + 1} E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{u + 1} D] [HasDerivedCategory.{u + 1} E]
    (R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E) [R.CommShift ℤ]
    (q : ℤ) (K : DerivedCategory.Plus D) :
    (DerivedCategory.Plus.homologyFunctor E 0).obj (R.obj (K⟦q⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor E q).obj (R.obj K) :=
  (DerivedCategory.Plus.homologyFunctor E 0).mapIso ((R.commShiftIso q).app K) ≪≫
    ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso q 0 q (add_zero q)).app _

end AbelianComparison


/-- Higher direct image is the sheaf associated to the restricted cohomology presheaf.
Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).

Proof:
1. Derived adjunction identifies the displayed presheaf with
   U ↦ Hom(ℤ[U][0], Rh_*(K[q])). Exact pullback commutes with the single functor.
2. For a bounded below derived object L, choose a K-injective complex M representing L.
   The map Hom(ℤ[U][0], L) → Γ(U, H⁰(L)) is locally bijective. Every section locally
   lifts through the epimorphism from cycles to homology, giving a chain map from
   ℤ[U][0]. If its homology section vanishes, the corresponding cycle locally lifts
   through the differential from degree -1, giving an explicit null homotopy. Naturality
   transports these assertions from M to L. The local-bijection criterion for
   sheafification therefore identifies the associated sheaf with H⁰(L).
3. Apply this to L = Rh_*(K[q]). Shift compatibility of derived direct image identifies
   H⁰(Rh_*(K[q])) with H^q(Rh_*K). For a sheaf specialize to its degree-zero complex. -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj (K⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj K)) := by
  rw [← Functor.assoc
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0)]
  rw [← Functor.assoc uliftYoneda.{u + 1}
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free) ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0)]
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  let R := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h
  have : R.CommShift ℤ := by
    dsimp only [R, rightDerivedLowerStarPlus]
    infer_instance
  exact AbelianComparison.nonempty_mapIso_trans
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (AbelianComparison.higherDirectImagePresheafIso h q K)
    (AbelianComparison.nonempty_sheafifyDerivedHomIso (R.obj (K⟦q⟧)))
    (AbelianComparison.homologyShiftIso R q K)

/-- Higher direct image is the sheaf associated to the restricted cohomology presheaf.
Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).

Proof:
1. Derived adjunction identifies the displayed presheaf with
   U ↦ Hom(ℤ[U][0], Rh_*(K[q])). Exact pullback commutes with the single functor.
2. For a bounded below derived object L, choose a K-injective complex M representing L.
   The map Hom(ℤ[U][0], L) → Γ(U, H⁰(L)) is locally bijective. Every section locally
   lifts through the epimorphism from cycles to homology, giving a chain map from
   ℤ[U][0]. If its homology section vanishes, the corresponding cycle locally lifts
   through the differential from degree -1, giving an explicit null homotopy. Naturality
   transports these assertions from M to L. The local-bijection criterion for
   sheafification therefore identifies the associated sheaf with H⁰(L).
3. Apply this to L = Rh_*(K[q]). Shift compatibility of derived direct image identifies
   H⁰(Rh_*(K[q])) with H^q(Rh_*K). For a sheaf specialize to its degree-zero complex. -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian_single
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj
              (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  exact nonempty_higherDirectImage_iso_sheafification_abelian h q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackComposition

/-! # The raw cohomology diagram

Source: Stacks Project, Tag 09Z1, the canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem five_factor_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T)
    (x y : X ⟶ Y) :
    (a ≫ b) ≫ F.map (x + y) ≫ c ≫ d =
      ((a ≫ b) ≫ F.map x ≫ c ≫ d) + ((a ≫ b) ≫ F.map y ≫ c ≫ d) := by
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem five_factor_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T) :
    (a ≫ b) ≫ F.map (0 : X ⟶ Y) ≫ c ≫ d = 0 := by
  simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit raw pullbacks satisfy identity and composition, independently of any
limit, affineness, or quasi-compactness assumption.
Source: Stacks Project, Tag 09Z1, canonical comparison maps in lemma-relative-colimit.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).

Proof: The derived inverse-image functor is additive, and composition with fixed
morphisms is additive in each argument. Thus the five-factor formula preserves zero
and addition. Expand the five factors defining raw pullback. For an identity morphism, the
identity comparison for inverse image cancels the single-functor comparison and its
inverse. Naturality of the shift comparison cancels its identity factors, leaving the
original derived morphism. For composable arrows, functoriality of derived inverse image
moves the five factors of the first pullback through those of the second. Naturality of
the single-functor comparison cancels the adjacent inverse and direct comparisons.
The associativity coherence of inverse-image composition identifies the resulting
source comparison with that for the composite. Its coefficient comparison is identified
in the same way, using the two equations defining morphisms in Over W. Compatibility of
derived inverse image with shifts identifies the remaining shift comparison. Thus the
five surviving factors are exactly those of the composite raw pullback. -/
theorem higherDirectImageRawOverPullback_functorial
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (∀ (A B : Over W) (f : A ⟶ B),
      higherDirectImageRawOverPullback Λ k G q f U 0 = 0) ∧
    (∀ (A B : Over W) (f : A ⟶ B)
      (x y : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q f U (x + y) =
        higherDirectImageRawOverPullback Λ k G q f U x +
          higherDirectImageRawOverPullback Λ k G q f U y) ∧
    (∀ (A : Over W)
      (z : (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (𝟙 A) U z = z) ∧
    (∀ (A B C : Over W) (f : A ⟶ B) (g : B ⟶ C)
      (z : (higherDirectImageRawOverPresheaf Λ k G q C).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (f ≫ g) U z =
        higherDirectImageRawOverPullback Λ k G q f U
          (higherDirectImageRawOverPullback Λ k G q g U z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B f
    exact five_factor_zero D+((f.left)^*[ModuleCat.{u + 1} Λ]) _ _ _ _
  · intro A B f x y
    exact five_factor_add D+((f.left)^*[ModuleCat.{u + 1} Λ]) _ _ _ _ x y
  · intro A z
    exact higherDirectImageRawOverPullback_id Λ k G q A U z
  · intro A B C f g z
    exact higherDirectImageRawOverPullback_comp Λ k G q f g U z

/-- The additive map on raw cohomology; its data are the explicit five-factor formula. -/
noncomputable def higherDirectImageRawOverPullbackHom
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U) ⟶
      (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  ConcreteCategory.ofHom (C := AddCommGrpCat)
    { toFun := higherDirectImageRawOverPullback Λ k G q f U
      map_zero' := (higherDirectImageRawOverPullback_functorial Λ k G q U).1 A B f
      map_add' := (higherDirectImageRawOverPullback_functorial Λ k G q U).2.1 A B f }

/-- The bundled additive map is exactly the prescribed raw pullback. -/
theorem higherDirectImageRawOverPullbackHom_apply
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    higherDirectImageRawOverPullbackHom Λ k G q f U z =
      higherDirectImageRawOverPullback Λ k G q f U z := rfl

/-- The contravariant raw cohomology functor on Over W. No data are chosen from an
existence theorem: objects and maps are the fixed raw presheaves and explicit pullbacks. -/
noncomputable def higherDirectImageRawOverFunctor
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A := (higherDirectImageRawOverPresheaf Λ k G q A.unop).obj (op U)
  map f := higherDirectImageRawOverPullbackHom Λ k G q f.unop U
  map_id A := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (𝟙 A.unop) U z = z
    rw [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.1 A.unop z
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (g.unop ≫ f.unop) U z =
      higherDirectImageRawOverPullbackHom Λ k G q g.unop U
        (higherDirectImageRawOverPullbackHom Λ k G q f.unop U z)
    simp only [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.2
      _ _ _ g.unop f.unop z

/-- The raw cohomology diagram of an inverse system. -/
noncomputable abbrev higherDirectImageRawDiagram
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (U : S.Etale) :=
  D.op ⋙ higherDirectImageRawOverFunctor Λ k G q U

/-- The raw cohomology cocone of a scheme cone, before any assertion of continuity. -/
noncomputable def higherDirectImageRawCocone
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cocone (higherDirectImageRawDiagram Λ k G q D U) :=
  (higherDirectImageRawOverFunctor Λ k G q U).mapCocone c.op

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverCoefficient
public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf
import Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOverMapCoefficient

/-! # Raw cohomology pullback and the higher-image comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

/-- Raw cohomology with coefficients restricted from W. -/
noncomputable abbrev higherDirectImageRawOverPresheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :=
  higherDirectImagePresheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

/-- The canonical raw comparison, with its underlying abelian target made explicit. -/
noncomputable abbrev higherDirectImageRawOverComparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :
    higherDirectImageRawOverPresheaf Λ k G q B ⟶
      (higherDirectImage Λ (B.hom ≫ k) q
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  higherDirectImagePresheafToSheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

/-- Pullback of a raw cohomology class for coefficients restricted from W.
The factors are pullback composition, the single-functor comparison, pullback
of the class, shift comparison, and the canonical coefficient identification.
Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps. -/
@[implicit_reducible]
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  higherDirectImageRawTrianglePullback Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) q _ _
    (higherDirectImageRawOverCoefficient Λ G f) U z

attribute [local irreducible] lowerStarPlusTransition higherDirectImagePresheafToHom

private theorem evaluation_postcomp
    (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}} (U : S.Etale)
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β : (freeSheaf Λ S).obj U ⟶ F) (m : F ⟶ G) :
    (freeSheafSections Λ G).app (op U) (β ≫ m) =
      m.hom.app (op U) ((freeSheafSections Λ F).app (op U) β) := by
  have h := freeSheafSections_naturality (Λ := Λ) m
  exact (congrArg (fun n ↦ n.app (op U) β) h).symm

/-- The comparison component of raw pullback with the higher direct image map.
Source: Stacks Project, Tags 03Q8 and 09Z1; canonical derived-Hom comparison.
(blueprint: sbc-lem-higher-image-raw-over-comparison).
The proof expands the adjunction comparison, applies the triangle identity,
and identifies the resulting shifted homology map with the canonical transition.
-/
theorem higherDirectImageRawOverPullback_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) := by
  rw [← higherDirectImageOverMap_coefficient Λ k G q f]
  change (freeSheafSections Λ _).app (op U)
      ((higherDirectImagePresheafToHom Λ (A.hom ≫ k) q _).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z)) = _
  exact (congrArg ((freeSheafSections Λ _).app (op U))
    (higherDirectImageRawTransition_toHom Λ f.left
      (B.hom ≫ k) (A.hom ≫ k) (by rw [← Category.assoc, Over.w]) q _ _
      (higherDirectImageRawOverCoefficient Λ G f) U z)).trans
    (evaluation_postcomp Λ U _ _)

/-- Restriction component of raw pullback naturality.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-restriction).
The proof is the naturality of the pullback composition and single-complex
comparison maps under restriction of the étale test object.
-/
theorem higherDirectImageRawOverPullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U))
    (T : S.Etale) (a : T ⟶ U) :
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z) := by
  unfold higherDirectImageRawOverPullback
  apply higherDirectImageRawTrianglePullback_restriction

/-- Raw pullback intertwines the fixed cohomology-presheaf comparison with the
canonical higher-image transition. This requires no limit or qcqs assumptions.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).

Proof: Expand the raw class comparison as derived adjunction followed by degree-zero
homology and evaluation at the identity generator of the free module sheaf of U.
Expand the transition as unit, pullback composition, and counit. Naturality of the
unit moves the class through pullback, and the triangle identity cancels the
counit against the unit in its adjoint image. The pullback composition comparison
on single complexes then gives the first two factors of the raw pullback. Shift
compatibility gives its fourth factor; the last factor is the shifted coefficient
identification. Naturality of homology and evaluation proves the equality.
For restriction along a : T -> U, use naturality of the pullback composition
and single-functor isomorphisms in the free sheaf of U. Functoriality moves its
precomposition through pullback; associativity gives the second equality.
The comparisons are the fixed constructions, not arbitrarily chosen isomorphisms. -/
theorem higherDirectImageRawOverPullback_toSheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) ∧
    ∀ (T : S.Etale) (a : T ⟶ U),
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z)  := by
  exact ⟨higherDirectImageRawOverPullback_comparison Λ k G q f U z,
    fun T a => higherDirectImageRawOverPullback_restriction Λ k G q f U z T a⟩

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
import Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-! # Raw pullback and the derived-Hom comparison

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Pullback of raw classes commutes with the comparison to morphisms from the free sheaf,
before evaluating those morphisms on sections, with a specified coefficient morphism.
Source: Stacks Project, Tags 03Q8 and 09Z1, canonical cohomology comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).

Proof: Write the comparison as the derived adjunction on the class, preceded by the
single-complex comparison, followed by degree-zero homology and the homology shift
comparison. Write the derived transition as the unit for h', pullback composition,
and pullback of the counit for h. Naturality of the unit and the adjunction triangle
identity show that composing the adjunct of z with this transition is the adjunct
of the pulled-back class. Compatibility of pullback composition with the single
complexes identifies its source map with the first two displayed factors. The shift
compatibility of the unit, counit, and pullback composition transports the shift
comparison past this identity, giving the fourth factor. Apply degree-zero homology,
use naturality of the identification H^0(L[q]) = H^q(L), and precompose with the inverse
single-complex homology comparison. This gives the stated equality of morphisms from
the free sheaf, without evaluation. Finally use naturality in the coefficient morphism v to
postcompose on raw classes by v[q] and on higher images by H^q(Rh'_*v).
The argument works for every integer q, every bounded-below K, and every commutative
triangle, including identity arrows and zero objects; it uses no qcqs hypotheses. -/
theorem higherDirectImageRawTransition_toHom
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K')
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U)
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U z) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) z ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (lowerStarPlusTransition Λ a h h' w K ≫
            R+((h')_*[ModuleCat.{u + 1} Λ]).map v) := by
  have H := higherDirectImageRawTransition_toHom_core Λ a h h' w q K K' v U
  have Hz := congrArg (fun f => f z) H
  exact Hz

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore

```lean
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

import Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionHomologyShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
private theorem map_factor
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {W X Y : C} {T Z Z' : D}
    (ε : T ⟶ H.obj W) (z : W ⟶ X) (z' : W ⟶ Y) (t : X ⟶ Y)
    (hz : z' = z ≫ t) (c : H.obj X ⟶ Z) (c' : H.obj Y ⟶ Z') (s : Z ⟶ Z')
    (hc : H.map t ≫ c' = c ≫ s) :
    ε ≫ H.map z' ≫ c' = (ε ≫ H.map z ≫ c) ≫ s := by
  rw [hz, H.map_comp]
  simp only [Category.assoc]
  rw [hc]

-- Construct this standard theorem application explicitly; Lean's kernel checks it.
private meta def toEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- Adapt the kernel-checked congruence method of HigherDirectImageTransitionCoreComposition.
-- Build congruence proofs before reducing the large derived-category objects.
private meta def congrProofs
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := a.consumeMData
      let b := b.consumeMData
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' => e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← congrProofs cache pairs n type type'
          let htype ← toEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← congrProofs cache (pairs.push (x, y, hxy)) n
                  (body.instantiate1 x) (body'.instantiate1 y)
                let h ← Lean.Meta.mkLambdaFVars #[x, y, hxy] h
                Lean.Meta.mkAppM ``Function.hfunext #[htype, h]
      let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let fn := e.getAppFn
        let .proj typeName index major := fn | return e
        let info := Lean.getStructureInfo (← Lean.getEnv) typeName
        let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
        return Lean.mkAppN p e.getAppArgs
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if af.isConstOf ``CategoryTheory.Preadditive.mk &&
          bf.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Preadditive.mk &&
          af.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if af.isConstOf ``CategoryTheory.Functor.mk &&
          bf.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Functor.mk &&
          af.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if af != bf || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a b'
        let reduceProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          if e''.getAppFn.isProj then
            let .proj typeName index major := e''.getAppFn | return none
            let info := Lean.getStructureInfo (← Lean.getEnv) typeName
            let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
            let e''' := Lean.mkAppN p e''.getAppArgs
            if e''' == e then return none
          return some e''
        if ← isProjection af then
          if let some a' ← reduceProjection a then
            return ← congrProofs cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← congrProofs cache pairs n a b'
        throwError "different congruence heads: {a} versus {b}"
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor := args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      let mut first := 0
      while first < aa.size && aa[first]! == ba[first]! do
        first := first + 1
      let f := Lean.mkAppN af (aa.extract 0 first)
      let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
      let mut args := #[]
      for i in [first:aa.size] do
        let h ← congrProofs cache pairs n aa[i]! ba[i]!
        let h ← if ct.argKinds[i - first]! == .eq then
          toEq h else pure h
        args := args.push aa[i]! |>.push ba[i]! |>.push h
      return Lean.mkAppN ct.proof args
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private meta def structuralExact (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target := (← Lean.Meta.whnf (← goal.getType)).consumeMData
    let some (_, lhs, rhs) := target.eq? | throwError "expected equality: {target}"
    let proofType ← Lean.Meta.whnf (← Lean.Meta.inferType proof)
    let some (_, lhs', rhs') := proofType.consumeMData.eq?
      | throwError "expected equality proof: {proofType}"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let hl ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 lhs lhs')
    let hr ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 rhs' rhs)
    let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
    let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
    goal.assign (← toEq hh)

set_option backward.isDefEq.respectTransparency true

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStarPlusComp upperStarComp
  Functor.mapDerivedCategoryPlusSingleFunctor lowerStarPlusTransition
  higherDirectImagePresheafToHom Adjunction.homEquiv Adjunction.derivedPlus
  derivedUpperStarLowerStarAdjunctionPlus

private theorem transitionThrough_eq
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.transitionThrough
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
      D+((a)^*[ModuleCat.{u + 1} Λ])
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom K K' v =
    lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v := by
  simp only [Adjunction.transitionThrough, lowerStarPlusTransition,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus, eqToIso_refl, Iso.refl_trans]
  erw [Functor.map_comp, Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The morphism-level coherence underlying the raw pullback comparison.  It is obtained by
expanding the derived adjunction comparison, the transition map, and the shift comparison;
naturality of the adjunction unit and the triangle identity identify the two composites.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom-core).
-/
theorem higherDirectImageRawTransition_toHom_core
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U) ∘
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) ≫
        (Functor.whiskerLeft (freeSheaf Λ S).op (preadditiveYoneda.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (lowerStarPlusTransition Λ a h h' w K ≫
              R+((h')_*[ModuleCat.{u + 1} Λ]).map v)))).app (op U) := by
  set_option backward.isDefEq.respectTransparency true in
    subst h'
    ext z
    have hd := higherDirectImageRawTrianglePullback_adjunct Λ a h q K K' v U z
    rw [transitionThrough_eq] at hd
    have ht := higherDirectImageTransition_homologyShift Λ a h q K K' v
    have hf := map_factor
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0)
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((freeSheaf Λ S).obj U)) _ _ _ hd _ _ _ ht
    have eh := higherDirectImagePresheafToHom_app_apply Λ h q K (op U) z
    have eh' := higherDirectImagePresheafToHom_app_apply Λ (a ≫ h) q K' (op U)
      (higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z)
    change (higherDirectImagePresheafToHom Λ (a ≫ h) q K').app (op U)
        (higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) z ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).map
          (lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫
            R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map v)
    rw [eh', eh]
    dsimp only [homologyShiftComparison, moduleDerivedAdjunction, moduleUpperStar,
      moduleLowerStar]
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        structuralExact (← Lean.Meta.getLocalDeclFromUserName `hf).toExpr

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct

```lean
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

import WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
public import WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem invert_square
    {C : Type*} [Category C] {W X Y Z V : C}
    (d : W ≅ X) (b : Y ≅ Z) (c : Z ≅ V) (p : X ⟶ Y) (s : W ⟶ V)
    (h : p ≫ b.hom ≫ c.hom = d.inv ≫ s) :
    s ≫ c.inv ≫ b.inv = d.hom ≫ p := by
  rw [← cancel_epi d.inv]
  simp only [Iso.inv_hom_id_assoc, ← reassoc_of% h,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem invert_square_map
    {C D : Type*} [Category C] [Category D] (P : D ⥤ C)
    {W Z V K' : C} {A B K : D}
    (d : W ≅ P.obj A) (b : P.obj B ≅ Z) (c : Z ≅ V)
    (f : A ⟶ B) (s : W ⟶ V)
    (h : P.map f ≫ b.hom ≫ c.hom = d.inv ≫ s)
    (z : B ⟶ K) (t : P.obj K ⟶ K') :
    s ≫ c.inv ≫ b.inv ≫ P.map z ≫ t = d.hom ≫ P.map (f ≫ z) ≫ t := by
  have hc := invert_square d b c (P.map f) s h
  rw [P.map_comp]
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ P.map z ≫ t) hc

private theorem adjunct_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    {X : C} {K : D} {K' : E} (f : L.obj X ⟶ K) (t : P.obj K ⟶ K') :
    adj'.homEquiv _ _ (θ.app X ≫ P.map f ≫ t) =
      adj.homEquiv _ _ f ≫ adj.transitionThrough adj' P θ K K' t := by
  have ht : adj.transitionThrough adj' P θ K K' t =
      adj'.homEquiv _ _ (θ.app (R.obj K) ≫ P.map (adj.counit.app K) ≫ t) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [ht, ← (adj'.homEquiv _ _).symm.injective.eq_iff,
    Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  rw [reassoc_of% (θ.naturality (adj.homEquiv _ _ f))]
  rw [← Functor.map_comp_assoc]
  have hc := (adj.homEquiv X K).symm_apply_apply f
  change L.map (adj.homEquiv X K f) ≫ adj.counit.app K = f at hc
  rw [hc]

/-- Passing raw triangle pullback through the derived adjunction gives the mate
of the pullback-composition comparison at the shifted coefficient objects.

Proof: invert the pullback/single-functor comparison from upperStarPlusComp_single
and compose it with the raw pullback formula. Naturality of the left-adjoint
comparison moves an adjunct through this composite. Applying the inverse
adjunction equivalence reduces the equality to naturality and the counit identity.
This calculation precedes applying any homology functor, so it is only the
adjunction part of the raw-transition/toHom comparison.
Source: Stacks Project Tags 03Q8 and 09Z1; upperStarPlusComp_single and Mathlib
Adjunction.homEquiv_naturality_left_symm.
(blueprint: sbc-lem-module-raw-triangle-adjunct). -/
theorem higherDirectImageRawTrianglePullback_adjunct
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).homEquiv _ _
      (((((a ≫ h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫
        higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
      (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫ z) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.transitionThrough
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
        D+((a)^*[ModuleCat.{u + 1} Λ])
        (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom (K⟦q⟧) (K'⟦q⟧)
        ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map v)  := by
  have hraw :
      ((((a ≫ h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫
        higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z =
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf Λ S).obj U)) ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            ((freeSheaf Λ S).obj U)) ≫ z) ≫
        ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map v) := by
    unfold higherDirectImageRawTrianglePullback rawTriangleMap rawTriangleSource
    simp only [Category.assoc]
    have hc := upperStarPlusComp_single Λ a h ((freeSheaf Λ S).obj U)
    exact invert_square_map D+((a)^*[ModuleCat.{u + 1} Λ])
      ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf Λ S).obj U)))
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U)))
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((upperStarComp (ModuleCat.{u + 1} Λ) a h (a ≫ h) rfl).app
          ((freeSheaf Λ S).obj U)).symm)
      _ _ hc z _
  rw [hraw]
  simpa only [derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus] using
    adjunct_transition
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h)
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h))
      D+((a)^*[ModuleCat.{u + 1} Λ])
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom
      (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        ((freeSheaf Λ S).obj U)) ≫ z)
      ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
        (shiftFunctor _ q).map v)

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-! # Raw pullback for a commutative triangle

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The two source factors of the raw triangle map, kept as one morphism.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction). -/
def rawTriangleSource
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C) :
    B.obj (H'.obj U) ⟶ F.obj (A.obj (H.obj U)) :=
  B.map (c.app U) ≫ e.app (H.obj U)

/-- The map on represented classes obtained from two comparison natural transformations
and a fixed coefficient morphism. This is the categorical formula for raw triangle pullback;
its factors are the comparisons used in Stacks Project, Tags 03Q8 and 09Z1. -/
def rawTriangleMap
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').obj (op U) :=
  rawTriangleSource H H' P A B F c e U ≫ F.map z ≫ s

/-- Pullback of a derived class, followed by a specified coefficient morphism. The
coefficient morphism is given data, and no witness is chosen from an existence theorem. -/
noncomputable def higherDirectImageRawTrianglePullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h' q K').obj (op U) :=
  rawTriangleMap
    ((freeSheaf Λ S) ⋙ (h)^*[ModuleCat.{u + 1} Λ])
    ((freeSheaf Λ S) ⋙ (h')^*[ModuleCat.{u + 1} Λ])
    ((a)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (Functor.whiskerLeft (freeSheaf Λ S)
      (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv
    U z ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v)

private theorem trianglePullback_naturality
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    {U T : C} (b : T ⟶ U) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    rawTriangleMap H H' P A B F c e T
      (((H ⋙ A).op ⋙ preadditiveYoneda.obj K).map b.op z) s =
      ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').map b.op
        (rawTriangleMap H H' P A B F c e U z s) := by
  unfold rawTriangleMap rawTriangleSource
  simp only [Category.assoc]
  change B.map (c.app T) ≫ e.app (H.obj T) ≫
    F.map (A.map (H.map b) ≫ z) ≫ s =
      B.map (H'.map b) ≫ B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s
  have hc := congrArg B.map (c.naturality b)
  have hs := e.naturality (H.map b)
  simp only [Functor.comp_map, Functor.map_comp] at hc hs
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hs, ← reassoc_of% hc]

set_option backward.isDefEq.respectTransparency true in
/-- Restriction naturality of the raw pullback.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
Proof: Naturality of restriction through each displayed pullback factor, followed by
functoriality and associativity. -/
theorem higherDirectImageRawTrianglePullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K')
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U))
    (T : S.Etale) (b : T ⟶ U) :
    higherDirectImageRawTrianglePullback Λ a h h' w q K K' v T
        ((higherDirectImagePresheaf Λ h q K).map b.op z) =
      (higherDirectImagePresheaf Λ h' q K').map b.op
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U z):= by
  unfold higherDirectImageRawTrianglePullback
  exact trianglePullback_naturality
    ((freeSheaf Λ S) ⋙ (h)^*[ModuleCat.{u + 1} Λ])
    ((freeSheaf Λ S) ⋙ (h')^*[ModuleCat.{u + 1} Λ])
    ((a)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (Functor.whiskerLeft (freeSheaf Λ S)
      (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv
    b z ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v)

end AlgebraicGeometry.Etale
```

### Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-! # Canonical derived direct image comparison for module coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The existing coefficientwise forgetful sheaf functor, abbreviated for comparisons. -/
abbrev moduleAbelianForget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance moduleAbelianForget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (moduleAbelianForget Λ X).Additive where
  map_add := by intro F G α β; ext W; rfl

instance moduleAbelianForget_preservesFiniteLimits
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (moduleAbelianForget Λ X) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.IsRightAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsRightAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom Λ)).isRightAdjoint
    infer_instance
  have : (moduleAbelianForget Λ X).IsRightAdjoint := by
    change (sheafCompose X.smallEtaleTopology U).IsRightAdjoint
    infer_instance
  infer_instance

instance moduleAbelianForget_preservesFiniteColimits
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (moduleAbelianForget Λ X) := by
  have : (moduleAbelianForget Λ X).IsLeftAdjoint :=
    Scheme.moduleSheafForgetIsLeftAdjoint X Λ
  infer_instance

/-- Direct image commutes definitionally with forgetting coefficients. -/
noncomputable def moduleAbelianLowerStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)_*[ModuleCat.{u + 1} Λ] ⋙ moduleAbelianForget Λ Y ≅
      moduleAbelianForget Λ X ⋙ (f)_*[AddCommGrpCat.{u + 1}] := Iso.refl _

/-- The canonical comparison determined by the units of right derived direct image. -/
noncomputable def moduleAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙ D+(moduleAbelianForget Λ Y) ⟶
      D+(moduleAbelianForget Λ X) ⋙ R+((f)_*[AddCommGrpCat.{u + 1}]) :=
  Functor.rightDerivedFunctorPlusBaseChange (moduleAbelianLowerStarIso Λ f).hom

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9. -/
private theorem moduleAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  obtain ⟨e, ⟨eAb⟩⟩ := moduleSheaf_constantRing_equivalence Λ X
  let O := (sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
  let I : SheafOfModules.{u + 1} O := e.functor.obj G
  have : Injective I := (e.map_injective_iff G).mpr inferInstance
  have htop : X.smallEtaleTopology.toPrecoverage.toGrothendieck =
      X.smallEtaleTopology := by
    apply le_antisymm
    · exact X.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
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
        (n + 1)).mapIso (eAb.app G).symm)

/-- The canonical derived direct-image coefficient comparison is invertible.

Source: Stacks Project, Tag 03FD, second paragraph of its proof, and Tag 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)

Proof: Identify a ModuleCat-valued sheaf with a module over the constant ring
sheaf, preserving its underlying abelian sheaf and injectivity. Tag 03FD gives
vanishing of positive abelian derived evaluation on every etale object for an
injective module sheaf I. By Tag 072W, the higher direct images of I_ab are the
sheafifications of V ↦ H^n(X ×_Y V, I_ab). Each value vanishes for n > 0, so
I_ab is acyclic for f_* on abelian sheaves. The coefficient forgetful sheaf
functors are exact, and f_* commutes with them by evaluation. Apply
Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic to this square.
Its hypothesis is precisely the preceding acyclicity. This proves invertibility
of the canonical unit-compatible comparison on all bounded below complexes,
without asserting that the underlying abelian sheaf of I is injective. -/
theorem isIso_moduleAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (moduleAbelianDerivedLowerStarComparison Λ f) := by
  apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (moduleAbelianLowerStarIso Λ f)
  intro I hI n
  let G := (moduleAbelianForget Λ X).obj I
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
    exact moduleAbelianForget_injective_evaluation_acyclic Λ X I _ n
  have hH := hz.of_iso c.symm
  exact hH.of_iso
    ((((f)_*[AddCommGrpCat.{u + 1}]).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      (n + 1)).app G).symm

attribute [instance] isIso_moduleAbelianDerivedLowerStarComparison

/-- Inverse-image comparison adjoint to the forgotten module adjunction unit. -/
noncomputable def moduleAbelianUpperStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    moduleAbelianForget Λ Y ⋙ (g)^*[AddCommGrpCat.{u + 1}] ⟶
      (g)^*[ModuleCat.{u + 1} Λ] ⋙ moduleAbelianForget Λ X where
  app J := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
    ((moduleAbelianForget Λ Y).obj J)
    ((moduleAbelianForget Λ X).obj ((g)^*[ModuleCat.{u + 1} Λ].obj J))).symm
      ((moduleAbelianForget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app J))
  naturality {J K} h := by
    apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _ |>.injective
    dsimp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Functor.comp_obj, Equiv.apply_symm_apply]
    change (moduleAbelianForget Λ Y).map h ≫
        (moduleAbelianForget Λ Y).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) =
      (moduleAbelianForget Λ Y).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app J) ≫
        (moduleAbelianForget Λ Y).map
          (((g)_*[ModuleCat.{u + 1} Λ]).map (((g)^*[ModuleCat.{u + 1} Λ]).map h))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (moduleAbelianForget Λ Y).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality h)

/-- The canonical inverse-image comparison is invertible by the underived comparison. -/
instance moduleAbelianUpperStarComparison_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (moduleAbelianUpperStarComparison Λ g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro J
  exact isIso_moduleAbelianInverseImageComparison g Λ J

/-- The unit-compatible inverse-image coefficient isomorphism. -/
noncomputable def moduleAbelianUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  asIso (moduleAbelianUpperStarComparison Λ g)

/-- Applying exact functors to complexes lifts the inverse-image coefficient comparison. -/
noncomputable def moduleAbelianDerivedUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    D+(moduleAbelianForget Λ Y) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}]) ≅
      D+((g)^*[ModuleCat.{u + 1} Λ]) ⋙ D+(moduleAbelianForget Λ X) :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (moduleAbelianUpperStarIso Λ g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical isomorphism for derived direct image after forgetting coefficients. -/
noncomputable def moduleAbelianDerivedLowerStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  asIso (moduleAbelianDerivedLowerStarComparison Λ f)

end AlgebraicGeometry.Etale
```

## New

### Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1, Nailin Guan, SHEAF group A3
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).
The presheaf is written using derived Hom from the free abelian sheaf of an etale
representable. This is the standard representation of restricted hypercohomology:
Hom(Z[U ×_X Y][0], K[q]) = H^q(U ×_X Y, K|). Its restriction maps are precomposition.
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram

/-! # The raw cohomology diagram

Source: Stacks Project, Tag 09Z1, the canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality

/-! # Raw cohomology pullback and the higher-image comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

/-! # Raw pullback and the derived-Hom comparison

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore

/-! # Canonical upstream raw cohomology comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
This compatibility module exports the upstream `HigherDirectImageRawTransitionToHomCore`.
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct

/-! # Canonical upstream raw cohomology comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
This compatibility module exports the upstream `HigherDirectImageRawTriangleAdjunct`.
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension

/-! # Raw pullback for a commutative triangle

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
-/

@[expose] public section
```

### Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Canonical derived direct image comparison for module coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)
-/

@[expose] public section

-- This shim retains a private API used by an `import all` consumer.
set_option linter.privateModule false

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private alias upstream_evaluation_acyclic := moduleAbelianForget_injective_evaluation_acyclic

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9. -/
private theorem moduleAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  exact upstream_evaluation_acyclic Λ X G W n

end AlgebraicGeometry.Etale
```

The sole consumer import change is `import all Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` to `import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.

## Users

The following is the complete transitive import audit, including quarantined
parents, computed from both source trees with the live tree taking precedence.
The canonical declaration names still supply every statement in this table.
Active direct consumers and the scalar-comparison restoration chain are checked
with lcompile.py in the report. Other quarantined modules retain their separate
restoration obligations; none is withdrawn, deleted, or weakened by this packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AbelianExchangeFilteredColimit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AbelianHigherDirectImageFilteredColimit | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing | unclaimed | Proof-only import all redirected to the defining upstream module; signature unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CartierPoleBoundary | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CohomologicalDimension | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.CommutativeExchangeChart | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCyclicModuleOfAbelian | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EllCohomologicalDimensionComparison | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomologyStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | claimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison | unclaimed | Canonical upstream re-export; preserves the public API. |
| Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyConventions | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.NTorsionModuleLift | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCup | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.PrimeCurveCharPHighVanishing | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | unclaimed | Restored unchanged; its original code compiles against the canonical imports. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | unclaimed | Restored unchanged; its original code compiles against the canonical imports. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Restored unchanged; its original code compiles against the canonical imports. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineInfinityBoundarySupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialHigherProjectionSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialInductionStep | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialProjectionSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreDerivedUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreUnitStalks | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.DeligneLaumon.FiniteCompactSupportFibreSupportBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.AmplificationProper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DeltaProperPushforward | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PreservationConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | claimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.BaseChangeTowardsFields | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.TraceFormula.PhEtaleComparisonHypotheses | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed | Public names and statements preserved; no statement adaptation. |
| Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Quarantined consumer; canonical names and statements preserved. No statement adaptation. |

## Status

landed 20261020T153746-L-2987711 2026-10-20 (merge of deliver/D2/Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram)
