/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Higher direct images as sheafified cohomology presheaves

For `h : Y ⟶ X` and `K ∈ D⁺(Y_ét, Λ)`, the `q`-th cohomology sheaf of `Rh_* K` receives a
canonical map from the presheaf `W ↦ H^q(W ×_X Y, K|)` on the small étale site of `X`; for `h`
quasi-compact and quasi-separated it identifies `R^q h_* K` with the sheafification of that
presheaf. That higher direct images commute with filtered colimits is in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`, and the
resulting vanishing criterion for `R^q h_* (Λ/dΛ)` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.LocalVanishing`.

## Main definitions

- `AlgebraicGeometry.Etale.higherDirectImagePresheaf`: the presheaf `W ↦ H^q(W ×_X Y, K|)`.
- `AlgebraicGeometry.Etale.freeSheafHomEquiv`: `Λ[W]` corepresents sections over `W`.
- `AlgebraicGeometry.Etale.derivedHomToHomology`: the map `Hom(Λ[W][0], L) ⟶ Hom(Λ[W], H⁰(L))`.
- `AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf`: the canonical map from that presheaf
  to `R^q h_* K`.

## Main statements

- `AlgebraicGeometry.Etale.isLocallyBijective_derivedHomToHomology`: for `L ∈ D⁺(X_ét, Λ)`,
  classes `Λ[W][0] ⟶ L` are locally the same as sections of `H⁰(L)` over `W`.
- `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf`: `R^q h_* K` is the
  sheafification of `W ↦ H^q(W ×_X Y, K|)` for a quasi-compact quasi-separated `h`.

## References

- Stacks Project, Lemma 59.51.6, <https://stacks.math.columbia.edu/tag/03Q8>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section CohomologyPresheaf

/-- The free sheaf `Λ[W]` of `Λ`-modules on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ Λ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(Λ[W], F)` is the étale cohomology `H^q(W, F|_W)`. -/
noncomputable def Etale.freeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf _ _

/-- The hypercohomology presheaf of an object `K` of `D⁺(Y_ét, Λ)` relative to `h : Y ⟶ X`:
the presheaf on the small étale site of `X` sending `W` to
`Hom(h^* Λ[W], K[q]) = H^q(W ×_X Y, K|)`, the degree-`q` (hyper)cohomology of the restriction
of `K` to `W ×_X Y`; indeed `h^* Λ[W] = Λ[W ×_X Y]`. For a sheaf `K = F[0]` this is the
presheaf `W ↦ H^q(W ×_X Y, F|)`. -/
noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

/-- Evaluation at the generator: for a sheaf `G` of `Λ`-modules on `X_ét`, the natural map
`Hom(Λ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `Λ[W]` given by
the identity of `W`. -/
noncomputable def Etale.freeSheafSections {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj G ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality X.smallEtaleTopology
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (ModuleCat.free Λ)))
    have h₂ := congr_arg (fun k ↦ k.hom (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))) =
        ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify X.smallEtaleTopology
          (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))

section DerivedSections

open Opposite

variable {X : Scheme.{u}}

/-- The free sheaf `Λ[W]` corepresents sections over `W`. -/
noncomputable def Etale.freeSheafHomEquiv (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.freeSheaf Λ X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma Etale.freeSheafHomEquiv_apply (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W G f = (Etale.freeSheafSections Λ G).app (op W) f := by
  simp [Etale.freeSheafHomEquiv, Etale.freeSheafSections]
  rfl

lemma Etale.freeSheafHomEquiv_comp (W : X.Etale)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) (g : G ⟶ G') :
    Etale.freeSheafHomEquiv Λ W G' (f ≫ g) =
      g.hom.app (op W) (Etale.freeSheafHomEquiv Λ W G f) := by
  simp only [Etale.freeSheafHomEquiv_apply, Etale.freeSheafSections]
  rfl

lemma Etale.freeSheafHomEquiv_map {W W' : X.Etale} (v : W' ⟶ W)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W' G ((Etale.freeSheaf Λ X).map v ≫ f) =
      G.obj.map v.op (Etale.freeSheafHomEquiv Λ W G f) := by
  simp only [Etale.freeSheafHomEquiv_apply]
  exact congrArg (fun k ↦ k f) ((Etale.freeSheafSections Λ G).naturality v.op)


variable {Λ}

/-- For `L ∈ D⁺(X_ét, Λ)`, the map `Hom(Λ[W][0], L) ⟶ Hom(Λ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`. -/
noncomputable def Etale.derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).inv.naturality
        ((Etale.freeSheaf Λ X).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ X).map g.unop) ≫ f) =
      (Etale.freeSheaf Λ X).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((Etale.freeSheaf Λ X).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

lemma Etale.derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (W : X.Etaleᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ L) :
    (Etale.derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β :=
  rfl

/-- The sections map of a morphism of sheaves of `Λ`-modules, on the underlying presheaves of
abelian groups. -/
noncomputable abbrev Etale.sectionsMap {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : G ⟶ G') :
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj ⟶
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G').obj :=
  ((sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map g).hom

lemma Etale.freeSheafSections_naturality
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G') :
    Etale.freeSheafSections Λ G ≫ Etale.sectionsMap g =
      Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map g) ≫
        Etale.freeSheafSections Λ G' := by
  ext W f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← Etale.freeSheafHomEquiv_apply, ← Etale.freeSheafHomEquiv_apply]
  exact (Etale.freeSheafHomEquiv_comp Λ W.unop f g).symm


section Key

variable (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The comparison `H⁰(M) ⟶ H⁰(Q M)` between the homology sheaf of a complex and the homology of
its image in `D⁺`. -/
noncomputable abbrev Etale.homologyComparison :
    M.obj.homology 0 ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M) :=
  (DerivedCategory.homologyFunctorFactors _ 0).inv.app M.obj ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.quotientCompQhIso _).inv.app M.obj)

lemma Etale.derivedHomToHomology_app_eq {W : X.Etaleᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ Etale.homologyComparison M :=
  DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map
    β f hf

theorem Etale.isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  have : Sheaf.IsLocallySurjective (M.obj.homologyπ 0) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  constructor
  intro W σ
  let σ' : ToType ((M.obj.homology 0).obj.obj (op W)) :=
    (inv (Etale.homologyComparison M)).hom.app (op W) σ
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology (M.obj.homologyπ 0).hom σ')
  rintro V g ⟨c, hc⟩
  let A := (Etale.freeSheaf Λ X).obj V
  let c' := (Etale.freeSheafHomEquiv Λ V (M.obj.cycles 0)).symm c
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  let fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj :=
    HomologicalComplex.mkHomFromSingle (inv τ ≫ c' ≫ M.obj.iCycles 0) (by
      intro k _
      simp)
  have hfM : DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap fM 0 = c' := by
    rw [← cancel_mono (M.obj.iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.mkHomFromSingle_f]
    have hτ : DerivedCategory.singleCyclesHom A ≫
        ((HomologicalComplex.single _ (.up ℤ) 0).obj A).iCycles 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = τ := by
      simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
    rw [reassoc_of% hτ, IsIso.hom_inv_id_assoc]
  obtain ⟨β, hβ⟩ : ∃ β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      DerivedCategory.Plus.Q.obj M, DerivedCategory.Plus.ι.map β =
        DerivedCategory.Q.map fM ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj :=
    ⟨DerivedCategory.Plus.ι.preimage _, Functor.map_preimage _ _⟩
  refine ⟨β, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    Etale.derivedHomToHomology_app_eq M (W := op V) β fM hβ, reassoc_of% hfM,
    ← Etale.freeSheafHomEquiv_apply, Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    hc]
  erw [NatTrans.naturality_apply (Etale.homologyComparison M).hom g.op σ']
  have hσ : (Etale.homologyComparison M).hom.app (op W) σ' = σ := by
    simp only [σ']
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]
    rfl
  rw [hσ]
  rfl

/-- A map from a single complex whose degree-`0` component factors through the differential
`M⁻¹ ⟶ M⁰` is null-homotopic. -/
noncomputable def Etale.homotopyOfSingle {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
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

theorem Etale.isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  constructor
  intro W x y hxy
  let β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M := x - y
  have hβ : (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
      Etale.freeSheafSections Λ
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).app W β =
      0 := by
    simp only [β, map_sub]
    exact sub_eq_zero.2 hxy
  have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
    exact sub_eq_zero.symm
  rw [hsieve]
  let A := (Etale.freeSheaf Λ X).obj W.unop
  obtain ⟨f, hf⟩ := DerivedCategory.Plus.exists_ι_map_eq M β
  let z := DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0
  have hz : z ≫ M.obj.homologyπ 0 = (0 : A ⟶ M.obj.homology 0) := by
    have hm : IsIso (Etale.homologyComparison M) := by
      dsimp only [Etale.homologyComparison]
      infer_instance
    have h2 : z ≫ M.obj.homologyπ 0 ≫ Etale.homologyComparison M = 0 := by
      apply (Etale.freeSheafHomEquiv Λ W.unop
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).injective
      rw [Etale.freeSheafHomEquiv_apply, Etale.freeSheafHomEquiv_apply, map_zero]
      have := Etale.derivedHomToHomology_app_eq M β f hf
      simp only [z, Category.assoc]
      rw [← this]
      exact hβ
    calc z ≫ M.obj.homologyπ 0 =
        (z ≫ M.obj.homologyπ 0 ≫ Etale.homologyComparison M) ≫
          inv (Etale.homologyComparison M) := by
          simp only [Category.assoc, IsIso.hom_inv_id]; erw [Category.comp_id]
      _ = 0 := by rw [h2, Limits.zero_comp]
  let S := ShortComplex.mk (M.obj.toCycles (-1) 0) (M.obj.homologyπ 0) (by simp)
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S (M.obj.homologyIsCokernel (-1) 0 (by simp))
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  let k' := S.liftCycles z hz
  let k := Etale.freeSheafHomEquiv Λ W.unop S.cycles k'
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology S.toCycles.hom k)
  rintro V g ⟨b, hb⟩
  let φ := (Etale.freeSheaf Λ X).map g
  let A' := (Etale.freeSheaf Λ X).obj V
  let b' := (Etale.freeSheafHomEquiv Λ V (M.obj.X (-1))).symm b
  have hφz : φ ≫ z = b' ≫ M.obj.toCycles (-1) 0 := by
    apply (Etale.freeSheafHomEquiv Λ V _).injective
    have hz' : z = k' ≫ S.iCycles := (S.liftCycles_i z hz).symm
    rw [hz', Etale.freeSheafHomEquiv_map, Etale.freeSheafHomEquiv_comp,
      Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
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
  have hβ' : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β) =
        DerivedCategory.Q.map f' ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj := by
    rw [Functor.map_comp, hf, Functor.map_comp, Category.assoc]
    rfl
  have h0 := DerivedCategory.Plus.eq_zero_of_homotopy _ f' hβ'
    (Etale.homotopyOfSingle M f' (inv τ' ≫ b') hf'0)
  simp only [Presheaf.equalizerSieve_apply, map_zero, map_sub]
  have h0' : (ConcreteCategory.hom (((Etale.freeSheaf Λ X ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (DerivedCategory.Plus.Q.obj M)).map g.op)) (x - y) = 0 := h0
  rw [map_sub] at h0'
  exact h0'

end Key

/-- For every `L ∈ D⁺(X_ét, Λ)`, the map `W ↦ (Hom(Λ[W][0], L) ⟶ Γ(W, H⁰(L)))` is locally
injective and locally surjective: classes of maps to `L` are locally determined by the
section of `H⁰(L)` they induce, and every section of `H⁰(L)` locally comes from such a class. -/
theorem Etale.isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) := by
  obtain ⟨n, hn⟩ := L.2
  have : L.IsGE n := (L.isGE_ι_obj_iff n).1 hn
  obtain ⟨L', _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso L n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L'
  have : M.obj.IsKInjective := inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj L'.obj))
  have := Etale.isLocallyInjective_derivedHomToHomology M
  have := Etale.isLocallySurjective_derivedHomToHomology M
  have hfac : Etale.derivedHomToHomology L ≫
      Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) =
    (Functor.isoWhiskerLeft (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
      (preadditiveYoneda.mapIso e.symm)).hom ≫
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) ≫
      ((sheafToPresheaf _ _).mapIso ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
          ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso e))).hom := by
    simp only [Category.assoc]
    have hnat := Etale.freeSheafSections_naturality
      ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    change _ = _ ≫ _ ≫ Etale.freeSheafSections Λ _ ≫
      Etale.sectionsMap ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    rw [hnat]
    ext W β
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    congr 1
    change _ = ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map (β ≫ e.inv)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map e.hom
    rw [Etale.derivedHomToHomology_app_apply]
    simp
  rw [hfac]
  constructor <;> infer_instance

end DerivedSections
/-- The isomorphism `Hom(h^* Λ[W][0], K[q]) ≅ Hom(Λ[W][0], Rh_*(K[q]))`, natural in `W`: the
isomorphism `Lh^*(Λ[W][0]) ≅ (h^* Λ[W])[0]` and the adjunction `Lh^* ⊣ Rh_*`. -/
noncomputable def Etale.higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ≅
      (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Etale.freeSheaf Λ X)
    (((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  NatIso.ofComponents (fun W ↦ AddEquiv.toAddCommGrpIso
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homAddEquiv _ _))
    (fun g ↦ by
      ext f
      exact (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
        h).homEquiv_naturality_left _ _)

/-- The map `Hom(h^* Λ[W], K[q]) ⟶ Hom(Λ[W], H^q(Rh_* K))`, natural in `W`: the adjunction
`Lh^* ⊣ Rh_*` (using `Lh^*(Λ[W][0]) ≅ (h^* Λ[W])[0]`), then the degree-`0` homology, using
`H^0(Λ[W][0]) ≅ Λ[W]` and `H^0((Rh_* K)[q]) ≅ H^q(Rh_* K)`. -/
noncomputable def Etale.higherDirectImagePresheafToHom {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) :=
  (Etale.higherDirectImagePresheafIso Λ h q K).hom ≫
  Etale.derivedHomToHomology (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) ≫
  Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _))

/-- The canonical map from the presheaf `W ↦ H^q(W ×_X Y, K|)` to the sheaf `H^q(Rh_* K)`, of
presheaves of abelian groups on `X_ét`: a class `Λ[W ×_X Y][0] ⟶ K[q]` goes, by adjunction, to
a map `Λ[W][0] ⟶ (Rh_* K)[q]`, then to `Λ[W] ⟶ H^q(Rh_* K)` on degree-`0` homology, and then to
the section of `H^q(Rh_* K)` over `W` that it picks out. On a complex of sheaves this is the map
`H^q(Γ(W ×_X Y, I^•)) ⟶ Γ(W, H^q(h_* I^•))` for an injective resolution `I^•` of `K`. -/
noncomputable def Etale.higherDirectImagePresheafToSheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
  Etale.higherDirectImagePresheafToHom Λ h q K ≫ Etale.freeSheafSections Λ _

/-- The canonical map from `W ↦ Hᵠ(W ×_X Y, K|)` to `Hᵠ(Rh_* K)` is locally injective and
locally surjective, for every morphism `h`. -/
theorem Etale.isLocallyBijective_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K) := by
  let L := R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)
  let eH : (DerivedCategory.Plus.homologyFunctor _ 0).obj L ⟶
      (DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) :=
    (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _
  have : IsIso eH := by dsimp only [eH]; infer_instance
  have : IsIso (Etale.sectionsMap eH) := inferInstanceAs
    (IsIso ((sheafToPresheaf _ _).map ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map eH)))
  have hφ : Etale.higherDirectImagePresheafToSheaf Λ h q K =
      (Etale.higherDirectImagePresheafIso Λ h q K).hom ≫
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ≫
        Etale.sectionsMap eH := by
    simp only [Etale.higherDirectImagePresheafToSheaf, Etale.higherDirectImagePresheafToHom,
      Category.assoc]
    rw [Etale.freeSheafSections_naturality]
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_derivedHomToHomology L
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Etale.higherDirectImagePresheafToSheaf Λ h q K) := by rw [hφ]; infer_instance
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Etale.higherDirectImagePresheafToSheaf Λ h q K) := by rw [hφ]; infer_instance
  exact ⟨‹_›, ‹_›⟩

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms, for complexes.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `K ∈ D⁺(Y_ét, Λ)`. Then the `q`-th
cohomology sheaf of `Rh_* K` is, as a sheaf of abelian groups, the sheafification of the
presheaf `W ↦ H^q(W ×_X Y, K|)` on the small étale site of `X`
(`AlgebraicGeometry.Etale.higherDirectImagePresheaf`): the canonical map
`AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf` induces an isomorphism from the
sheafification. The hypotheses on `h` are those of the blueprint; the statement holds for any
`h` (Stacks `072W`). -/
theorem Etale.isIso_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q K)) := by
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ h q K
  set ψ := ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (Etale.higherDirectImagePresheafToSheaf Λ h q K)
  have hfac : toSheafify _ _ ≫ ψ.hom = Etale.higherDirectImagePresheafToSheaf Λ h q K := by
    have := ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
      _ _).apply_symm_apply (Etale.higherDirectImagePresheafToSheaf Λ h q K)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨?_, ?_⟩
  · have : Presheaf.IsLocallyInjective X.smallEtaleTopology (toSheafify _ _ ≫ ψ.hom) := by
      rw [hfac]; infer_instance
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      X.smallEtaleTopology
      (toSheafify _ _) ψ.hom
  · have : Presheaf.IsLocallySurjective X.smallEtaleTopology (toSheafify _ _ ≫ ψ.hom) := by
      rw [hfac]; infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective X.smallEtaleTopology
      (toSheafify _ _) ψ.hom

/-- Blueprint `lem-weil-pbc-qcqs-higher-direct-image`: Higher direct images for quasi-compact
quasi-separated morphisms.

Let `h : Y ⟶ X` be quasi-compact and quasi-separated and `F` an étale sheaf of `Λ`-modules on
`Y`. Then `R^q h_* F` is, as a sheaf of abelian groups, the sheafification of the presheaf
`W ↦ H^q(W ×_X Y, F|)` on the small étale site of `X`, via the canonical map
`AlgebraicGeometry.Etale.higherDirectImagePresheafToSheaf`. This is the case `K = F[0]` of
`AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf`. -/
theorem Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  Etale.isIso_higherDirectImagePresheafToSheaf Λ h q _

end CohomologyPresheaf


section FilteredColimits

open Opposite

/-- Morphisms out of `h^* Λ[W]` are morphisms out of `Λ[W ×_X Y]`. -/
noncomputable def Etale.upperStarFreeSheafHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) ≃
      ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) ⟶ G) :=
  ((Etale.upperStarLowerStarAdjunction _ h).homEquiv _ _).trans
    ((Etale.freeSheafHomEquiv Λ W _).trans (Etale.freeSheafHomEquiv Λ _ G).symm)

lemma Etale.upperStarFreeSheafHomEquiv_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) (g : G ⟶ G') :
    Etale.upperStarFreeSheafHomEquiv Λ h W G' (a ≫ g) =
      Etale.upperStarFreeSheafHomEquiv Λ h W G a ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.upperStarFreeSheafHomEquiv, Equiv.trans_apply, Etale.freeSheafHomEquiv_comp,
    Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The pullback of the free sheaf `Λ[W]` along `h : Y ⟶ X` is the free sheaf on `W ×_X Y`:
both corepresent the sections over `W ×_X Y`. -/
noncomputable def Etale.upperStarFreeSheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) :=
  Coyoneda.ext _ _ (fun f ↦ Etale.upperStarFreeSheafHomEquiv Λ h W _ f)
    (fun g ↦ (Etale.upperStarFreeSheafHomEquiv Λ h W _).symm g) (by simp) (by simp) (by
      intro Z Z' f g
      apply (Etale.upperStarFreeSheafHomEquiv Λ h W _).injective
      rw [Etale.upperStarFreeSheafHomEquiv_comp]
      simp)

/-- The map of hypercohomology presheaves `W ↦ Hᵠ(W ×_X Y, K|)` induced by `φ : K ⟶ K'`. -/
noncomputable def Etale.higherDirectImagePresheafMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheaf Λ h q K ⟶ Etale.higherDirectImagePresheaf Λ h q K' :=
  Functor.whiskerLeft _ (preadditiveYoneda.map ((shiftFunctor _ q).map φ))


/-- The shift identification `H⁰((Rh_* K)[q]) ≅ Hᵠ(Rh_* K)`. -/
noncomputable abbrev Etale.homologyShiftComparison {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _

lemma Etale.higherDirectImagePresheafToHom_app_apply {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (W : X.Etaleᵒᵖ) (β : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W.unop)) ⟶ K⟦q⟧) :
    (Etale.higherDirectImagePresheafToHom Λ h q K).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
            ((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              ((Etale.freeSheaf Λ X).obj W.unop) ≫ β)) ≫
        Etale.homologyShiftComparison Λ h q K := by
  simp only [Etale.higherDirectImagePresheafToHom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    Etale.derivedHomToHomology_app_apply]
  rfl

/-- Naturality of the shift identification `H⁰((Rh_* K)[q]) ≅ Hᵠ(Rh_* K)` in `K`: for
`φ : K ⟶ K'` the square
```
H⁰((Rh_* K)[q])  ⟶ Hᵠ(Rh_* K)
      │                 │
      ▼                 ▼
H⁰((Rh_* K')[q]) ⟶ Hᵠ(Rh_* K')
```
commutes. -/
lemma Etale.homologyShiftComparison_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map ((shiftFunctor _ q).map φ)) ≫
      Etale.homologyShiftComparison Λ h q K' =
    Etale.homologyShiftComparison Λ h q K ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ) := by
  simp only [Etale.homologyShiftComparison]
  rw [← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality, Functor.map_comp_assoc]
  simp only [Category.assoc]
  congr 1
  have n₁ := ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.naturality
    ((shiftFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))
  have n₂ := ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.naturality
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)
  erw [reassoc_of% n₁, n₂]
  rfl

/-- Naturality of the canonical map from `W ↦ Hᵠ(W ×_X Y, K|)` to `Hᵠ(Rh_* K)` in `K`: for
`φ : K ⟶ K'` the square
```
Hᵠ(- ×_X Y, K|)  ⟶ Hᵠ(Rh_* K)
      │                 │
      ▼                 ▼
Hᵠ(- ×_X Y, K'|) ⟶ Hᵠ(Rh_* K')
```
of presheaves on `X_ét` commutes, the right map being the map on sections of `Hᵠ(Rh_* φ)`. -/
lemma Etale.higherDirectImagePresheafToSheaf_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToSheaf Λ h q K' =
      Etale.higherDirectImagePresheafToSheaf Λ h q K ≫ Etale.sectionsMap
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)) := by
  have h₁ : ∀ L, Etale.higherDirectImagePresheafToSheaf Λ h q L =
      Etale.higherDirectImagePresheafToHom Λ h q L ≫ Etale.freeSheafSections Λ _ := fun _ ↦ rfl
  have h₂ : Etale.higherDirectImagePresheafMap Λ h q φ ≫
      Etale.higherDirectImagePresheafToHom Λ h q K' =
      Etale.higherDirectImagePresheafToHom Λ h q K ≫ Functor.whiskerLeft (Etale.freeSheaf Λ X).op
        (preadditiveYoneda.map ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))) := by
    ext W β
    have e₁ : (Etale.higherDirectImagePresheafMap Λ h q φ).app W β =
        β ≫ (shiftFunctor _ q).map φ := rfl
    rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, e₁, Etale.higherDirectImagePresheafToHom_app_apply,
      Etale.higherDirectImagePresheafToHom_app_apply]
    change _ = _ ≫ _
    rw [← Category.assoc _ β, Adjunction.homEquiv_naturality_right, Functor.map_comp]
    simp only [Category.assoc]
    congr 2
    exact Etale.homologyShiftComparison_naturality Λ h q φ
  rw [h₁, h₁, Category.assoc, Etale.freeSheafSections_naturality, ← Category.assoc,
    ← Category.assoc, h₂]

/-- The hypercohomology presheaves `W ↦ Hᵠ(W ×_X Y, K|)` as a functor of `K`. -/
noncomputable def Etale.higherDirectImagePresheafFunctor {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor _ q ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0).op

lemma Etale.higherDirectImagePresheafFunctor_obj {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) (K) :
    (Etale.higherDirectImagePresheafFunctor Λ h q).obj K =
      Etale.higherDirectImagePresheaf Λ h q K :=
  rfl

lemma Etale.higherDirectImagePresheafFunctor_map {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K'} (φ : K ⟶ K') :
    (Etale.higherDirectImagePresheafFunctor Λ h q).map φ =
      Etale.higherDirectImagePresheafMap Λ h q φ :=
  rfl

end FilteredColimits

end AlgebraicGeometry
