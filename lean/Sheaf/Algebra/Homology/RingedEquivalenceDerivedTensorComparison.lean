/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Derived tensor comparison for an exact tensor equivalence

Source: Stacks Project, Tags 06YN, 06YS and 06YU.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe c h d k r w w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

private theorem ringedEquivalence_kFlat_image
    {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
    {D : Type d} [Category.{k} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w'} (ringedSiteModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (F : ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      ringedSiteModules.{r}
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [F.Additive] [F.IsEquivalence]
    (c₀ : tensor _ ⋙ F ≅ F.prod F ⋙ tensor _)
    (P : CochainComplex (KFlatFixedTensor.Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  let := cochainModulesPreadditive R
  let := cochainModulesPreadditive S
  let A := KFlatFixedTensor.Modules R
  let B := KFlatFixedTensor.Modules S
  let FC := F.mapHomologicalComplex (.up ℤ)
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj (curriedTensor B) :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ c₀.app (M, N)) (by
      intro N N' g
      change F.map (M ◁ g) ≫ _ = _ ≫ (F.obj M ◁ F.map g)
      have h := c₀.hom.naturality (Prod.mkHom (𝟙 M) g)
      change F.map (𝟙 M ⊗ₘ g) ≫ _ = _ ≫ (F.map (𝟙 M) ⊗ₘ F.map g) at h
      rw [id_tensorHom, F.map_id, id_tensorHom] at h
      exact h)) (by
      intro M M' g
      apply NatTrans.ext
      funext N
      change F.map (g ▷ N) ≫ _ = _ ≫ (F.map g ▷ F.obj N)
      have h := c₀.hom.naturality (Prod.mkHom g (𝟙 N))
      change F.map (g ⊗ₘ 𝟙 N) ≫ _ = _ ≫ (F.map g ⊗ₘ F.map (𝟙 N)) at h
      rw [tensorHom_id, F.map_id, tensorHom_id] at h
      exact h)
  let tC (P Q : CochainComplex A ℤ) :=
    asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) P Q)
  intro Z hZ
  let e := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  have hZ' : (e.inverse.obj Z).Acyclic := by
    intro q
    exact (hZ q).map F.asEquivalence.inverse
  have ht := hP (e.inverse.obj Z) hZ'
  have ht' : (FC.obj (CochainComplex.mapBifunctor
      (e.inverse.obj Z) P (curriedTensor A))).Acyclic := by
    intro q
    exact (ht q).map F
  have ht'' : (CochainComplex.mapBifunctor (FC.obj (e.inverse.obj Z))
      (FC.obj P) (curriedTensor B)).Acyclic := by
    intro q
    exact (ht' q).of_iso (tC (e.inverse.obj Z) P)
  let j := (Functor.uncurry.obj (curriedTensor B).map₂CochainComplex).mapIso
    (Iso.prod (e.counitIso.app Z) (Iso.refl (FC.obj P)))
  intro q
  exact (ht'' q).of_iso j

/-- An additive equivalence preserving ordinary sheaf tensor preserves derived tensor
against a module in degree zero. No Tor bound, scalar reduction or slice site is assumed.

Source: Stacks Project, sites-cohomology.tex, definition-K-flat, lemma-K-flat-resolution
and definition-derived-tor (Tags 06YN, 06YS and 06YU); the exact-equivalence paragraph
of lem-sf-clopen-preserves-residue-tor.
(blueprint: lem-sf-ringed-equivalence-derived-tensor-comparison).

Proof: Apply the additive equivalence F termwise to cochain complexes. F and its
inverse are exact and F preserves coproducts, so the ordinary tensor comparison
induces an isomorphism between F of a signed total tensor and the total tensor of
the images. For an acyclic target complex Z, the inverse image of Z is acyclic.
If P is K-flat, its total tensor with that inverse image is acyclic. Apply F,
the total comparison and the counit to deduce that Tot(Z,F(P)) is acyclic. Thus
F(P) is K-flat. Choose a K-flat resolution P of a representative of X. The existing
K-flat single-tensor comparison computes both X tensor N[0] and F(X) tensor F(N)[0]
by the corresponding termwise tensor complexes. The components of the given ordinary
tensor comparison form an isomorphism F(P tensor N) to F(P) tensor F(N): its chain-map
equation is precisely naturality for (d_P,id_N). Localize this chain isomorphism and
compose with the exact-functor factorization and the chosen representative isomorphism.
This supplies the asserted isomorphism. No boundedness, nonzero-ring or inhabited-site
hypothesis is needed; the same construction applies to zero complexes and empty sites. -/
theorem ringedEquivalence_derivedTensorComparison
    {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
    {D : Type d} [Category.{k} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{r}) (S : Sheaf K CommRingCat.{r})
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w'} (ringedSiteModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (F : ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      ringedSiteModules.{r}
        ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [F.Additive] [F.IsEquivalence]
    (c₀ : tensor _ ⋙ F ≅ F.prod F ⋙ tensor _) :
    ∀ (X : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
      (N : ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)),
      Nonempty (F.mapDerivedCategory.obj
          ((siteDerivedTensorIndependentCoefficients J R).obj
            (X, (DerivedCategory.singleFunctor _ 0).obj N)) ≅
        (siteDerivedTensorIndependentCoefficients K S).obj
          (F.mapDerivedCategory.obj X, (DerivedCategory.singleFunctor _ 0).obj (F.obj N))) := by
  classical
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let := cochainModulesPreadditive R
  let := cochainModulesPreadditive S
  let FC := F.mapHomologicalComplex (.up ℤ)
  intro X N
  let Y := DerivedCategory.Q.objPreimage X
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Y
  let := hp
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  obtain ⟨cR, _⟩ := (ringed_kFlat_single_tensor_comparison R).exists
  obtain ⟨cS, _⟩ := (ringed_kFlat_single_tensor_comparison S).exists
  let sR : (siteDerivedTensorIndependentCoefficients J R).obj
      (DerivedCategory.Q.obj P, (DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.obj (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P) :=
    (siteDerivedTensorIndependentCoefficients J R).mapIso
      (Iso.prod (Iso.refl _) ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N)) ≪≫
        cR P hP N
  let sS : (siteDerivedTensorIndependentCoefficients K S).obj
      (DerivedCategory.Q.obj (FC.obj P),
        (DerivedCategory.singleFunctor _ 0).obj (F.obj N)) ≅
      DerivedCategory.Q.obj
        (((tensorRight (F.obj N)).mapHomologicalComplex (.up ℤ)).obj (FC.obj P)) :=
    (siteDerivedTensorIndependentCoefficients K S).mapIso
      (Iso.prod (Iso.refl _) ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj N))) ≪≫
        cS (FC.obj P) (ringedEquivalence_kFlat_image R S F c₀ P hP) (F.obj N)
  let tN : FC.obj (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((tensorRight (F.obj N)).mapHomologicalComplex (.up ℤ)).obj (FC.obj P) :=
    HomologicalComplex.Hom.isoOfComponents (fun q ↦ c₀.app (P.X q, N)) (by
      intro i j hij
      change (c₀.app (P.X i, N)).hom ≫ (F.map (P.d i j) ▷ F.obj N) =
        F.map (P.d i j ▷ N) ≫ (c₀.app (P.X j, N)).hom
      have h := c₀.hom.naturality (Prod.mkHom (P.d i j) (𝟙 N))
      change F.map (P.d i j ⊗ₘ 𝟙 N) ≫ _ = _ ≫
        (F.map (P.d i j) ⊗ₘ F.map (𝟙 N)) at h
      rw [tensorHom_id, F.map_id, tensorHom_id] at h
      exact h.symm)
  exact ⟨F.mapDerivedCategory.mapIso
      ((siteDerivedTensorIndependentCoefficients J R).mapIso
        (Iso.prod eP.symm (Iso.refl _))) ≪≫ F.mapDerivedCategory.mapIso sR ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso tN ≪≫ sS.symm ≪≫
      (siteDerivedTensorIndependentCoefficients K S).mapIso
        (Iso.prod ((F.mapDerivedCategoryFactors.app P).symm ≪≫
          F.mapDerivedCategory.mapIso eP) (Iso.refl _))⟩

end SheafOfModules
