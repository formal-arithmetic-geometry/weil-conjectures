/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Leray's theorem, naturally in the sheaf

`AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H` gives, for each
quasi-coherent module separately, an isomorphism between Čech cohomology on a covering with
affine finite intersections and sheaf cohomology. Here we fix one natural isomorphism of functors
(`AlgebraicGeometry.Scheme.Modules.cechHNatIso`) and derive from it a named isomorphism
`AlgebraicGeometry.Scheme.Modules.cechComplexHomologyLinearEquivH` which is natural in the
quasi-coherent module (`AlgebraicGeometry.Scheme.Modules.cechComplexHomologyLinearEquivH_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The morphism of presheaves of `Γ(X, ⊤)`-modules underlying a morphism of sheaves of
modules. -/
noncomputable def presheafModuleCatMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ℱ.presheafModuleCat ⟶ 𝒢.presheafModuleCat :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val

lemma presheafModuleCatMap_app_apply {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (V : X.Opensᵒᵖ)
    (x : ℱ.presheafModuleCat.obj V) :
    (presheafModuleCatMap φ).app V x = φ.app V.unop x :=
  rfl

/-- The identification `presheafModuleCatCompForget₂Iso` is natural in the sheaf of modules. -/
lemma whiskerRight_presheafModuleCatMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    Functor.whiskerRight (presheafModuleCatMap φ) (forget₂ (ModuleCat.{u} Γ(X, ⊤))
      AddCommGrpCat.{u}) ≫ (presheafModuleCatCompForget₂Iso 𝒢).hom =
      (presheafModuleCatCompForget₂Iso ℱ).hom ≫
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
  ext V x
  rfl

/-- The identification `cechComplexHomologyAddEquiv` is natural in the sheaf of modules. -/
lemma cechComplexHomologyAddEquiv_map {ι : Type u} (U : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) (q : ℕ) (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechComplexHomologyAddEquiv U 𝒢 q
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (presheafModuleCatMap φ))
          q x) =
      (TopCat.Sheaf.cechCohomologyFunctor U q).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) (cechComplexHomologyAddEquiv U ℱ q x) := by
  have key : HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (Functor.whiskerRight (presheafModuleCatMap φ)
        (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}))) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso 𝒢).hom) q =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, whiskerRight_presheafModuleCatMap]
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_naturality U ℱ.presheafModuleCat
      (presheafModuleCatMap φ) q) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  change HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (presheafModuleCatCompForget₂Iso 𝒢).hom) q
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso U 𝒢.presheafModuleCat q).hom
        ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
            (presheafModuleCatMap φ)) q) x)) =
    HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) q
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q).hom x))
  rw [h]
  exact ConcreteCategory.congr_hom key _

/-- If all nonempty finite intersections of a family of opens are affine, so are the
intersections `U (y 0) ⊓ ⋯ ⊓ U (y k)`. -/
lemma isAffineOpen_iInf_fin {ι : Type u} {U : ι → X.Opens}
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (k : ℕ)
    (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
  classical
  have h := hU (Finset.univ.image y) (Finset.univ_nonempty.image y)
  convert h using 1
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_)
    (le_iInf fun l ↦ iInf₂_le (y l) (Finset.mem_image_of_mem y (Finset.mem_univ l)))
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
  exact iInf_le _ l

/-- **Leray's natural isomorphism.** A fixed choice of natural isomorphism, on the abelian
sheaves which are Čech-acyclic on affine opens, between the Čech cohomology of an open covering
all of whose nonempty finite intersections are affine and sheaf cohomology
(`TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH`).

(blueprint: `lem-pc-cech-computes`) -/
noncomputable def cechHNatIso {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (q : ℕ) :
    (cechAcyclicOnAffines X).ι ⋙ TopCat.Sheaf.cechCohomologyFunctor U q ≅
      (cechAcyclicOnAffines X).ι ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q :=
  Classical.choice (TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH U hU'
    (cechAcyclicOnAffines X) (fun _ h ↦ cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h k y ↦ surjective_app_of_cechAcyclicOnAffines hS h (isAffineOpen_iInf_fin hU k y))
    q)

/-- The underlying abelian sheaf of a quasi-coherent module, as an object of the full subcategory
of sheaves which are Čech-acyclic on affine opens. -/
noncomputable abbrev toCechAcyclicOnAffines (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    (cechAcyclicOnAffines X).FullSubcategory :=
  ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ, cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩

/-- **Leray's theorem for quasi-coherent sheaves, as a named isomorphism.** For an open covering
`𝔘 = (U i)` all of whose nonempty finite intersections are affine and a quasi-coherent
`𝒪_X`-module `ℱ`, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` as `Γ(X, ⊤)`-modules, through the natural isomorphism
`cechHNatIso`. It is natural in `ℱ` (`cechComplexHomologyLinearEquivH_map`).

(blueprint: `lem-pc-cech-computes`) -/
noncomputable def cechComplexHomologyLinearEquivH {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q where
  toAddEquiv := (cechComplexHomologyAddEquiv U ℱ q).trans
    ((cechHNatIso U hU hU' q).app (toCechAcyclicOnAffines ℱ)).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    have h := ConcreteCategory.congr_hom ((cechHNatIso U hU hU' q).hom.naturality
      (ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)) :
        toCechAcyclicOnAffines ℱ ⟶ toCechAcyclicOnAffines ℱ))
        (cechComplexHomologyAddEquiv U ℱ q x)
    refine (congrArg ((cechHNatIso U hU hU' q).app (toCechAcyclicOnAffines ℱ)).hom
      (cechComplexHomologyAddEquiv_smul U ℱ q r x)).trans ?_
    exact h.trans (H.smul_eq_map ℱ q r _).symm

lemma cechComplexHomologyLinearEquivH_apply {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ)
    (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechComplexHomologyLinearEquivH U hU hU' ℱ q x =
      ((cechHNatIso U hU hU' q).app (toCechAcyclicOnAffines ℱ)).hom
        (cechComplexHomologyAddEquiv U ℱ q x) :=
  rfl

/-- **Naturality of Leray's isomorphism**: `cechComplexHomologyLinearEquivH` transports the map
induced on Čech cohomology by a morphism `φ : ℱ ⟶ 𝒢` of quasi-coherent modules to the map
`H^q(φ)` on sheaf cohomology. -/
lemma cechComplexHomologyLinearEquivH_map {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    {ℱ 𝒢 : X.Modules} [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢) (q : ℕ)
    (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechComplexHomologyLinearEquivH U hU hU' 𝒢 q
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (presheafModuleCatMap φ))
          q x) =
      H.map φ q (cechComplexHomologyLinearEquivH U hU hU' ℱ q x) := by
  rw [cechComplexHomologyLinearEquivH_apply, cechComplexHomologyAddEquiv_map]
  exact ConcreteCategory.congr_hom ((cechHNatIso U hU hU' q).hom.naturality
    (ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :
      toCechAcyclicOnAffines ℱ ⟶ toCechAcyclicOnAffines 𝒢)) (cechComplexHomologyAddEquiv U ℱ q x)

end AlgebraicGeometry.Scheme.Modules
