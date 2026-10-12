/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Naturality of Leray's isomorphism

Leray's theorem `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H` identifies
the Čech cohomology of a quasi-coherent module on an affine covering with all finite
intersections affine with its sheaf cohomology. The identification comes from a natural
isomorphism of functors on the Čech-acyclic sheaves, so it can be chosen once and for all,
naturally in the module.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.presheafModuleCatMap`: the morphism of presheaves of
  `Γ(X, ⊤)`-modules induced by a morphism of sheaves of modules.
- `AlgebraicGeometry.Scheme.Modules.cechHLinearEquiv`: Leray's isomorphism
  `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`, as a definition.

## Main results

- `AlgebraicGeometry.Scheme.Modules.cechHLinearEquiv_naturality`: Leray's isomorphism is natural
  in the quasi-coherent module.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The morphism of presheaves of `Γ(X, ⊤)`-modules `ℱ.presheafModuleCat ⟶ 𝒢.presheafModuleCat`
induced by a morphism of sheaves of modules `φ : ℱ ⟶ 𝒢`. -/
noncomputable def presheafModuleCatMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ℱ.presheafModuleCat ⟶ 𝒢.presheafModuleCat :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val

lemma presheafModuleCatMap_app_apply {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (V : X.Opensᵒᵖ)
    (x : ℱ.presheafModuleCat.obj V) :
    (presheafModuleCatMap φ).app V x = φ.app V.unop x :=
  rfl

/-- The identification `presheafModuleCatCompForget₂Iso` is natural in the module. -/
lemma whiskerRight_presheafModuleCatMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    Functor.whiskerRight (presheafModuleCatMap φ) (forget₂ (ModuleCat.{u} Γ(X, ⊤))
      AddCommGrpCat.{u}) ≫ (presheafModuleCatCompForget₂Iso 𝒢).hom =
      (presheafModuleCatCompForget₂Iso ℱ).hom ≫
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
  ext V x
  rfl

/-- **Naturality of `cechComplexHomologyAddEquiv`**: the identification of the homology of
Mathlib's Čech complex of `ℱ.presheafModuleCat` with the Čech cohomology of the underlying
abelian sheaf is natural in `ℱ`. -/
lemma cechComplexHomologyAddEquiv_naturality {ι : Type u} (U : ι → X.Opens) {ℱ 𝒢 : X.Modules}
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
          (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (presheafModuleCatMap φ))
            q) x)) =
    HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) q
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q).hom x))
  rw [h]
  exact ConcreteCategory.congr_hom key _

/-- The finite intersections `U (y 0) ⊓ ⋯ ⊓ U (y k)` of a family of opens all of whose nonempty
finite intersections are affine are affine. -/
lemma isAffineOpen_iInf_of_forall_finset {ι : Type u} {U : ι → X.Opens}
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (k : ℕ)
    (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
  classical
  have h := hU (Finset.univ.image y) (Finset.univ_nonempty.image y)
  convert h using 1
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_)
    (le_iInf fun l ↦ iInf₂_le (y l) (Finset.mem_image_of_mem y (Finset.mem_univ l)))
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
  exact iInf_le _ l

/-- **A choice of Leray's natural isomorphism**: for a covering `𝔘` of `X` all of whose nonempty
finite intersections are affine, a natural isomorphism between Čech cohomology on `𝔘` and sheaf
cohomology, on the abelian sheaves which are Čech-acyclic on affines (e.g. the quasi-coherent
ones). -/
noncomputable def lerayIso {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (q : ℕ) :
    (cechAcyclicOnAffines X).ι ⋙ TopCat.Sheaf.cechCohomologyFunctor U q ≅
      (cechAcyclicOnAffines X).ι ⋙ CategoryTheory.Sheaf.functorH.{u}
        (Opens.grothendieckTopology X) q :=
  Classical.choice (TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH U hU'
    (cechAcyclicOnAffines X) (fun _ h ↦ cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h k y ↦ surjective_app_of_cechAcyclicOnAffines hS h
      (isAffineOpen_iInf_of_forall_finset hU k y)) q)

/-- The quasi-coherent module `ℱ`, as an object of the category of abelian sheaves which are
Čech-acyclic on affines. -/
noncomputable abbrev cechAcyclicObj (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    (cechAcyclicOnAffines X).FullSubcategory :=
  ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ, cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩

/-- **Leray's isomorphism** `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` of additive groups, for a covering `𝔘` of `X`
all of whose nonempty finite intersections are affine and a quasi-coherent module `ℱ`, through
the natural isomorphism `lerayIso`. -/
noncomputable def cechHAddEquiv {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃+ ℱ.H q :=
  (cechComplexHomologyAddEquiv U ℱ q).trans
    ((lerayIso U hU hU' q).app (cechAcyclicObj ℱ)).addCommGroupIsoToAddEquiv

/-- **Naturality of Leray's isomorphism** in the quasi-coherent module, at the level of
additive groups. -/
lemma cechHAddEquiv_naturality {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    {ℱ 𝒢 : X.Modules} [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢) (q : ℕ)
    (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechHAddEquiv U hU hU' 𝒢 q
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (presheafModuleCatMap φ))
          q x) =
      H.map φ q (cechHAddEquiv U hU hU' ℱ q x) := by
  have h := ConcreteCategory.congr_hom ((lerayIso U hU hU' q).hom.naturality
    (ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :
      cechAcyclicObj ℱ ⟶ cechAcyclicObj 𝒢)) (cechComplexHomologyAddEquiv U ℱ q x)
  refine (congrArg ((lerayIso U hU hU' q).app (cechAcyclicObj 𝒢)).hom
    (cechComplexHomologyAddEquiv_naturality U φ q x)).trans ?_
  exact h

/-- **Leray's isomorphism** `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` as `Γ(X, ⊤)`-modules, for a covering `𝔘` of
`X` all of whose nonempty finite intersections are affine and a quasi-coherent module `ℱ`. It is
natural in `ℱ` (`cechHLinearEquiv_naturality`).

(blueprint: `lem-pc-cech-computes`) -/
noncomputable def cechHLinearEquiv {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q where
  toAddEquiv := cechHAddEquiv U hU hU' ℱ q
  map_smul' r x := by
    have h := ConcreteCategory.congr_hom ((lerayIso U hU hU' q).hom.naturality
      (ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)) :
        cechAcyclicObj ℱ ⟶ cechAcyclicObj ℱ)) (cechComplexHomologyAddEquiv U ℱ q x)
    refine ((congrArg ((lerayIso U hU hU' q).app (cechAcyclicObj ℱ)).hom
      (cechComplexHomologyAddEquiv_smul U ℱ q r x)).trans h).trans ?_
    exact (H.smul_eq_map ℱ q r _).symm

lemma cechHLinearEquiv_apply {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ)
    (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechHLinearEquiv U hU hU' ℱ q x = cechHAddEquiv U hU hU' ℱ q x :=
  rfl

/-- **Naturality of Leray's isomorphism** `cechHLinearEquiv` in the quasi-coherent module: it
intertwines the map induced on Čech cohomology by a morphism `φ : ℱ ⟶ 𝒢` with the map induced
on sheaf cohomology.

(blueprint: `lem-pc-cech-computes`) -/
lemma cechHLinearEquiv_naturality {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    {ℱ 𝒢 : X.Modules} [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢) (q : ℕ)
    (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechHLinearEquiv U hU hU' 𝒢 q
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map (presheafModuleCatMap φ))
          q x) =
      H.map φ q (cechHLinearEquiv U hU hU' ℱ q x) :=
  cechHAddEquiv_naturality U hU hU' φ q x

end AlgebraicGeometry.Scheme.Modules
