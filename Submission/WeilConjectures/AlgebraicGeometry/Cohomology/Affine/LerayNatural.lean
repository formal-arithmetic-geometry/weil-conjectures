/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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


/-- **Leray's theorem, linearly over a ring mapping to the global sections.** For a ring
homomorphism `φ : A →+* Γ(X, ⊤)` (e.g. `Γ(S, 𝒪_S) → Γ(X, 𝒪_X)` for `X` over `S = Spec A`),
`cechComplexHomologyLinearEquivH` is `A`-linear after restricting scalars along `φ`.

(blueprint: `det-lem-picard-cech-computes`, `lem-pc-cech-computes`) -/
noncomputable def cechComplexHomologyRestrictScalarsLinearEquivH {A : Type u} [CommRing A]
    (φ : A →+* Γ(X, ⊤)) {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    (ModuleCat.restrictScalars φ).obj
        (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of Γ(X, ⊤) (ℱ.H q)) :=
  { (cechComplexHomologyLinearEquivH U hU hU' ℱ q).toAddEquiv with
    map_smul' a x := (cechComplexHomologyLinearEquivH U hU hU' ℱ q).map_smul (φ a) x }


end AlgebraicGeometry.Scheme.Modules
