/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionBase
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSectionsBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.QuasiIsoSections
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexOfMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus
public import Mathlib.RingTheory.TensorProduct.Free
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FreeAwayBaseChange

/-!
# Comparison of a free model of the Čech complex with the higher direct images

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite affine cover `U` of `X` and a quasi-coherent `𝒪_X`-module `ℱ`.
Let `R` be an `A`-algebra with a ring map `τ : R ⟶ Γ(T, ⊤)` over `A`, `P` a complex of free
`R`-modules of finite rank (with chosen bases) and `Φ : P ⟶ R ⊗[A] Č(U, ℱ)` a morphism which is
a quasi-isomorphism after every base change `R ⟶ B`. Then the complex of free `𝒪_T`-modules with
the matrices of the differentials of `P` (mapped by `τ`) computes the higher direct images
`R^q f'_* g'^* ℱ` (`AlgebraicGeometry.Scheme.Modules.nonempty_homology_freeComplex_iso`).

The comparison morphism to the Čech resolution `f'_* Č(g'⁻¹ U, g'^* ℱ)` is given on the basis
vectors by the images of the basis of `P` under `Φ` and the base change of Čech cochains; over an
affine open `W` of `T` it is identified with `Γ(T, W) ⊗[R] Φ`, hence a quasi-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace CochainComplex

variable {R : Type u} [CommRing R] {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))

/-- The matrix of the differential `P^n ⟶ P^{n+1}` of a complex of free modules with chosen
bases. -/
noncomputable def dMatrix (n : ℤ) : Matrix (κ (n + 1)) (κ n) R :=
  LinearMap.toMatrix (b n) (b (n + 1)) (P.d n (n + 1)).hom

lemma dMatrix_mul (n : ℤ) : P.dMatrix b (n + 1) * P.dMatrix b n = 0 := by
  rw [dMatrix, dMatrix, ← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp, P.d_comp_d,
    ModuleCat.hom_zero, map_zero]

end CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  {R : Type u} [CommRing R] [Algebra Γ(S, ⊤) R]

/-- The sheafified Čech complex `f'_* Č(g'⁻¹ U, g'^* ℱ)` of the base change. -/
noncomputable abbrev mumfordCech : CochainComplex T.Modules ℕ :=
  ((pushforward f').mapHomologicalComplex _).obj
    (cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ))

section Sections

variable (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
  [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

/-- The base change map `Γ(T, W) ⊗[R] (R ⊗[A] Č^k(U, ℱ)) ⟶ Γ(W, f'_* Č^k(g'⁻¹ U, g'^* ℱ))`. -/
noncomputable def mumfordSectionsMap (k : ℕ) :
    Γ(T, W) ⊗[R] (R ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) →+
      Γ((mumfordCech (f' := f') (g' := g') ℱ U).X k, W) :=
  ((sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
      (f' ⁻¹ᵁ W)).inv.f k).hom.comp
    ((cechSectionsBaseChangeX H ℱ U W hg k).comp
      (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W)
        (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))).toAddMonoidHom)

lemma mumfordSectionsMap_apply (k : ℕ) (x) :
    mumfordSectionsMap H ℱ U W hg k x =
      (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)).inv.f k
        (cechSectionsBaseChangeX H ℱ U W hg k
          (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W) _ x)) :=
  rfl

/-- `mumfordSectionsMap` is bijective over an affine open. -/
lemma bijective_mumfordSectionsMap [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (mumfordSectionsMap (R := R) H ℱ U W hg k) :=
  ((ConcreteCategory.bijective_of_isIso _).comp
    (bijective_cechSectionsBaseChangeX H ℱ U W hg hW hU k)).comp
      (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W) _).bijective

end Sections

/-! ### The base change map of Čech complexes on sections, as a morphism of complexes -/

section SectionsHom

variable (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
  [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

/-- **The base change map of Čech complexes on sections**, as a morphism of complexes of abelian
groups `Γ(T, W) ⊗[R] (R ⊗[A] Č(U, ℱ)) ⟶ Γ(W, f'_* Č(g'⁻¹ U, g'^* ℱ))`; in degree `k` it is
`AlgebraicGeometry.Scheme.Modules.mumfordSectionsMap`. -/
noncomputable def mumfordSectionsHom :
    ((forget₂ (ModuleCat.{u} Γ(T, W)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((ModuleCat.baseChange R Γ(T, W)).mapHomologicalComplex _).obj
        (((ModuleCat.baseChange Γ(S, ⊤) R).mapHomologicalComplex _).obj
          (cechModuleComplexNat f ℱ U))) ⟶
      ((sectionsAb W).mapHomologicalComplex _).obj (mumfordCech (f' := f') (g' := g') ℱ U) :=
  ((forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (ModuleCat.mapHomologicalComplexBaseChangeCompIso Γ(S, ⊤) R Γ(T, W)
        (cechModuleComplexNat f ℱ U)).hom ≫
    cechSectionsBaseChange H ℱ U W hg ≫
      (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)).inv

lemma mumfordSectionsHom_f_apply (k : ℕ) (x) :
    (mumfordSectionsHom (R := R) H ℱ U W hg).f k x = mumfordSectionsMap H ℱ U W hg k x :=
  rfl

/-- `mumfordSectionsHom` is an isomorphism over an affine open. -/
lemma isIso_mumfordSectionsHom [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) :
    IsIso (mumfordSectionsHom (R := R) H ℱ U W hg) := by
  have : IsIso (cechSectionsBaseChange H ℱ U W hg) := by
    refine HomologicalComplex.Hom.isIso_of_components _ fun k ↦ ?_
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_cechSectionsBaseChangeX H ℱ U W hg hW hU k)
  dsimp only [mumfordSectionsHom]
  infer_instance

/-- `mumfordSectionsMap` is semilinear. -/
lemma mumfordSectionsMap_smul (k : ℕ) (c : Γ(T, W))
    (x : Γ(T, W) ⊗[R] (R ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))))) :
    mumfordSectionsMap H ℱ U W hg k (c • x) = c • mumfordSectionsMap H ℱ U W hg k x := by
  rw [mumfordSectionsMap_apply, mumfordSectionsMap_apply, LinearEquiv.map_smul]
  exact sectionsCechResolutionIso_inv_cechSectionsBaseChangeX_smul H ℱ U W hg k c _

/-- `mumfordSectionsMap` is compatible with the restriction from `W'` to `W ≤ W'`, on the
elements `1 ⊗ z`. -/
lemma presheaf_map_mumfordSectionsMap_one_tmul {W' : T.Opens} (hW : W ≤ W')
    [Algebra Γ(S, ⊤) Γ(T, W')] [Algebra R Γ(T, W')] [IsScalarTower Γ(S, ⊤) R Γ(T, W')]
    (hg' : algebraMap Γ(S, ⊤) Γ(T, W') = (g.appLE ⊤ W' (le_top.trans g.preimage_top.ge)).hom)
    (hR : ∀ r : R, T.presheaf.map (homOfLE hW).op (algebraMap R Γ(T, W') r) =
      algebraMap R Γ(T, W) r) (k : ℕ)
    (z : R ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    ((mumfordCech (f' := f') (g' := g') ℱ U).X k).presheaf.map (homOfLE hW).op
        (mumfordSectionsMap H ℱ U W' hg' k (1 ⊗ₜ z)) =
      mumfordSectionsMap H ℱ U W hg k (1 ⊗ₜ z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy]
  | tmul r m =>
    have h₁ (B : Type u) [CommRing B] [Algebra R B] :
        (1 : B) ⊗ₜ[R] (r ⊗ₜ[Γ(S, ⊤)] m) =
          algebraMap R B r • ((1 : B) ⊗ₜ[R] ((1 : R) ⊗ₜ[Γ(S, ⊤)] m)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h₁, h₁, mumfordSectionsMap_smul, mumfordSectionsMap_smul, map_smul, hR]
    congr 1
    rw [mumfordSectionsMap_apply, mumfordSectionsMap_apply]
    simp only [AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    exact presheaf_map_sectionsCechResolutionIso_inv_one_tmul H ℱ U W hg hW hg' k m

end SectionsHom

/-! ### The complex of free modules of a complex with bases -/

section Free

variable {Z : Scheme.{u}} {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))

/-- The complex of free `𝒪_Z`-modules whose differentials have the matrices of those of a complex
`P` of free `R`-modules with chosen bases, mapped to `Γ(Z, ⊤)` by `τ`. -/
noncomputable abbrev freeComplexOfBasis (τ : R →+* Γ(Z, ⊤)) : CochainComplex Z.Modules ℤ :=
  freeComplex (fun n ↦ (P.dMatrix b n).map τ) (fun n ↦ by
    rw [← Matrix.map_mul, P.dMatrix_mul, Matrix.map_zero _ (map_zero τ)])

/-- The sections over `W` of the free module `𝒪_Z^{(κ n)}` are `Γ(Z, W) ⊗[R] P^n`. -/
noncomputable def freeSectionsTensorEquiv (W : Z.Opens) [Algebra R Γ(Z, W)] (n : ℤ) :
    Γ(Z, W) ⊗[R] P.X n ≃ₗ[Γ(Z, W)] Γ(free (R := Z.ringCatSheaf) (κ n), W) :=
  (Algebra.TensorProduct.basis Γ(Z, W) (b n)).equivFun.trans
    (freeSectionsEquivOpens W (κ n)).symm

lemma freeSectionsEquivOpens_freeSectionsTensorEquiv (W : Z.Opens) [Algebra R Γ(Z, W)] (n : ℤ)
    (x : Γ(Z, W) ⊗[R] P.X n) :
    freeSectionsEquivOpens W (κ n) (freeSectionsTensorEquiv P b W n x) =
      (Algebra.TensorProduct.basis Γ(Z, W) (b n)).repr x := by
  simp [freeSectionsTensorEquiv]

/-- The identification of the sections over `W` of `freeComplexOfBasis P b τ` (in degrees `≥ 0`)
with `Γ(Z, W) ⊗[R] P`, as a morphism of complexes of abelian groups. -/
noncomputable def freeSectionsTensorHom (τ : R →+* Γ(Z, ⊤)) (W : Z.Opens) [Algebra R Γ(Z, W)]
    (hτ : algebraMap R Γ(Z, W) = (Z.presheaf.map (homOfLE le_top).op).hom.comp τ) :
    ((forget₂ (ModuleCat.{u} Γ(Z, W)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((ModuleCat.baseChange R Γ(Z, W)).mapHomologicalComplex _).obj
        (P.restriction ComplexShape.embeddingUpNat)) ⟶
      ((sectionsAb W).mapHomologicalComplex _).obj
        ((freeComplexOfBasis P b τ).restriction ComplexShape.embeddingUpNat) where
  f k := AddCommGrpCat.ofHom (freeSectionsTensorEquiv P b W k).toAddMonoidHom
  comm' := by
    rintro k _ rfl
    ext x
    have h₁ := freeComplex_d_natCast (fun n ↦ (P.dMatrix b n).map τ) (fun n ↦ by
      rw [← Matrix.map_mul, P.dMatrix_mul, Matrix.map_zero _ (map_zero τ)]) k
    change freeSectionsTensorEquiv P b W ((k + 1 : ℕ) : ℤ)
        ((P.d k (k + 1 : ℕ)).hom.baseChange Γ(Z, W) x) =
      Hom.app ((freeComplexOfBasis P b τ).d k (k + 1 : ℕ)) W (freeSectionsTensorEquiv P b W k x)
    rw [h₁]
    apply (freeSectionsEquivOpens W _).injective
    rw [freeSectionsEquivOpens_app, freeMatrix_freeHomOfMatrix,
      freeSectionsEquivOpens_freeSectionsTensorEquiv,
      freeSectionsEquivOpens_freeSectionsTensorEquiv, ← LinearMap.toMatrix_mulVec_repr,
      LinearMap.toMatrix_baseChange, Matrix.map_map, hτ]
    rfl

lemma freeSectionsTensorHom_f_apply (τ : R →+* Γ(Z, ⊤)) (W : Z.Opens) [Algebra R Γ(Z, W)]
    (hτ : algebraMap R Γ(Z, W) = (Z.presheaf.map (homOfLE le_top).op).hom.comp τ) (k : ℕ) (x) :
    (freeSectionsTensorHom P b τ W hτ).f k x = freeSectionsTensorEquiv P b W k x :=
  rfl

instance (τ : R →+* Γ(Z, ⊤)) (W : Z.Opens) [Algebra R Γ(Z, W)]
    (hτ : algebraMap R Γ(Z, W) = (Z.presheaf.map (homOfLE le_top).op).hom.comp τ) :
    IsIso (freeSectionsTensorHom P b τ W hτ) := by
  refine HomologicalComplex.Hom.isIso_of_components _ fun k ↦ ?_
  exact (ConcreteCategory.isIso_iff_bijective _).2 (freeSectionsTensorEquiv P b W k).bijective

end Free

/-! ### The comparison morphism -/

section Comparison

variable [Algebra Γ(S, ⊤) Γ(T, ⊤)] [Algebra R Γ(T, ⊤)] [IsScalarTower Γ(S, ⊤) R Γ(T, ⊤)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = (g.appLE ⊤ ⊤ (le_top.trans g.preimage_top.ge)).hom)
  {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))
  (Φ : P.restriction ComplexShape.embeddingUpNat ⟶
    ((ModuleCat.baseChange Γ(S, ⊤) R).mapHomologicalComplex _).obj (cechModuleComplexNat f ℱ U))

/-- The images in `Γ(T, f'_* Č^k(g'⁻¹ U, g'^* ℱ))` of the basis vectors of `P^k` under `Φ`. -/
noncomputable def mumfordSections (k : ℕ) (i : κ k) :
    Γ((mumfordCech (f' := f') (g' := g') ℱ U).X k, ⊤) :=
  mumfordSectionsMap H ℱ U ⊤ hg k (1 ⊗ₜ (Φ.f k).hom (b k i))

lemma one_tmul_smul (B : Type u) [CommRing B] [Algebra R B] {N : Type u} [AddCommGroup N]
    [Module R N] (r : R) (y : N) :
    (1 : B) ⊗ₜ[R] (r • y) = algebraMap R B r • ((1 : B) ⊗ₜ[R] y) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

lemma tmul_smul_eq_smul_one_tmul (B : Type u) [CommRing B] [Algebra R B] {N : Type u}
    [AddCommGroup N] [Module R N] (c : B) (r : R) (y : N) :
    c ⊗ₜ[R] (r • y) = (c * algebraMap R B r) • ((1 : B) ⊗ₜ[R] y) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_comm]

lemma mumfordSections_d (k : ℕ) (i : κ k) :
    ((mumfordCech (f' := f') (g' := g') ℱ U).d k (k + 1)).app ⊤
        (mumfordSections H ℱ U hg P b Φ k i) =
      ∑ j : κ ((k : ℤ) + 1), (P.dMatrix b k).map (algebraMap R Γ(T, ⊤)) j i •
        mumfordSections H ℱ U hg P b Φ (k + 1) j := by
  have h := ConcreteCategory.congr_hom ((mumfordSectionsHom (R := R) H ℱ U ⊤ hg).comm k (k + 1))
    (1 ⊗ₜ (Φ.f k).hom (b k i))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  change Hom.app _ ⊤ (mumfordSectionsMap H ℱ U ⊤ hg k _) =
    mumfordSectionsMap H ℱ U ⊤ hg (k + 1) (1 ⊗ₜ _) at h
  rw [mumfordSections, h]
  have hΦ := ConcreteCategory.congr_hom (Φ.comm k (k + 1)) (b k i)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hΦ
  change (Φ.f (k + 1)).hom ((P.d k (k + 1 : ℕ)).hom (b k i)) = _ at hΦ
  rw [← hΦ, ← (b ((k : ℤ) + 1)).sum_repr ((P.d k (k + 1 : ℕ)).hom (b k i)), map_sum,
    TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, one_tmul_smul, mumfordSectionsMap_smul, Matrix.map_apply, CochainComplex.dMatrix,
    LinearMap.toMatrix_apply]
  rfl

/-- **The comparison morphism** from the complex of free `𝒪_T`-modules with the matrices of `P`
(in degrees `≥ 0`) to the Čech resolution `f'_* Č(g'⁻¹ U, g'^* ℱ)`: it sends the basis vectors
to the images of the basis of `P` under `Φ`. -/
noncomputable def mumfordFreeHom :
    (freeComplexOfBasis P b (algebraMap R Γ(T, ⊤))).restriction ComplexShape.embeddingUpNat ⟶
      mumfordCech (f' := f') (g' := g') ℱ U :=
  freeComplexHom _ _ _ (mumfordSections H ℱ U hg P b Φ) (mumfordSections_d H ℱ U hg P b Φ)

/-- The comparison morphism on sections over `W`, through the identifications of both sides with
base changes. -/
lemma mumfordFreeHom_sections (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
    [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
    (hgW : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)
    (hR : algebraMap R Γ(T, W) =
      (T.presheaf.map (homOfLE le_top).op).hom.comp (algebraMap R Γ(T, ⊤))) :
    freeSectionsTensorHom P b (algebraMap R Γ(T, ⊤)) W hR ≫
        ((sectionsAb W).mapHomologicalComplex _).map (mumfordFreeHom H ℱ U hg P b Φ) =
      ((forget₂ (ModuleCat.{u} Γ(T, W)) AddCommGrpCat.{u}).mapHomologicalComplex _).map
          (((ModuleCat.baseChange R Γ(T, W)).mapHomologicalComplex _).map Φ) ≫
        mumfordSectionsHom H ℱ U W hgW := by
  ext k : 1
  ext x
  change Hom.app (freeHomOfSections _ (mumfordSections H ℱ U hg P b Φ k)) W
      (freeSectionsTensorEquiv P b W k x) =
    mumfordSectionsMap H ℱ U W hgW k ((Φ.f k).hom.baseChange Γ(T, W) x)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul r p =>
    rw [freeHomOfSections_app, freeSectionsEquivOpens_freeSectionsTensorEquiv,
      LinearMap.baseChange_tmul]
    conv_rhs => rw [← (b k).sum_repr p, map_sum, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, tmul_smul_eq_smul_one_tmul, mumfordSectionsMap_smul, mumfordSections,
      presheaf_map_mumfordSectionsMap_one_tmul H ℱ U W hgW le_top hg (fun r ↦ by rw [hR]; rfl),
      Algebra.TensorProduct.basis_repr_tmul]
    rfl

/-- **The comparison morphism is a quasi-isomorphism**, if `Φ` is a quasi-isomorphism after every
base change: over an affine open `W` of `T` it is identified with `Γ(T, W) ⊗[R] Φ`. -/
theorem quasiIso_mumfordFreeHom [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hΦ : ∀ (B : Type u) [CommRing B] [Algebra R B],
      QuasiIso (((ModuleCat.baseChange R B).mapHomologicalComplex _).map Φ)) :
    QuasiIso (mumfordFreeHom H ℱ U hg P b Φ) := by
  refine quasiIso_of_quasiIso_sectionsAb_nat _ fun x V hx ↦ ?_
  obtain ⟨W, hW, hxW, hWV⟩ := (Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) hx
  refine ⟨W, hxW, hWV, ?_⟩
  let ρ := (T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  letI : Algebra R Γ(T, W) := (ρ.comp (algebraMap R Γ(T, ⊤))).toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(T, W) := (ρ.comp (algebraMap Γ(S, ⊤) Γ(T, ⊤))).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) R Γ(T, W) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change ρ _ = ρ _
    rw [← IsScalarTower.algebraMap_apply]
  have hgW : algebraMap Γ(S, ⊤) Γ(T, W) =
      (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom := by
    rw [RingHom.algebraMap_toAlgebra, hg, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have hsq := mumfordFreeHom_sections H ℱ U hg P b Φ W hgW rfl
  have := isIso_mumfordSectionsHom (R := R) H ℱ U W hgW hW hU
  have := hΦ Γ(T, W)
  rw [← quasiIso_iff_comp_left (freeSectionsTensorHom P b (algebraMap R Γ(T, ⊤)) W rfl), hsq]
  infer_instance

omit [Algebra Γ(S, ⊤) R] in
/-- The finite intersections of the preimages of affine opens are affine over the base. -/
lemma isAffineHom_ι_comp_of_isPullback [IsAffine S] {V : X.Opens} (hV : IsAffineOpen V)
    {V' : Y.Opens} (hV' : V' = g' ⁻¹ᵁ V) : IsAffineHom (V'.ι ≫ f') := by
  subst hV'
  have : IsAffine V := hV
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    ((isPullback_morphismRestrict g' V).paste_vert H).flip inferInstance

/-- **The free complex computes the higher direct images.** In the situation of
`AlgebraicGeometry.Scheme.Modules.quasiIso_mumfordFreeHom`, with `f` separated and `U` a finite
cover of `X` whose finite intersections are affine, the cohomology of the complex of free
`𝒪_T`-modules with the matrices of `P` is `R^q f'_* g'^* ℱ`. -/
theorem nonempty_homology_freeComplexOfBasis_iso [IsAffine S] [IsSeparated f]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
    [HasInjectiveResolutions Y.Modules]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (hU' : ⨆ i, U i = ⊤)
    (hκ : ∀ n < 0, IsEmpty (κ n))
    (hΦ : ∀ (B : Type u) [CommRing B] [Algebra R B],
      QuasiIso (((ModuleCat.baseChange R B).mapHomologicalComplex _).map Φ)) (q : ℕ) :
    Nonempty ((freeComplexOfBasis P b (algebraMap R Γ(T, ⊤))).homology q ≅
      (higherDirectImage f' q).obj ((pullback g').obj ℱ)) := by
  have : IsSeparated f' := MorphismProperty.of_isPullback H.flip inferInstance
  set K := freeComplexOfBasis (Z := T) P b (algebraMap R Γ(T, ⊤))
  have : K.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have := hκ i hi
    exact isZero_free_of_isEmpty _
  have := quasiIso_mumfordFreeHom H ℱ U hg P b Φ hU hΦ
  have hU₂ (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineHom ((⨅ l, g' ⁻¹ᵁ U (y l)).ι ≫ f') :=
    isAffineHom_ι_comp_of_isPullback H (hU k y) (iInf_preimage_eq_preimage_iInf g' U y)
  have hU₃ : ⨆ i, g' ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU', Scheme.Hom.preimage_top]
  exact ⟨HomologicalComplex.homologyMapIso
      (HomologicalComplex.isoExtendRestriction ComplexShape.embeddingUpNat K) (q : ℤ) ≪≫
    (K.restriction ComplexShape.embeddingUpNat).extendHomologyIso ComplexShape.embeddingUpNat
      (j := q) rfl ≪≫
    asIso (HomologicalComplex.homologyMap (mumfordFreeHom H ℱ U hg P b Φ) q) ≪≫
    (higherDirectImageIsoCechResolutionOfIsAffineHom f' (fun i ↦ g' ⁻¹ᵁ U i) hU₂ hU₃
      ((pullback g').obj ℱ) q).symm⟩

end Comparison

end AlgebraicGeometry.Scheme.Modules
