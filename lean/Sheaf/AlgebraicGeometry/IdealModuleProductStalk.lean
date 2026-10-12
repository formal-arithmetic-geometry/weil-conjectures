module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Stalks of ideal-module products, quotients, and powers

Source: literature/stacks-project/modules.tex, Lemmas 01AG and 01CB, as used in
Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The product `𝒥𝓕 ⊆ 𝓕` of a sheaf of ideals `ι : 𝒥 ⟶ 𝒪_X` and an `𝒪_X`-module `𝓕`:
the image of the multiplication map `𝒥 ⊗ 𝓕 ⟶ 𝒪_X ⊗ 𝓕 ≅ 𝓕`, `a ⊗ s ↦ a s`.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealModuleProduct {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : X.Modules :=
  letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  image (ι ▷ F ≫ (λ_ F).hom)

/-- The inclusion `𝒥𝓕 ⟶ 𝓕` of the product of a sheaf of ideals and a module.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealModuleProductι {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    idealModuleProduct ι F ⟶ F :=
  letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  image.ι (ι ▷ F ≫ (λ_ F).hom)

/-- The powers `𝒥ⁿ ⊆ 𝒪_X` of a sheaf of ideals, with their inclusions into `𝒪_X`:
`𝒥¹ = 𝒥` and `𝒥ⁿ⁺¹ = 𝒥 · 𝒥ⁿ ⊆ 𝒥ⁿ ⊆ 𝒪_X`; the value at `0` is `𝒪_X` and is not used.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV
(blueprint: lem-weil-pbc-ideal-module-product-stalk). -/
def idealSheafPower {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ℕ → Σ P : X.Modules, P ⟶ SheafOfModules.unit X.ringCatSheaf
  | 0 => ⟨SheafOfModules.unit X.ringCatSheaf, 𝟙 _⟩
  | 1 => ⟨J, ι⟩
  | n + 2 => ⟨idealModuleProduct ι (idealSheafPower ι (n + 1)).1,
      idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫ (idealSheafPower ι (n + 1)).2⟩

/-- Stalks of ideal sheaves, of products `𝒥𝓕`, of quotients `𝓕/𝒥𝓕` and of powers.
Let `ι : 𝒥 ⟶ 𝒪_X` be a sheaf of ideals, `𝓕` an `𝒪_X`-module and `x ∈ X`; `e` is the
identification of the stalk of `𝒪_X` with `𝒪_{X,x}` (germs to germs) and `I` the image of
`𝒥_x` in `𝒪_{X,x}`. Then `𝒥_x ⟶ 𝒪_{X,x}` and `(𝒥𝓕)_x ⟶ 𝓕_x` are injective,
`(𝒥𝓕)_x = I 𝓕_x`, the stalk of `𝓕 ⟶ 𝓕/𝒥𝓕` induces `𝓕_x / I 𝓕_x ≅ (𝓕/𝒥𝓕)_x`, and for
`n ≥ 1`: `(𝒥ⁿ)_x = Iⁿ`, `(𝒥ⁿ𝓕)_x = Iⁿ 𝓕_x` and `𝓕_x / Iⁿ 𝓕_x ≅ (𝓕/𝒥ⁿ𝓕)_x`.
Source: Stacks Project, Modules, Lemmas 01AG and 01CB; Cohomology of Schemes,
proof of Lemma 0CYV (blueprint: lem-weil-pbc-ideal-module-product-stalk).

Proof: the stalk functor is exact (Modules, Lemma 01AG), so it preserves monomorphisms,
images and cokernels; this gives the injectivity of `𝒥_x ⟶ 𝒪_{X,x}` and of
`(𝒥𝓕)_x ⟶ 𝓕_x`, and `(𝓕/𝒥𝓕)_x = 𝓕_x/(𝒥𝓕)_x`. By Lemma 01CB the stalk of
`𝒥 ⊗ 𝓕 ⟶ 𝓕` is the multiplication `𝒥_x ⊗ 𝓕_x ⟶ 𝓕_x`, whose image is `𝒥_x 𝓕_x`;
this is (2), and (3) follows. For (4) induct on `n`: `(𝒥ⁿ⁺¹)_x = 𝒥_x (𝒥ⁿ)_x =
I · Iⁿ = Iⁿ⁺¹` by (2) applied to `𝓕 = 𝒥ⁿ`, and the remaining two claims are (2) and (3)
for the ideal `𝒥ⁿ`. -/
theorem ideal_module_product_stalk {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] (F : X.Modules) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r) ∧
      let I : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map ι ≫ e.hom).hom
      Function.Injective (S.map ι).hom ∧
      Function.Injective (S.map (idealModuleProductι ι F)).hom ∧
      LinearMap.range (S.map (idealModuleProductι ι F)).hom = I • ⊤ ∧
      (∃ φ : (S.obj F ⧸ I • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F))) ≃ₗ[
          X.presheaf.stalk x] S.obj (cokernel (idealModuleProductι ι F)),
        ∀ m : S.obj F, φ (Submodule.Quotient.mk m) =
          (S.map (cokernel.π (idealModuleProductι ι F))).hom m) ∧
      ∀ n : ℕ, 1 ≤ n →
        let Jn := idealSheafPower ι n
        LinearMap.range (S.map Jn.2 ≫ e.hom).hom = I ^ n ∧
        LinearMap.range (S.map (idealModuleProductι Jn.2 F)).hom = I ^ n • ⊤ ∧
        ∃ φ : (S.obj F ⧸ I ^ n • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F))) ≃ₗ[
            X.presheaf.stalk x] S.obj (cokernel (idealModuleProductι Jn.2 F)),
          ∀ m : S.obj F, φ (Submodule.Quotient.mk m) =
            (S.map (cokernel.π (idealModuleProductι Jn.2 F))).hom m := by
  sorry

end

end AlgebraicGeometry.Scheme
