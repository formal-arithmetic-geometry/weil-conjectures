/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!

# Extension of scalars along a quotient by a nonzerodivisor

Let `C` be a closed symmetric monoidal abelian category, `R ⟶ S` a morphism `φ` of commutative
algebra objects and `k` an integer such that
```
0 ⟶ R --k--> R --φ--> S ⟶ 0
```
is short exact in `C`, i.e. `S = R ⧸ k` and `k` is a nonzerodivisor on `R`. For a flat
`R`-module `M`, the sequence
```
0 ⟶ M --k--> M --unit--> S ⊗_R M ⟶ 0
```
is short exact (`Mod.shortExact_extendUnit`): it is the image of the former sequence, regarded
as a sequence of `R`-modules, under the exact functor `- ⊗_R M`, identified through the left
unitor `R ⊗_R M ≅ M` and the identification `S ⊗_R M ≅ φ^* S ⊗_R M` of the underlying objects
(`Mod.extendForgetTensorObjIso`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [IsCommMonObj S] in
/-- The left unitor of the relative tensor product is induced by the action:
`r ⊗ m ↦ r • m`. -/
@[reassoc]
lemma tensorObjπ_leftUnitor_hom_hom [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] (M : Mod C R) :
    tensorObjπ (𝟙_ (Mod C R)) M ≫ (λ_ M).hom.hom = γ[R,M.X] := by
  have h : (λ_ M).hom.hom = ((toBimodRegularIso (R := R)).hom ▷ (toBimod R).obj M).hom ≫
      (λ_ ((toBimod R).obj M)).hom.hom := rfl
  rw [h]
  dsimp only [tensorObjπ]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom, id_whiskerRight]
  erw [Category.id_comp]
  exact colimit.ι_desc _ _

omit [IsCommMonObj R] [IsCommMonObj S] [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] in
/-- The `R`-linear map `R ⟶ φ^* S` underlying `φ`. -/
@[simps!]
def regularToComapRegular : regular R ⟶ (comap φ).obj (regular S) :=
  Hom.mk' φ (by
    change μ[R] ≫ φ = R ◁ φ ≫ φ ▷ S ≫ μ[S]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

omit [SymmetricCategory C] [IsGrothendieckAbelian.{v} C]
  [IsCommMonObj R] in
/-- A short complex of module objects is short exact if its underlying short complex is. -/
lemma shortExact_of_shortExact_map_forget {T : ShortComplex (Mod C R)}
    (h : (T.map (forget R)).ShortExact) : T.ShortExact :=
  have := (forget R).mono_of_mono_map h.mono_f
  have := (forget R).epi_of_epi_map h.epi_g
  ⟨(ShortComplex.exact_map_iff_of_faithful T (forget R)).1 h.exact⟩

/-- Through the left unitor `R ⊗_R M ≅ M`, multiplication by an integer `k` on `R` induces the
multiplication by `k` on `M`. -/
@[reassoc]
lemma zsmul_whiskerRight_hom_leftUnitor_hom_hom (k : ℤ) (M : Mod C R) :
    ((k • 𝟙 (𝟙_ (Mod C R))) ▷ M).hom ≫ (λ_ M).hom.hom = (λ_ M).hom.hom ≫ (k • 𝟙 M.X) := by
  rw [zsmul_whiskerRight, id_whiskerRight]
  simp

omit [MonoidalPreadditive C] in
/-- Through the left unitor `R ⊗_R M ≅ M` and the identification of the underlying objects of
`S ⊗_R M` and `φ^* S ⊗_R M`, the map `φ ⊗_R M` is the unit `M ⟶ S ⊗_R M`. -/
@[reassoc]
lemma regularToComapRegular_whiskerRight_hom_extendForgetTensorObjIso_inv (M : Mod C R) :
    (regularToComapRegular φ ▷ M).hom ≫ (extendForgetTensorObjIso φ M).inv =
      (λ_ M).hom.hom ≫ extendUnitHom φ M := by
  rw [← cancel_epi (tensorObjπ (𝟙_ (Mod C R)) M), tensorObjπ_whiskerRight_assoc,
    tensorObjπ_leftUnitor_hom_hom_assoc, smul_extendUnitHom]
  exact congrArg (φ ▷ M.X ≫ ·) (coequalizer.π_desc _ _)

variable {φ} in
/-- If `k • 1 ≫ φ = 0`, the unit `M ⟶ S ⊗_R M` kills the multiplication by `k`. -/
lemma zsmul_comp_extendUnit (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0) (M : Mod C R) :
    (k • 𝟙 M) ≫ extendUnit φ M = 0 := by
  have w' : (k • 𝟙 (𝟙_ (Mod C R))) ≫ regularToComapRegular φ = 0 := hom_ext _ _ w
  refine hom_ext _ _ ?_
  rw [comp_hom', zsmul_hom, id_hom', extendUnit_hom, ← cancel_epi (λ_ M).hom.hom,
    ← zsmul_whiskerRight_hom_leftUnitor_hom_hom_assoc,
    ← regularToComapRegular_whiskerRight_hom_extendForgetTensorObjIso_inv, ← Category.assoc,
    ← comp_hom', ← comp_whiskerRight, w', MonoidalPreadditive.zero_whiskerRight]
  erw [Limits.zero_comp, Limits.comp_zero]

variable {φ} in
/-- **Reduction modulo a nonzerodivisor**: if `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, then
for every flat `R`-module `M` the sequence `0 ⟶ M --k--> M --unit--> S ⊗_R M ⟶ 0` is short
exact. -/
theorem shortExact_extendUnit (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (M : Mod C R) (hM : ObjectProperty.flat M) :
    (ShortComplex.mk (k • 𝟙 M) (extendUnit φ M) (zsmul_comp_extendUnit k w M)).ShortExact := by
  have w' : (k • 𝟙 (𝟙_ (Mod C R))) ≫ regularToComapRegular φ = 0 := hom_ext _ _ w
  have h₀ : (ShortComplex.mk _ _ w').ShortExact := shortExact_of_shortExact_map_forget hφ
  have := hM.tensorRight.preservesFiniteLimits
  have := hM.tensorRight.preservesFiniteColimits
  have h₁ := (h₀.map_of_exact (tensorRight M)).map_of_exact (forget R)
  refine shortExact_of_shortExact_map_forget (ShortComplex.shortExact_of_iso ?_ h₁)
  exact ShortComplex.isoMk ((forget R).mapIso (λ_ M)) ((forget R).mapIso (λ_ M))
    (extendForgetTensorObjIso φ M).symm (zsmul_whiskerRight_hom_leftUnitor_hom_hom k M).symm
    (regularToComapRegular_whiskerRight_hom_extendForgetTensorObjIso_inv φ M).symm

end CategoryTheory.Mod
