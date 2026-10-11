/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Local triviality of linear relations in flat sheaves of modules

Let `F` be a flat sheaf of modules over a Noetherian commutative ring `R` on a site. Every
finite system of `R`-linear relations `∑ⱼ eₗⱼ yⱼ = 0` between sections `yⱼ` of `F` over `V` is
*locally trivial*: locally on `V`, the `yⱼ` are `R`-linear combinations `yⱼ = ∑ₘ bⱼₘ zₘ` with
`∑ⱼ eₗⱼ bⱼₘ = 0` (`CategoryTheory.Sheaf.exists_factorization_of_flat`). This is the sheaf
version of the equational criterion for flatness.

The proof tensors the exact sequence `R^t ⟶ R^s ⟶ R^q` (the kernel of `e` being finitely
generated) with `F`. By flatness the resulting sequence of sheaves is exact, and it is the
sheafification of the sequence of presheaves `F(-) ⊗ R^t ⟶ F(-) ⊗ R^s ⟶ F(-) ⊗ R^q`. Exactness
of the sheafification means local exactness of the presheaves
(`CategoryTheory.Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf`), which is the
statement.

## Main results

- `CategoryTheory.Sheaf.imageSieve_mem_of_exact`: in an exact sequence of sheaves of modules,
  a section of the middle term killed by the second map is locally in the image of the first.
- `CategoryTheory.Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf`: the same for a short
  complex of presheaves whose sheafification is exact.
- `CategoryTheory.Sheaf.exists_factorization_of_flat`: linear relations between sections of a
  flat sheaf of modules are locally trivial.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

section LocalExactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type w} [Ring R] [HasSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- **Exact sequences of sheaves are locally exact on sections.** If `S` is an exact short
complex of sheaves of modules and `x` is a section of `S.X₂` over `V` killed by `S.g`, then `x`
is locally in the image of `S.f`. -/
theorem Sheaf.imageSieve_mem_of_exact {S : ShortComplex (Sheaf J (ModuleCat.{w} R))}
    (hS : S.Exact) {V : C} (x : S.X₂.obj.obj (op V)) (hx : S.g.hom.app (op V) x = 0) :
    Presheaf.imageSieve S.f.hom x ∈ J V := by
  have := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.toCycles)).2 this
  -- lift `x` to a section `c` of the cycles, a kernel of `S.g` computed sectionwise
  let E : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
    sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op V)
  let hk := KernelFork.mapIsLimit _ S.cyclesIsKernel E
  let φ : ModuleCat.of R R ⟶ E.obj S.X₂ := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  have hφ : φ ≫ E.map S.g = 0 :=
    ModuleCat.hom_ext (LinearMap.ext_ring (by simpa [φ, E] using hx))
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk φ hφ
  let c : ToType (S.cycles.obj.obj (op V)) := l (1 : R)
  have hc : S.iCycles.hom.app (op V) c = x := by
    have h := ConcreteCategory.congr_hom hl (1 : R)
    simp only [φ, E] at h
    rw [ConcreteCategory.comp_apply] at h
    exact h.trans (by simp)
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J S.toCycles.hom c)
  rintro W f ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have h := congrArg (fun g ↦ g.hom.app (op W) z) S.toCycles_i
  dsimp only at h
  rw [← h, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply, hz,
    NatTrans.naturality_apply, hc]

/-- **Short complexes of presheaves with exact sheafification are locally exact.** If `S` is a
short complex of presheaves of modules whose sheafification is exact and `x` is a section of
`S.X₂` over `V` killed by `S.g`, then `x` is locally in the image of `S.f`. -/
theorem Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf
    {S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{w} R)} (hS : (S.map (presheafToSheaf J _)).Exact)
    {V : C} (x : S.X₂.obj (op V)) (hx : S.g.app (op V) x = 0) :
    Presheaf.imageSieve S.f x ∈ J V := by
  let x' := (toSheafify J S.X₂).app (op V) x
  have hx' : ((presheafToSheaf J _).map S.g).hom.app (op V) x' = 0 := by
    have := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J S.g) (op V)) x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
    rw [← this, hx, map_zero]
  refine J.transitive (Sheaf.imageSieve_mem_of_exact hS x' hx') _ ?_
  rintro W f ⟨z', hz'⟩
  refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J S.X₁) z') _ ?_
  rintro U g ⟨z₀, hz₀⟩
  -- `S.f z₀` and the restriction of `x` agree after sheafification, hence locally
  have heq : (toSheafify J S.X₂).app (op U) (S.f.app (op U) z₀) =
      (toSheafify J S.X₂).app (op U) (S.X₂.map (g ≫ f).op x) := by
    have h₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J S.f) (op U)) z₀
    have h₂ := NatTrans.naturality_apply (toSheafify J S.X₂) (g ≫ f).op x
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₁
    rw [h₁, hz₀, NatTrans.naturality_apply, NatTrans.naturality_apply (toSheafify J S.X₂),
      show (sheafifyMap J S.f).app (op W) z' = _ from hz', op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
    rfl
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J (toSheafify J S.X₂) _ _ heq)
  intro U' h hh
  refine ⟨S.X₁.map h.op z₀, ?_⟩
  change S.X₂.map h.op _ = S.X₂.map h.op _ at hh
  rw [NatTrans.naturality_apply, hh, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [op_comp, Category.assoc]

end LocalExactness

section Flat

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

/-- Coordinates of an element of `M ⊗ R^t` after applying the matrix `b`: the coordinates of
`(1 ⊗ b) z` are `∑ₘ bⱼₘ zₘ`, in terms of the coordinates `zₘ` of `z`. -/
lemma _root_.TensorProduct.piScalarRight_lTensor_mulVecLin {M : Type*} [AddCommGroup M]
    [Module R M] {s t : ℕ} (b : Matrix (Fin s) (Fin t) R) (z : M ⊗[R] (Fin t → R))
    (j : Fin s) :
    TensorProduct.piScalarRight R R M (Fin s) ((b.mulVecLin).lTensor M z) j =
      ∑ m, b j m • TensorProduct.piScalarRight R R M (Fin t) z m := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul x v =>
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]

/-- Coordinates of `∑ⱼ yⱼ ⊗ eⱼ` in `M ⊗ R^s` are the `yⱼ`. -/
lemma _root_.TensorProduct.piScalarRight_sum_tmul_single {M : Type*} [AddCommGroup M]
    [Module R M] {s : ℕ} (y : Fin s → M) :
    TensorProduct.piScalarRight R R M (Fin s) (∑ j, y j ⊗ₜ Pi.single j 1) = y := by
  ext i
  simp [Pi.single_apply]

variable [IsNoetherianRing R] [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

/-- **Linear relations between sections of a flat sheaf are locally trivial.** Let `F` be a
flat sheaf of modules over a Noetherian commutative ring `R`, and let `y : Fin s → F(V)` satisfy
the relations `∑ⱼ eₗⱼ yⱼ = 0`. Then locally on `V` there are a matrix `b` with `e * b = 0` and
sections `z` with `yⱼ = ∑ₘ bⱼₘ zₘ`.

This is the sheaf version of the equational criterion for flatness
(`Module.Flat.iff_forall_exists_factorization`). -/
theorem Sheaf.exists_factorization_of_flat {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) {V : C} {s q : ℕ} (y : Fin s → F.obj.obj (op V))
    (e : Matrix (Fin q) (Fin s) R) (he : ∀ l, ∑ j, e l j • y j = 0) :
    ∃ T ∈ J V, ∀ ⦃W : C⦄ (f : W ⟶ V), T f → ∃ (t : ℕ) (b : Matrix (Fin s) (Fin t) R)
      (z : Fin t → F.obj.obj (op W)), e * b = 0 ∧ ∀ j, F.obj.map f.op (y j) = ∑ m, b j m • z m := by
  classical
  -- the exact sequence `R^t ⟶ R^s ⟶ R^q`, with `R^t ⟶ R^s` generating the kernel of `e`
  let φ := e.mulVecLin
  obtain ⟨t, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (LinearMap.ker φ))
  let b : Matrix (Fin s) (Fin t) R := Matrix.of fun j m ↦ gens m j
  have hb : LinearMap.range b.mulVecLin = LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, ← hgens]
    rfl
  have heb : e * b = 0 := by
    ext l m
    have : gens m ∈ LinearMap.ker φ := hgens ▸ Submodule.subset_span ⟨m, rfl⟩
    have := congrFun (LinearMap.mem_ker.1 this) l
    simpa [φ, b, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  let S₀ := ShortComplex.moduleCatMkOfKerLERange (ModuleCat.ofHom b.mulVecLin)
    (ModuleCat.ofHom φ) (by rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, hb])
  have hS₀ : S₀.Exact := ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ hb
  -- tensoring with `F` keeps it exact, and computes the sheafification of `F(-) ⊗ R^n`
  have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
  have : PreservesFiniteColimits (tensorLeft F) := hF.tensorLeft.2
  let Φ : ModuleCat.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
    Functor.const Cᵒᵖ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _
  let eΦ : constantSheaf J (ModuleCat.{u + 1} R) ⋙ tensorLeft F ≅ Φ :=
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
        (asIso ((sheafificationAdjunction J _).counit.app F)).symm) ≪≫
      Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
        (Sheaf.presheafToSheafCompTensorLeftIso F.obj)
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteColimits _ _
  have hS : (S₀.map Φ).Exact :=
    (ShortComplex.exact_iff_of_iso (S₀.mapNatIso eΦ)).1
      ((hS₀.map (constantSheaf J _)).map (tensorLeft F))
  let Sp := S₀.map (Functor.const Cᵒᵖ ⋙ tensorLeft F.obj)
  -- the section `∑ⱼ yⱼ ⊗ eⱼ` of `F(V) ⊗ R^s` is killed by `e`
  let x : Sp.X₂.obj (op V) := ∑ j, y j ⊗ₜ[R] (Pi.single j 1 : Fin s → R)
  have hx : Sp.g.app (op V) x = 0 := by
    refine (TensorProduct.piScalarRight R R _ (Fin q)).injective ?_
    ext l
    change TensorProduct.piScalarRight R R _ (Fin q) (φ.lTensor _ x) l = 0
    rw [TensorProduct.piScalarRight_lTensor_mulVecLin, TensorProduct.piScalarRight_sum_tmul_single]
    simpa using he l
  refine ⟨_, Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf hS x hx, ?_⟩
  rintro W f ⟨z₀, hz₀⟩
  refine ⟨t, b, TensorProduct.piScalarRight R R _ (Fin t) z₀, heb, fun j ↦ ?_⟩
  have hz := congrArg (fun w ↦ TensorProduct.piScalarRight R R _ (Fin s) w j) hz₀
  change TensorProduct.piScalarRight R R _ (Fin s) (b.mulVecLin.lTensor _ z₀) j =
    TensorProduct.piScalarRight R R _ (Fin s)
      (TensorProduct.map (F.obj.map f.op).hom LinearMap.id x) j at hz
  rw [TensorProduct.piScalarRight_lTensor_mulVecLin] at hz
  rw [hz]
  simp [x, map_sum, Pi.single_apply]

end Flat

end CategoryTheory
