/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.HomologyFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TopHomology
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.DimensionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.JacobsonTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.ConstructibleSheaf.FiniteMorphism
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion

/-!
# Dévissage of the degree-wise base change maps

Fix a commutative square `h ≫ f' = e ≫ g` with `h` quasi-compact and quasi-separated,
`p : X' ⟶ X` with `X` of finite type over a field, and a sheaf `𝓕` on `T` killed by the Jacobson
radical `J` of the finite ring `Λ`. Consider the degree-`q` base change maps
(`AlgebraicGeometry.Etale.tensorBaseChangeHomologyMap`)

`τ_q(𝓖) : Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)`, `N = Lf'^* Rg_* 𝓕[0]`,

natural in the sheaf `𝓖` on `X`. The source is `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`
(`AlgebraicGeometry.Etale.singleFunctorTensorRightHomologyIso`), a sheaf killed by `J`. If the
`τ_q` are isomorphisms at the sheaves `π_* Λ / J π_* Λ` for finite morphisms `π`, they are
isomorphisms at every sheaf `𝓖`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeHomologyMap_app_of_cokernel_lowerStar`):

1. both sides only depend on `𝓖 / J 𝓖`, since they are right exact in `𝓖` and kill `J`;
2. `𝓖 / J 𝓖` is a filtered colimit of constructible sheaves killed by `J` (blueprint
   `lem-kun-03sa`), and both sides commute with filtered colimits;
3. a constructible sheaf killed by `J` embeds into a finite sum of sheaves `π_* M` with `M`
   killed by `J`, retracts of sums of copies of `π_* Λ / J π_* Λ`, with constructible cokernel
   killed by `J`; on short exact sequences of sheaves killed by `J`, the sources are exact (the
   tensor product over the semisimple ring `Λ / J`) and the targets form a long exact sequence,
   so dimension shifting (`CategoryTheory.isIso_app_of_dimensionShift`) applies.

This is the `𝔽_ℓ`-vector space case of the proof of blueprint `lem-kun-0f1j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

section General

variable {C D : Type*} [Category C] [Category D]

/-- If a natural transformation is an isomorphism at an object, it is an isomorphism at its
retracts. -/
lemma CategoryTheory.NatTrans.isIso_app_of_retract {S T : C ⥤ D} (τ : S ⟶ T) {A B : C}
    (r : Retract A B) [IsIso (τ.app B)] : IsIso (τ.app A) :=
  ⟨T.map r.i ≫ inv (τ.app B) ≫ S.map r.r, by
    rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, ← S.map_comp, r.retract, S.map_id], by
    rw [Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc, ← T.map_comp,
      r.retract, T.map_id]⟩

/-- A natural transformation between additive functors which is an isomorphism at finitely many
objects is an isomorphism at their biproduct. -/
lemma CategoryTheory.NatTrans.isIso_app_biproduct [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] {S T : C ⥤ D} [S.Additive] [T.Additive]
    (τ : S ⟶ T) {ι : Type} [Finite ι] (f : ι → C) [∀ i, IsIso (τ.app (f i))] :
    IsIso (τ.app (⨁ f)) := by
  have : τ.app (⨁ f) = (S.mapBiproduct f).hom ≫ biproduct.map (fun i ↦ τ.app (f i)) ≫
      (T.mapBiproduct f).inv := by
    rw [← cancel_mono (T.mapBiproduct f).hom]
    ext i
    simp [Functor.mapBiproduct_hom, ← τ.naturality]
  rw [this]
  infer_instance

/-- A natural transformation between functors preserving a colimit, which is an isomorphism on
the diagram, is an isomorphism at the colimit. -/
lemma CategoryTheory.NatTrans.isIso_app_of_isColimit {J : Type*} [Category J] {S T : C ⥤ D}
    (τ : S ⟶ T) {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) [PreservesColimit F S]
    [PreservesColimit F T] (h : ∀ j, IsIso (τ.app (F.obj j))) : IsIso (τ.app c.pt) := by
  let hS := isColimitOfPreserves S hc
  let hT := isColimitOfPreserves T hc
  have : IsIso (Functor.whiskerLeft F τ) := NatIso.isIso_of_isIso_app _
  have e : τ.app c.pt = (hS.coconePointsIsoOfNatIso hT (asIso (Functor.whiskerLeft F τ))).hom :=
    hS.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
      exact τ.naturality (c.ι.app j)
  rw [e]
  infer_instance

/-- A functor preserving the cokernel of a morphism which it sends to zero sends the projection
to the cokernel to an isomorphism. -/
lemma CategoryTheory.Functor.isIso_map_cokernel_π_of_map_eq_zero [Abelian C] [Abelian D]
    (Φ : C ⥤ D) [Φ.PreservesZeroMorphisms] {A B : C} (f : A ⟶ B)
    [PreservesColimit (parallelPair f 0) Φ] (hf : Φ.map f = 0) :
    IsIso (Φ.map (cokernel.π f)) := by
  rw [← π_comp_cokernelComparison]
  have : IsIso (cokernel.π (Φ.map f)) := by
    rw [hf]
    infer_instance
  infer_instance

end General

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Smul

variable {Λ : Type (u + 1)} [CommRing Λ] {C D : Type*} [Category C] [Category D]

/-- The cokernel of `AlgebraicGeometry.Etale.smulDesc I A`, the quotient `A / I A`, is killed by
`I`. -/
lemma smul_id_cokernel_smulDesc [Abelian C] [Linear Λ C] (I : Ideal Λ) [Finite I] (A : C)
    {x : Λ} (hx : x ∈ I) : x • 𝟙 (cokernel (smulDesc I A)) = 0 := by
  rw [← cancel_epi (cokernel.π (smulDesc I A)), comp_zero, Linear.comp_smul, Category.comp_id,
    ← Category.id_comp (cokernel.π _), ← Linear.smul_comp]
  have : x • 𝟙 A = biproduct.ι (fun _ : I ↦ A) ⟨x, hx⟩ ≫ smulDesc I A := by
    simp [smulDesc]
  rw [this, Category.assoc, cokernel.condition, comp_zero]

/-- A quotient of an object killed by `I` is killed by `I`. -/
lemma smul_id_eq_zero_of_epi [Preadditive C] [Linear Λ C] {A B : C} (π : A ⟶ B) [Epi π]
    {x : Λ} (hA : x • 𝟙 A = 0) : x • 𝟙 B = 0 := by
  rw [← cancel_epi π, comp_zero, Linear.comp_smul, Category.comp_id,
    ← Category.id_comp π, ← Linear.smul_comp, hA, zero_comp]

/-- A subobject of an object killed by `I` is killed by `I`. -/
lemma smul_id_eq_zero_of_mono [Preadditive C] [Linear Λ C] {A B : C} (ι : A ⟶ B) [Mono ι]
    {x : Λ} (hB : x • 𝟙 B = 0) : x • 𝟙 A = 0 := by
  rw [← cancel_mono ι, zero_comp, Linear.smul_comp, Category.id_comp,
    ← Category.comp_id ι, ← Linear.comp_smul, hB, comp_zero]

/-- A retract of an object killed by `x` is killed by `x`. -/
lemma smul_id_eq_zero_of_retract [Preadditive C] [Linear Λ C] {A B : C} (r : Retract A B)
    {x : Λ} (hB : x • 𝟙 B = 0) : x • 𝟙 A = 0 :=
  calc x • 𝟙 A = r.i ≫ (x • 𝟙 B) ≫ r.r := by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, r.retract]
    _ = 0 := by rw [hB, zero_comp, comp_zero]

/-- A biproduct of objects killed by `x` is killed by `x`. -/
lemma smul_id_biproduct_eq_zero [Preadditive C] [Linear Λ C] {ι : Type} [Finite ι]
    [HasFiniteBiproducts C] (f : ι → C) {x : Λ} (hf : ∀ i, x • 𝟙 (f i) = 0) :
    x • 𝟙 (⨁ f) = 0 := by
  ext i
  simp [hf i]

/-- A functor sending the multiplications by the elements of `I` on `A` to zero sends
`AlgebraicGeometry.Etale.smulDesc I A` to zero. -/
lemma Functor.map_smulDesc_eq_zero [Preadditive C] [Preadditive D] [Linear Λ C]
    [HasFiniteBiproducts C] (Φ : C ⥤ D) [Φ.Additive] (I : Ideal Λ) [Finite I] (A : C)
    (hΦ : ∀ x ∈ I, Φ.map (x • 𝟙 A) = 0) : Φ.map (smulDesc I A) = 0 := by
  have := Fintype.ofFinite I
  rw [smulDesc, biproduct.desc_eq, Φ.map_sum]
  exact Finset.sum_eq_zero fun x _ ↦ by rw [Φ.map_comp, hΦ x x.2, comp_zero]

end Smul

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

local notation "𝐌" => ModuleCat.{u + 1} Λ

/-- Tensoring with a sheaf killed by `x` kills the multiplication by `x`. -/
lemma whiskerRight_smul_id_eq_zero {Z : Scheme.{u}} (A H : Sheaf Z.smallEtaleTopology 𝐌)
    {x : Λ} (hH : x • 𝟙 H = 0) : (x • 𝟙 A) ▷ H = 0 := by
  rw [MonoidalLinear.smul_whiskerRight, id_whiskerRight, ← MonoidalCategory.whiskerLeft_id,
    ← MonoidalLinear.whiskerLeft_smul, hH, MonoidalPreadditive.whiskerLeft_zero]

/-- The semisimplicity of `Λ ⧸ J` for the Jacobson radical `J` of the finite ring `Λ`. -/
instance isSemisimpleRing_quotient_jacobson : IsSemisimpleRing (Λ ⧸ Ring.jacobson Λ) :=
  inferInstance

variable {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
  (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (𝓕 : Sheaf T.smallEtaleTopology 𝐌)

/-- The sheaf `Hᵠ(τ^{≤q} N)` on `X'`, `N = Lf'^* Rg_* 𝓕[0]`. -/
noncomputable abbrev tensorBaseChangeHomologySheaf (q : ℤ) : Sheaf X'.smallEtaleTopology 𝐌 :=
  (DerivedCategory.homologyFunctor _ q).obj
    ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex Λ f' g 𝓕))

/-- The source of the degree-`q` base change map is `𝓖 ↦ p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologySourceIso (q : ℤ) :
    tensorBaseChangeHomologySource Λ p f' g 𝓕 q ≅
      (p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso 𝐌 p) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (p)^*[𝐌]
      (singleFunctorTensorRightHomologyIso
        ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex Λ f' g 𝓕)) q)

/-- The degree-`q` base change map with the source `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologyMap' (q : ℤ) :
    (p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q) ⟶
      tensorBaseChangeHomologyTarget Λ p h e 𝓕 q :=
  (tensorBaseChangeHomologySourceIso Λ p f' g 𝓕 q).inv ≫
    tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q

lemma isIso_tensorBaseChangeHomologyMap'_app_iff (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology 𝐌) :
    IsIso ((tensorBaseChangeHomologyMap' Λ p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app 𝓖) := by
  rw [tensorBaseChangeHomologyMap', NatTrans.comp_app, isIso_comp_left_iff]

variable {𝓕} in
/-- The complex `N = Lf'^* Rg_* 𝓕[0]` is killed by every element killing `𝓕`. -/
lemma smul_id_tensorBaseChangeComplex {x : Λ} (hx : x • 𝟙 𝓕 = 0) :
    x • 𝟙 (tensorBaseChangeComplex Λ f' g 𝓕) = 0 := by
  rw [tensorBaseChangeComplex, ← Functor.map_id, ← Functor.map_id, ← Functor.map_id,
    ← Functor.map_smul, ← Functor.map_smul, ← Functor.map_smul, hx, Functor.map_zero,
    Functor.map_zero, Functor.map_zero]

variable {𝓕} in
/-- The sheaf `Hᵠ(τ^{≤q} N)` is killed by every element killing `𝓕`. -/
lemma smul_id_tensorBaseChangeHomologySheaf {x : Λ} (hx : x • 𝟙 𝓕 = 0) (q : ℤ) :
    x • 𝟙 (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q) = 0 := by
  let N := tensorBaseChangeComplex Λ f' g 𝓕
  have : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app N)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLEι_app N q q le_rfl
  let i := asIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app N))
  have hN : x • 𝟙 ((DerivedCategory.homologyFunctor _ q).obj N) = 0 := by
    rw [← Functor.map_id, ← Functor.map_smul, smul_id_tensorBaseChangeComplex Λ f' g hx,
      Functor.map_zero]
  apply smul_id_eq_zero_of_mono i.hom hN

/-- The complex `N = Lf'^* Rg_* 𝓕[0]` is concentrated in degrees `≥ 0`. -/
instance isGE_tensorBaseChangeComplex : (tensorBaseChangeComplex Λ f' g 𝓕).IsGE 0 := by
  have : (R((g)_*[𝐌]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)).IsGE 0 :=
    ((g)_*[𝐌]).isGE_rightDerivedFunctor_obj _ 0
  exact isGE_leftDerivedUpperStar_obj f' _ 0

end Etale

end AlgebraicGeometry
