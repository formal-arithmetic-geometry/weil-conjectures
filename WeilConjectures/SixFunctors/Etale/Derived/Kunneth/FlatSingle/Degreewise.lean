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

/-- Tensoring with a sheaf is right exact. -/
instance preservesFiniteColimits_tensorRight_sheaf {Z : Scheme.{u}}
    (H : Sheaf Z.smallEtaleTopology 𝐌) : PreservesFiniteColimits (tensorRight H) :=
  preservesFiniteColimits_tensorRight H

/-- On short exact sequences of sheaves on `X` whose middle term is killed by the Jacobson radical,
the functor `𝓖 ↦ p^* 𝓖 ⊗ H` is exact, for any sheaf `H` on `X'`. -/
lemma exact_upperStar_tensorRight (H : Sheaf X'.smallEtaleTopology 𝐌)
    (S : ShortComplex (Sheaf X.smallEtaleTopology 𝐌)) (hS : S.ShortExact)
    (hS₂ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 S.X₂ = 0) :
    Mono (((p)^*[𝐌] ⋙ tensorRight H).map S.f) ∧ Epi (((p)^*[𝐌] ⋙ tensorRight H).map S.g) ∧
      (S.map ((p)^*[𝐌] ⋙ tensorRight H)).Exact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨?_, inferInstance, hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance⟩
  exact Sheaf.mono_whiskerRight_of_smul_eq_zero_of_ideal (Ring.jacobson Λ) ((p)^*[𝐌].map S.f)
    (fun x hx ↦ by rw [← Functor.map_id, ← Functor.map_smul, hS₂ x hx, Functor.map_zero]) H

/-- On short exact sequences of sheaves on `X` whose middle term is killed by the Jacobson radical,
the functors `𝓖 ↦ Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` form a long exact sequence. -/
lemma exists_δ_tensorBaseChangeHomologyTarget
    (S : ShortComplex (Sheaf X.smallEtaleTopology 𝐌)) (hS : S.ShortExact)
    (hS₂ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 S.X₂ = 0) (q : ℤ) :
    ∃ (δ : (tensorBaseChangeHomologyTarget Λ p h e 𝓕 (q - 1)).obj S.X₃ ⟶
        (tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).obj S.X₁)
      (hδ : δ ≫ (tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).map S.f = 0),
      (tensorBaseChangeHomologyTarget Λ p h e 𝓕 (q - 1)).map S.g ≫ δ = 0 ∧
        (ShortComplex.mk δ _ hδ).Exact := by
  let Ψ := (p)^*[𝐌] ⋙ (h)^*[𝐌] ⋙ tensorRight ((e)^*[𝐌].obj 𝓕)
  have := hS.mono_f
  have := hS.epi_g
  have : Mono (S.map Ψ).f :=
    Sheaf.mono_whiskerRight_of_smul_eq_zero_of_ideal (Ring.jacobson Λ)
      ((h)^*[𝐌].map ((p)^*[𝐌].map S.f))
      (fun x hx ↦ by
        rw [← Functor.map_id, ← Functor.map_id, ← Functor.map_smul, ← Functor.map_smul,
          hS₂ x hx, Functor.map_zero, Functor.map_zero]) _
  have : Epi (S.map Ψ).g := inferInstanceAs (Epi (Ψ.map S.g))
  have hS' : (S.map Ψ).ShortExact :=
    ⟨hS.exact.map_of_epi_of_preservesCokernel Ψ hS.epi_g inferInstance⟩
  let T := R((h)_*[𝐌]).mapTriangle.obj hS'.singleTriangle
  have hT : T ∈ distTriang _ := R((h)_*[𝐌]).map_distinguished _ hS'.singleTriangle_distinguished
  exact ⟨DerivedCategory.HomologySequence.δ T (q - 1) q (by lia),
    DerivedCategory.HomologySequence.δ_comp T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.comp_δ T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.exact₁ T hT (q - 1) q (by lia)⟩

/-- The target `Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologyTarget_obj {q : ℤ} (hq : q < 0)
    (A : Sheaf X.smallEtaleTopology 𝐌) :
    IsZero ((tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).obj A) := by
  have := ((h)_*[𝐌]).isGE_rightDerivedFunctor_obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((h)^*[𝐌].obj ((p)^*[𝐌].obj A) ⊗ (e)^*[𝐌].obj 𝓕)) 0
  exact (R((h)_*[𝐌]).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((h)^*[𝐌].obj ((p)^*[𝐌].obj A) ⊗ (e)^*[𝐌].obj 𝓕))).isZero_of_isGE 0 q hq

/-- The sheaf `Hᵠ(τ^{≤q} N)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologySheaf {q : ℤ} (hq : q < 0) :
    IsZero (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q) := by
  let N := tensorBaseChangeComplex Λ f' g 𝓕
  have : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app N)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLEι_app N q q le_rfl
  exact (N.isZero_of_isGE 0 q hq).of_iso
    (asIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app N)))

/-- Dimension shifting: if the degree-wise base change maps are isomorphisms at the sheaves
`π_* Λ / J π_* Λ` for finite morphisms `π`, they are isomorphisms at every constructible sheaf
killed by the Jacobson radical `J`, on `X` of finite type over a field. -/
theorem isIso_tensorBaseChangeHomologyMap_app_of_isConstructibleSheaf {K : Type u} [Field K]
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0)
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π] (q : ℤ),
      IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[𝐌].obj (𝟙_ _))))))
    (q : ℤ) (A : Sheaf X.smallEtaleTopology 𝐌) [IsConstructibleSheaf A]
    (hA : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 A = 0) :
    IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app A) := by
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  let τ := tensorBaseChangeHomologyMap' Λ p h e f' g w 𝓕
  -- the sheaves `π_* M`, `M` finite and killed by `J`, are good
  have hπ : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π] (M : 𝐌) [Finite M]
      (_ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0),
      (∀ x ∈ Ring.jacobson Λ, x • 𝟙 ((π)_*[𝐌].obj
        ((constantSheaf Xᵢ.smallEtaleTopology 𝐌).obj M)) = 0) ∧
      ∀ q, IsIso ((τ q).app ((π)_*[𝐌].obj ((constantSheaf Xᵢ.smallEtaleTopology 𝐌).obj M))) := by
    intro Xᵢ π _ M _ hM
    obtain ⟨m, ⟨r⟩⟩ := exists_retract_lowerStar_constantSheaf_of_smul_eq_zero Λ π M hM
    refine ⟨fun x hx ↦ smul_id_eq_zero_of_retract r
      (smul_id_biproduct_eq_zero _ fun _ ↦ smul_id_cokernel_smulDesc _ _ hx), fun q ↦ ?_⟩
    have : IsIso ((τ q).app (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[𝐌].obj (𝟙_ _))))) :=
      (isIso_tensorBaseChangeHomologyMap'_app_iff Λ p h e f' g w 𝓕 q _).2 (hgood π q)
    have := NatTrans.isIso_app_biproduct (τ q)
      (fun _ : Fin m ↦ cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[𝐌].obj (𝟙_ _))))
    exact NatTrans.isIso_app_of_retract (τ q) r
  refine (isIso_tensorBaseChangeHomologyMap'_app_iff Λ p h e f' g w 𝓕 q A).1 ?_
  refine isIso_app_of_dimensionShift (D := Sheaf X'.smallEtaleTopology 𝐌)
    (fun A ↦ IsConstructibleSheaf A ∧ ∀ x ∈ Ring.jacobson Λ, x • 𝟙 A = 0)
    (fun A ↦ (∀ x ∈ Ring.jacobson Λ, x • 𝟙 A = 0) ∧ ∀ q, IsIso ((τ q).app A))
    (fun q ↦ (p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q))
    (fun q ↦ tensorBaseChangeHomologyTarget Λ p h e 𝓕 q) τ ?_ (fun q A hA ↦ hA.2 q) ?_ q A
    ⟨inferInstance, hA⟩
  · intro q hq A _
    have h₁ : IsZero (((p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q)).obj A) :=
      (IsZero.iff_id_eq_zero _).2 (by
        dsimp
        rw [← MonoidalCategory.whiskerLeft_id,
          (isZero_tensorBaseChangeHomologySheaf Λ f' g 𝓕 hq).eq_of_src (𝟙 _) 0,
          MonoidalPreadditive.whiskerLeft_zero])
    exact ⟨0, h₁.eq_of_src _ _,
      (isZero_tensorBaseChangeHomologyTarget_obj Λ p h e 𝓕 hq A).eq_of_src _ _⟩
  · rintro A ⟨hAc, hAJ⟩
    obtain ⟨r, Y, π, hπfin, M, hMfin, hMJ, φ, hφ⟩ :=
      exists_mono_biproduct_lowerStar_of_smul_eq_zero Λ a A hAJ
    let fB := fun i ↦ (π i)_*[𝐌].obj ((constantSheaf (Y i).smallEtaleTopology 𝐌).obj (M i))
    have hB : ∀ i, (∀ x ∈ Ring.jacobson Λ, x • 𝟙 (fB i) = 0) ∧ ∀ q, IsIso ((τ q).app (fB i)) :=
      fun i ↦ hπ (π i) (M i) (hMJ i)
    have hBJ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 (⨁ fB) = 0 :=
      fun x hx ↦ smul_id_biproduct_eq_zero _ fun i ↦ (hB i).1 x hx
    have hBτ : ∀ q, IsIso ((τ q).app (⨁ fB)) := fun q ↦ by
      have := fun i ↦ (hB i).2 q
      exact NatTrans.isIso_app_biproduct (τ q) fB
    have : ∀ i, IsConstructibleSheaf (fB i) := fun i ↦ by
      have : Module.Finite Λ (M i) := Module.Finite.of_finite
      have := Scheme.isConstructibleSheaf_constantSheaf (X := Y i) (M i)
      exact Scheme.IsConstructibleSheaf.lowerStar_of_isFinite (π i) _
    have : IsConstructibleSheaf (⨁ fB) := IsConstructibleSheaf.biproduct fB
    have : IsConstructibleSheaf (cokernel φ) := IsConstructibleSheaf.cokernel φ
    let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ)) inferInstance inferInstance
    refine ⟨⨁ fB, cokernel φ, φ, cokernel.π φ, cokernel.condition φ, ⟨hBJ, hBτ⟩,
      ⟨inferInstance, fun x hx ↦ smul_id_eq_zero_of_epi (cokernel.π φ) (hBJ x hx)⟩,
      fun q ↦ ?_⟩
    obtain ⟨h₁, h₂, h₃⟩ := exact_upperStar_tensorRight Λ p
      (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q) S hS hBJ
    obtain ⟨δ, hδ, h₄, h₅⟩ := exists_δ_tensorBaseChangeHomologyTarget Λ p h e 𝓕 S hS hBJ q
    exact ⟨h₁, h₂, h₃, δ, hδ, h₄, h₅⟩

/-- The degree-`q` base change map at a sheaf `𝓖` is an isomorphism if and only if it is one at
`𝓖 / J 𝓖`: both sides are right exact in `𝓖` and kill the Jacobson radical `J`. -/
lemma isIso_tensorBaseChangeHomologyMap_app_iff_cokernel_smulDesc
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0) (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology 𝐌) :
    IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) 𝓖))) := by
  rw [← isIso_tensorBaseChangeHomologyMap'_app_iff, ← isIso_tensorBaseChangeHomologyMap'_app_iff]
  let τ := tensorBaseChangeHomologyMap' Λ p h e f' g w 𝓕 q
  let π := cokernel.π (smulDesc (Ring.jacobson Λ) 𝓖)
  let Φ := (p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q)
  let Ψ := (p)^*[𝐌] ⋙ (h)^*[𝐌] ⋙ tensorRight ((e)^*[𝐌].obj 𝓕)
  have hΦ : IsIso (Φ.map π) := Functor.isIso_map_cokernel_π_of_map_eq_zero Φ _
    (Functor.map_smulDesc_eq_zero Φ _ _ fun x hx ↦ by
      change (p)^*[𝐌].map (x • 𝟙 𝓖) ▷ _ = 0
      rw [Functor.map_smul, Functor.map_id]
      exact whiskerRight_smul_id_eq_zero Λ _ _
        (smul_id_tensorBaseChangeHomologySheaf Λ f' g (h𝓕 x hx) q))
  have hΨ : IsIso (Ψ.map π) := Functor.isIso_map_cokernel_π_of_map_eq_zero Ψ _
    (Functor.map_smulDesc_eq_zero Ψ _ _ fun x hx ↦ by
      change (h)^*[𝐌].map ((p)^*[𝐌].map (x • 𝟙 𝓖)) ▷ _ = 0
      rw [Functor.map_smul, Functor.map_id, Functor.map_smul, Functor.map_id]
      exact whiskerRight_smul_id_eq_zero Λ _ _ (by
        rw [← Functor.map_id, ← Functor.map_smul, h𝓕 x hx, Functor.map_zero]))
  have hT : IsIso ((tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).map π) :=
    inferInstanceAs (IsIso ((DerivedCategory.singleFunctor _ 0 ⋙ R((h)_*[𝐌]) ⋙
      DerivedCategory.homologyFunctor _ q).map (Ψ.map π)))
  have hn := τ.naturality π
  constructor
  · intro _
    have : IsIso (Φ.map π ≫ τ.app _) := by rw [hn]; infer_instance
    exact IsIso.of_isIso_comp_left (Φ.map π) _
  · intro _
    have : IsIso (τ.app 𝓖 ≫ (tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).map π) := by
      rw [← hn]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((tensorBaseChangeHomologyTarget Λ p h e 𝓕 q).map π)

/-- If the degree-wise base change maps are isomorphisms at the sheaves `π_* Λ / J π_* Λ` for
finite morphisms `π`, they are isomorphisms at every sheaf, on `X` of finite type over a field
and for `h` quasi-compact and quasi-separated. -/
theorem isIso_tensorBaseChangeHomologyMap_app_of_cokernel_lowerStar [QuasiCompact h]
    [QuasiSeparated h] {K : Type u} [Field K]
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0)
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π] (q : ℤ),
      IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app
        (cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[𝐌].obj (𝟙_ _))))))
    (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology 𝐌) :
    IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app 𝓖) := by
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian a }
  rw [isIso_tensorBaseChangeHomologyMap_app_iff_cokernel_smulDesc Λ p h e f' g w 𝓕 h𝓕,
    ← isIso_tensorBaseChangeHomologyMap'_app_iff]
  let Q := cokernel (smulDesc (Ring.jacobson Λ) 𝓖)
  have hQ : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 Q = 0 := fun x hx ↦ smul_id_cokernel_smulDesc _ _ hx
  obtain ⟨I, _, _, D, c, hc, hD, hmono, ⟨hcol⟩⟩ := exists_isColimit_isConstructibleSheaf Q
  have : PreservesColimitsOfShape I
      ((p)^*[𝐌] ⋙ tensorRight (tensorBaseChangeHomologySheaf Λ f' g 𝓕 q)) := inferInstance
  have := preservesColimitsOfShape_singleFunctor_rightDerivedLowerStar Λ h q I
  have : PreservesColimitsOfShape I (tensorBaseChangeHomologyTarget Λ p h e 𝓕 q) :=
    inferInstanceAs (PreservesColimitsOfShape I ((p)^*[𝐌] ⋙ (h)^*[𝐌] ⋙
      tensorRight ((e)^*[𝐌].obj 𝓕) ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R((h)_*[𝐌]) ⋙
        DerivedCategory.homologyFunctor _ q))
  have key := NatTrans.isIso_app_of_isColimit (tensorBaseChangeHomologyMap' Λ p h e f' g w 𝓕 q)
    hcol fun j ↦ by
      have := hD j
      rw [isIso_tensorBaseChangeHomologyMap'_app_iff]
      exact isIso_tensorBaseChangeHomologyMap_app_of_isConstructibleSheaf Λ p h e f' g w 𝓕 a h𝓕
        hgood q (D.obj j) fun x hx ↦ by
          have := hmono j
          exact smul_id_eq_zero_of_mono (c.ι.app j) (hc ▸ hQ x hx)
  rwa [hc] at key

end Etale

end AlgebraicGeometry
