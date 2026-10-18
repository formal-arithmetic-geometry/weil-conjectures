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

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

section General

variable {C D : Type*} [Category C] [Category D]

/-- A natural transformation between additive functors which is an isomorphism at finitely many
objects is an isomorphism at their biproduct. -/
lemma CategoryTheory.NatTrans.isIso_app_biproduct [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] {S T : C ⥤ D} [S.Additive] [T.Additive]
    (τ : S ⟶ T) {ι : Type} [Finite ι] (f : ι → C) [∀ i, IsIso (τ.app (f i))] :
    IsIso (τ.app (⨁ f)) := by
  have : τ.app (⨁ f) = (S.mapBiproduct f ≪≫ biproduct.mapIso (fun i ↦ asIso (τ.app (f i))) ≪≫
      (T.mapBiproduct f).symm).hom := by
    rw [← cancel_mono (T.mapBiproduct f).hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    simp only [Category.assoc, biproduct.mapIso_hom, Functor.mapBiproduct_hom, asIso_hom]
    erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
    exact (τ.naturality _).symm
  rw [this]
  infer_instance

/-- A natural transformation between functors preserving a colimit, which is an isomorphism on
the diagram, is an isomorphism at the colimit. -/
lemma CategoryTheory.NatTrans.isIso_app_of_isColimit {J : Type*} [Category J] {S T : C ⥤ D}
    (τ : S ⟶ T) {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) [PreservesColimit F S]
    [PreservesColimit F T] (h : ∀ j, IsIso (τ.app (F.obj j))) : IsIso (τ.app c.pt) := by
  let hS := isColimitOfPreserves S hc
  let hT := isColimitOfPreserves T hc
  have : ∀ j, IsIso ((Functor.whiskerLeft F τ).app j) := h
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
  have : IsIso (cokernel.π (Φ.map f)) :=
    CokernelCofork.IsColimit.isIso_π _ (colimit.isColimit _) hf
  infer_instance

end General

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] Abelian.hasFiniteBiproducts

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
  refine biproduct.hom_ext _ _ fun i ↦ ?_
  rw [zero_comp, Linear.smul_comp, Category.id_comp, ← Category.comp_id (biproduct.π f i),
    ← Linear.comp_smul, hf i, comp_zero]

/-- A functor sending the multiplications by the elements of `I` on `A` to zero sends
`AlgebraicGeometry.Etale.smulDesc I A` to zero. -/
lemma Functor.map_smulDesc_eq_zero [Preadditive C] [Preadditive D] [Linear Λ C]
    [HasFiniteBiproducts C] (Φ : C ⥤ D) [Φ.Additive] (I : Ideal Λ) [Finite I] (A : C)
    (hΦ : ∀ x ∈ I, Φ.map (x • 𝟙 A) = 0) : Φ.map (smulDesc I A) = 0 := by
  rw [← cancel_epi (Φ.mapBiproduct (fun _ : I ↦ A)).inv, comp_zero]
  refine biproduct.hom_ext' _ _ fun x ↦ ?_
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Φ.map_comp, smulDesc,
    biproduct.ι_desc, hΦ x x.2, comp_zero]

end Smul

section Generic

/-! ### Constructions for a general coefficient category -/

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (𝓕 : Sheaf T.smallEtaleTopology A)

/-- The sheaf `Hᵠ(τ^{≤q} N)` on `X'`, `N = Lf'^* Rg_* 𝓕[0]`. -/
noncomputable abbrev tensorBaseChangeHomologySheaf (q : ℤ) : Sheaf X'.smallEtaleTopology A :=
  (DerivedCategory.homologyFunctor _ q).obj
    ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex A f' g 𝓕))

/-- The source of the degree-`q` base change map is `𝓖 ↦ p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologySourceIso (q : ℤ) :
    tensorBaseChangeHomologySource A p f' g 𝓕 q ≅
      (p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q) :=
  let M := (DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex A f' g 𝓕)
  let sX := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  let sX' := DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology A) 0
  let rest := tensorRight M ⋙ DerivedCategory.homologyFunctor (Sheaf X'.smallEtaleTopology A) q
  (Functor.associator sX L((p)^*[A]) rest).symm ≪≫
    Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso A p) rest ≪≫
    Functor.associator (p)^*[A] sX' rest ≪≫
    Functor.isoWhiskerLeft (p)^*[A] (singleFunctorTensorRightHomologyIso M q)

/-- The complex `N = Lf'^* Rg_* 𝓕[0]` is concentrated in degrees `≥ 0`. -/
instance isGE_tensorBaseChangeComplex : (tensorBaseChangeComplex A f' g 𝓕).IsGE 0 := by
  have : (R((g)_*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)).IsGE 0 :=
    ((g)_*[A]).isGE_rightDerivedFunctor_obj _ 0
  exact isGE_leftDerivedUpperStar_obj A f' _ 0

/-- The sheaf `Hᵠ(τ^{≤q} N)` is isomorphic to `Hᵠ(N)`. -/
noncomputable def tensorBaseChangeHomologySheafIso (q : ℤ) :
    tensorBaseChangeHomologySheaf A f' g 𝓕 q ≅
      (DerivedCategory.homologyFunctor _ q).obj (tensorBaseChangeComplex A f' g 𝓕) :=
  have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
    (tensorBaseChangeComplex A f' g 𝓕) (q + 1) q (by lia)
  have : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex A f' g 𝓕))) := by
    rw [← DerivedCategory.TStructure.t.truncLEIsoTruncLT_hom_ι_app q (q + 1) rfl, Functor.map_comp]
    infer_instance
  asIso ((DerivedCategory.homologyFunctor _ q).map
    ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex A f' g 𝓕)))

/-- The sheaf `Hᵠ(τ^{≤q} N)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologySheaf {q : ℤ} (hq : q < 0) :
    IsZero (tensorBaseChangeHomologySheaf A f' g 𝓕 q) :=
  ((tensorBaseChangeComplex A f' g 𝓕).isZero_of_isGE 0 q hq).of_iso
    (tensorBaseChangeHomologySheafIso A f' g 𝓕 q)

/-- The source `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologySource'_obj {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsZero (((p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q)).obj 𝓖) :=
  (IsZero.iff_id_eq_zero _).2 (by
    dsimp
    rw [← MonoidalCategory.whiskerLeft_id,
      (isZero_tensorBaseChangeHomologySheaf A f' g 𝓕 hq).eq_of_src (𝟙 _) 0,
      MonoidalPreadditive.whiskerLeft_zero])

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- The target `Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` vanishes in negative degrees. -/
lemma isZero_tensorBaseChangeHomologyTarget_obj {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsZero ((tensorBaseChangeHomologyTarget A p h e 𝓕 q).obj 𝓖) := by
  have := ((h)_*[A]).isGE_rightDerivedFunctor_obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((tensorBaseChangeHomologyTargetSheaf A p h e 𝓕).obj 𝓖)) 0
  exact (R((h)_*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((tensorBaseChangeHomologyTargetSheaf A p h e 𝓕).obj 𝓖))).isZero_of_isGE 0 q hq

variable [Etale.UpperStarPreservesFlat A]

/-- The degree-`q` base change map with the source `p^* 𝓖 ⊗ Hᵠ(τ^{≤q} N)`. -/
noncomputable def tensorBaseChangeHomologyMap' (q : ℤ) :
    (p)^*[A] ⋙ tensorRight (tensorBaseChangeHomologySheaf A f' g 𝓕 q) ⟶
      tensorBaseChangeHomologyTarget A p h e 𝓕 q :=
  (tensorBaseChangeHomologySourceIso A p f' g 𝓕 q).inv ≫
    tensorBaseChangeHomologyMap A p h e f' g w 𝓕 q

lemma isIso_tensorBaseChangeHomologyMap'_app_iff (q : ℤ) (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((tensorBaseChangeHomologyMap A p h e f' g w 𝓕 q).app 𝓖) := by
  rw [tensorBaseChangeHomologyMap', NatTrans.comp_app, isIso_comp_left_iff]

/-- The degree-wise base change map is an isomorphism in negative degrees. -/
lemma isIso_tensorBaseChangeHomologyMap'_app_of_neg {q : ℤ} (hq : q < 0)
    (𝓖 : Sheaf X.smallEtaleTopology A) :
    IsIso ((tensorBaseChangeHomologyMap' A p h e f' g w 𝓕 q).app 𝓖) :=
  ⟨0, (isZero_tensorBaseChangeHomologySource'_obj A p f' g 𝓕 hq 𝓖).eq_of_src _ _,
    (isZero_tensorBaseChangeHomologyTarget_obj A p h e 𝓕 hq 𝓖).eq_of_src _ _⟩

omit [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A] in
/-- If `𝓖 ↦ h^* p^* 𝓖 ⊗ e^* 𝓕` sends a short exact sequence to a short exact sequence, the
functors `𝓖 ↦ Rᵠh_*(h^* p^* 𝓖 ⊗ e^* 𝓕)` form a long exact sequence on it. -/
lemma exists_δ_tensorBaseChangeHomologyTarget (S : ShortComplex (Sheaf X.smallEtaleTopology A))
    (hS : (S.map (tensorBaseChangeHomologyTargetSheaf A p h e 𝓕)).ShortExact) (q : ℤ) :
    ∃ (δ : (tensorBaseChangeHomologyTarget A p h e 𝓕 (q - 1)).obj S.X₃ ⟶
        (tensorBaseChangeHomologyTarget A p h e 𝓕 q).obj S.X₁)
      (hδ : δ ≫ (tensorBaseChangeHomologyTarget A p h e 𝓕 q).map S.f = 0),
      (tensorBaseChangeHomologyTarget A p h e 𝓕 (q - 1)).map S.g ≫ δ = 0 ∧
        (ShortComplex.mk δ _ hδ).Exact := by
  let T := R((h)_*[A]).mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang _ := R((h)_*[A]).map_distinguished _ hS.singleTriangle_distinguished
  exact ⟨DerivedCategory.HomologySequence.δ T (q - 1) q (by lia),
    DerivedCategory.HomologySequence.δ_comp T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.comp_δ T hT (q - 1) q (by lia),
    DerivedCategory.HomologySequence.exact₁ T hT (q - 1) q (by lia)⟩

end Generic

end Etale

end AlgebraicGeometry
