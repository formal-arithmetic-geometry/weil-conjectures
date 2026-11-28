/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Transport of single arrows through coefficient stages

Generic lemmas transporting a derived arrow between single complexes through an exact
realization stage or a derived scalar extension stage, compatibly with the underlying sheaf maps
of the endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the same abelian structure on module sheaves as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

section Generic
open SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C C' D : Type*} [Category C] [Category C'] [Category D]
  [Abelian C] [Abelian C'] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]

/-- Exact transport of a single arrow through an exact functor `G` whose composite with a
forgetful functor `U'` is identified with `U`, after fixing both endpoints of the image. -/
theorem mapSingleArrow_exact_stage (G : C ⥤ C') (U : C ⥤ D) (U' : C' ⥤ D)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U'.Additive] [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (e : G ⋙ U' ≅ U) {P Q : C} {P' Q' : C'} (i : G.obj P ≅ P') (j : G.obj Q ≅ Q')
    (f : (DerivedCategory.singleFunctor C 0).obj P ⟶
      ((DerivedCategory.singleFunctor C 0).obj Q)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor D 0).map (e.inv.app P ≫ U'.map i.hom) ≫
        mapSingleArrow U' 2 ((DerivedCategory.singleFunctor C' 0).map i.inv ≫
          mapSingleArrow G 2 f ≫ ((DerivedCategory.singleFunctor C' 0).map j.hom)⟦(2 : ℤ)⟧') =
      mapSingleArrow U 2 f ≫
        ((DerivedCategory.singleFunctor D 0).map (e.inv.app Q ≫ U'.map j.hom))⟦(2 : ℤ)⟧' := by
  rw [mapSingleArrow_precompose, mapSingleArrow_postcompose, mapSingleArrow_composite]
  have h := mapSingleArrow_natIso U (G ⋙ U') e.symm 2 f
  rw [← Category.assoc, ← Functor.map_comp, Category.assoc, ← U'.map_comp, i.hom_inv_id,
    U'.map_id]
  erw [Category.comp_id]
  erw [reassoc_of% h]
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- Let `L` be a shift-compatible left adjoint of the derived functor of an exact functor `R`.
If two endpoint isomorphisms for `L` have the ordinary maps `m`, `m'` as adjuncts, then
transporting a single arrow by `L` and back by `R` recovers it up to `m` and `m'`. -/
theorem mapSingleArrow_adjunct_stage {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : DerivedCategory A ⥤ DerivedCategory B) [L.CommShift ℤ]
    (adj : L ⊣ R.mapDerivedCategory) [adj.CommShift ℤ] {M M' : A} {N N' : B}
    (i : L.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      (DerivedCategory.singleFunctor B 0).obj N)
    (i' : L.obj ((DerivedCategory.singleFunctor A 0).obj M') ≅
      (DerivedCategory.singleFunctor B 0).obj N')
    (m : M ⟶ R.obj N) (m' : M' ⟶ R.obj N')
    (hm : adj.homEquiv _ _ i.hom = (DerivedCategory.singleFunctor A 0).map m ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)
    (hm' : adj.homEquiv _ _ i'.hom = (DerivedCategory.singleFunctor A 0).map m' ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N')
    (f : (DerivedCategory.singleFunctor A 0).obj M ⟶
      ((DerivedCategory.singleFunctor A 0).obj M')⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor A 0).map m ≫
        mapSingleArrow R 2 (i.inv ≫ L.map f ≫ (L.commShiftIso (2 : ℤ)).hom.app _ ≫
          i'.hom⟦(2 : ℤ)⟧') =
      f ≫ ((DerivedCategory.singleFunctor A 0).map m')⟦(2 : ℤ)⟧' := by
  rw [Adjunction.homEquiv_unit] at hm hm'
  have h₁ : (DerivedCategory.singleFunctor A 0).map m ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N ≫ R.mapDerivedCategory.map i.inv =
      adj.unit.app ((DerivedCategory.singleFunctor A 0).obj M) := by
    rw [← Category.assoc, ← hm, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have h₂ : adj.unit.app ((DerivedCategory.singleFunctor A 0).obj M')⟦(2 : ℤ)⟧' ≫
      (R.mapDerivedCategory.map i'.hom ≫
        (R.mapDerivedCategorySingleFunctor 0).hom.app N')⟦(2 : ℤ)⟧' =
      ((DerivedCategory.singleFunctor A 0).map m')⟦(2 : ℤ)⟧' := by
    rw [← Functor.map_comp, ← Category.assoc, hm', Category.assoc, Iso.inv_hom_id_app]
    exact congrArg _ (Category.comp_id _)
  have h₃ := adj.unit_app_commShiftIso_hom_app ℤ (2 : ℤ)
    ((DerivedCategory.singleFunctor A 0).obj M')
  rw [Functor.commShiftIso_comp_hom_app] at h₃
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁]
  have hn := adj.unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn.symm]
  rw [R.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  rw [reassoc_of% h₃, ← h₂, Functor.map_comp]

/-- Glue an endpoint factorization, a transported-arrow square and a target identification. -/
theorem shifted_glue {B D : Type*} [Category B] [Category D] [HasShift D ℤ] (S : B ⥤ D)
    {I U₀ U₁ L₀ L₁ : B} (a : I ⟶ U₀) (p : U₀ ⟶ U₁) (g : I ⟶ U₁) (q q' : L₀ ⟶ L₁)
    (φ : S.obj U₀ ⟶ (S.obj L₀)⟦(2 : ℤ)⟧) (ψ : S.obj U₁ ⟶ (S.obj L₁)⟦(2 : ℤ)⟧)
    (hE : a ≫ p = g) (hD : S.map p ≫ ψ = φ ≫ (S.map q)⟦(2 : ℤ)⟧') (hF : q = q') :
    S.map g ≫ ψ = S.map a ≫ φ ≫ (S.map q')⟦(2 : ℤ)⟧' := by
  rw [← hE, ← hF, Functor.map_comp, Category.assoc, hD]

/-- Compose two transport squares of shifted arrows along their endpoint maps. -/
theorem single_stage_trans {B D : Type*} [Category B] [Category D] [HasShift D ℤ] (S : B ⥤ D)
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : B} (p₁ : X₀ ⟶ X₁) (p₂ : X₁ ⟶ X₂) (q₁ : Y₀ ⟶ Y₁) (q₂ : Y₁ ⟶ Y₂)
    (g₀ : S.obj X₀ ⟶ (S.obj Y₀)⟦(2 : ℤ)⟧) (g₁ : S.obj X₁ ⟶ (S.obj Y₁)⟦(2 : ℤ)⟧)
    (g₂ : S.obj X₂ ⟶ (S.obj Y₂)⟦(2 : ℤ)⟧)
    (h₁ : S.map p₁ ≫ g₁ = g₀ ≫ (S.map q₁)⟦(2 : ℤ)⟧')
    (h₂ : S.map p₂ ≫ g₂ = g₁ ≫ (S.map q₂)⟦(2 : ℤ)⟧') :
    S.map (p₁ ≫ p₂) ≫ g₂ = g₀ ≫ (S.map (q₁ ≫ q₂))⟦(2 : ℤ)⟧' := by
  rw [Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, Functor.map_comp, Functor.map_comp]

/-- Reassociate a composite of seven morphisms. -/
theorem comp_reassoc_seven {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) (f₅ : X₅ ⟶ X₆)
    (f₆ : X₆ ⟶ X₇) :
    ((f₀ ≫ f₁) ≫ f₂) ≫ f₃ ≫ f₄ ≫ (f₅ ≫ f₆) = f₀ ≫ (((f₁ ≫ f₂) ≫ f₃) ≫ f₄) ≫ f₅ ≫ f₆ := by
  simp only [Category.assoc]

/-- A composite starting at a unit map stays a unit map along unit-preserving steps. -/
theorem comp_unit_chain {C : Type*} [Category C] {I R₀ R₁ R₂ R₃ M R₄ : C}
    (a : I ⟶ R₀) (u : R₀ ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃) (e : R₃ ⟶ M) (k : M ⟶ R₄)
    (η₁ : I ⟶ R₁) (η₂ : I ⟶ R₂) (η₃ : I ⟶ R₃) (w : R₃ ⟶ R₄) (η₄ : I ⟶ R₄)
    (hu : a ≫ u = η₁) (hb : η₁ ≫ b = η₂) (hc : η₂ ≫ c = η₃) (hk : e ≫ k = w)
    (hw : η₃ ≫ w = η₄) : (a ≫ u ≫ b ≫ c ≫ e) ≫ k = η₄ := by
  simp only [Category.assoc]
  rw [hk, reassoc_of% hu, reassoc_of% hb, reassoc_of% hc, hw]

end Generic

section EndpointStage
open SpTowerClasses

/-- An adjoint-normalized endpoint pair transports a single arrow along derived scalar
extension compatibly with the specified underlying semilinear sheaf maps. -/
theorem Endpoint.mapSingleArrow_forget
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}} [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M M' : Modules Λ X} {N N' : Modules Λ' X}
    {m : M.X ⟶ N.X} {m' : M'.X ⟶ N'.X} (e : Endpoint a M N m) (e' : Endpoint a M' N' m')
    (f : (DerivedCategory.singleFunctor (Modules Λ X) 0).obj M ⟶
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M')⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (DiagonalAb X) 0).map m ≫
        mapSingleArrow (Mod.forget (condensedRingObj Λ' X)) 2
          (e.iso.inv ≫ (derivedScalars a X).map f ≫ e'.shift a) =
      mapSingleArrow (Mod.forget (condensedRingObj Λ X)) 2 f ≫
        ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map m')⟦(2 : ℤ)⟧' := by
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have h := mapSingleArrow_adjunct_stage (Mod.comap (coefficientMap a X))
    (derivedScalars a X) adj e.iso e'.iso e.semilinear.hom e'.semilinear.hom
    e.normalization e'.normalization f
  have hh := congrArg (mapSingleArrow (Mod.forget (condensedRingObj Λ X)) (2 : ℤ)) h
  rw [mapSingleArrow_precompose, mapSingleArrow_composite, mapSingleArrow_postcompose] at hh
  have h₁ : (Mod.forget (condensedRingObj Λ X)).map e.semilinear.hom = m :=
    e.semilinear.underlying
  have h₂ : (Mod.forget (condensedRingObj Λ X)).map e'.semilinear.hom = m' :=
    e'.semilinear.underlying
  rw [h₁, h₂] at hh
  unfold Endpoint.shift
  have hF : Mod.comap (coefficientMap a X) ⋙
      Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) =
      Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) := rfl
  convert hh using 3
  all_goals rfl

/-- A derived scalar extension stage followed by an exact realization stage, transported
compatibly with the composite underlying endpoint maps. -/
theorem Endpoint.mapSingleArrow_forget_exact
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}} [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M M' : Modules Λ X} {N N' : Modules Λ' X}
    {m : M.X ⟶ N.X} {m' : M'.X ⟶ N'.X} (e : Endpoint a M N m) (e' : Endpoint a M' N' m')
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    (G : Modules Λ' X ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (U : E ⥤ DiagonalAb X) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (c : G ⋙ U ≅ Mod.forget (condensedRingObj Λ' X)) {P Q : E} (i : G.obj N ≅ P)
    (j : G.obj N' ≅ Q)
    (f : (DerivedCategory.singleFunctor (Modules Λ X) 0).obj M ⟶
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M')⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (DiagonalAb X) 0).map (m ≫ c.inv.app N ≫ U.map i.hom) ≫
        mapSingleArrow U 2 ((DerivedCategory.singleFunctor E 0).map i.inv ≫
          mapSingleArrow G 2 (e.iso.inv ≫ (derivedScalars a X).map f ≫ e'.shift a) ≫
          ((DerivedCategory.singleFunctor E 0).map j.hom)⟦(2 : ℤ)⟧') =
      mapSingleArrow (Mod.forget (condensedRingObj Λ X)) 2 f ≫
        ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map
          (m' ≫ c.inv.app N' ≫ U.map j.hom))⟦(2 : ℤ)⟧' :=
  single_stage_trans _ _ _ _ _ _ _ _ (Endpoint.mapSingleArrow_forget a e e' f)
    (mapSingleArrow_exact_stage G _ U c i j _)

end EndpointStage

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
