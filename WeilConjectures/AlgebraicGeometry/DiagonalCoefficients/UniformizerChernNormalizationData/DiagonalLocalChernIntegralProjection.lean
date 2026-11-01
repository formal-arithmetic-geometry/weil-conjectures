/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalLocalShiftedAdjunction
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralBoundary
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport

/-! # Integral comparison for a local uniformizer reduction -/

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
namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

private theorem whisker_eqToIso_inv_app_map_heq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S T : C ⥤ D} (F : D ⥤ E) (h : S = T) (M : C)
    {N : D} (f : S.obj M ⟶ N) :
    HEq ((Functor.isoWhiskerRight (eqToIso h) F).inv.app M ≫ F.map f)
      (F.map f) := by
  subst T
  simp

private theorem normalized_iso_transport
    {C : Type*} [Category C] {U U' V V' : C}
    (u : U ≅ U') (v : V ≅ V') {a : U ⟶ V} {b : U' ⟶ V'}
    (h : a = u.hom ≫ b ≫ v.inv) : u.inv ≫ a ≫ v.hom = b := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem normalized_four_squares
    {C D : Type*} [Category C] [Category D] [HasShift D ℤ]
    (S : C ⥤ D) {M₀ M₁ M₂ M₃ M₄ T₀ T₁ T₂ T₃ T₄ : C}
    {q₀ : M₀ ⟶ M₁} {q₁ : M₁ ⟶ M₂} {q₂ : M₂ ⟶ M₃} {q₃ : M₃ ⟶ M₄}
    {r₀ : T₀ ⟶ T₁} {r₁ : T₁ ⟶ T₂} {r₂ : T₂ ⟶ T₃} {r₃ : T₃ ⟶ T₄}
    {a₀ : S.obj M₀ ⟶ (S.obj T₀)⟦(2 : ℤ)⟧}
    {a₁ : S.obj M₁ ⟶ (S.obj T₁)⟦(2 : ℤ)⟧}
    {a₂ : S.obj M₂ ⟶ (S.obj T₂)⟦(2 : ℤ)⟧}
    {a₃ : S.obj M₃ ⟶ (S.obj T₃)⟦(2 : ℤ)⟧}
    {a₄ : S.obj M₄ ⟶ (S.obj T₄)⟦(2 : ℤ)⟧}
    (h₀ : S.map q₀ ≫ a₁ = a₀ ≫ (S.map r₀)⟦(2 : ℤ)⟧')
    (h₁ : S.map q₁ ≫ a₂ = a₁ ≫ (S.map r₁)⟦(2 : ℤ)⟧')
    (h₂ : S.map q₂ ≫ a₃ = a₂ ≫ (S.map r₂)⟦(2 : ℤ)⟧')
    (h₃ : S.map q₃ ≫ a₄ = a₃ ≫ (S.map r₃)⟦(2 : ℤ)⟧') :
    S.map (q₀ ≫ q₁ ≫ q₂ ≫ q₃) ≫ a₄ =
      a₀ ≫ (S.map (r₀ ≫ r₁ ≫ r₂ ≫ r₃))⟦(2 : ℤ)⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [h₃, reassoc_of% h₂, reassoc_of% h₁, reassoc_of% h₀]

private theorem normalized_target_chain
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    {r₀ : X₀ ⟶ X₁} {r₁ : X₁ ⟶ X₂} {r₂ : X₂ ⟶ X₃} {r₃ : X₃ ⟶ X₄}
    {i : X₀ ⟶ X₁} {j : X₀ ⟶ X₂} {p : X₀ ⟶ X₅}
    {f f' : X₅ ⟶ X₄} {e : X₀ ⟶ X₀}
    (h₀ : r₀ = i) (h₁ : i ≫ r₁ = j) (h₂ : j ≫ r₂ ≫ r₃ = p ≫ f)
    (hf : f = f') (he : e = 𝟙 X₀) :
    r₀ ≫ r₁ ≫ r₂ ≫ r₃ = e ≫ p ≫ f' := by
  rw [h₀, ← Category.assoc, h₁, h₂, hf, he, Category.id_comp]

private theorem normalized_square_precompose
    {C D : Type*} [Category C] [Category D] [HasShift D ℤ]
    (S : C ⥤ D) {I M N T P : C}
    (g : I ⟶ M) (i : I ⟶ N) (q : M ⟶ N) (r r' : T ⟶ P)
    (a : S.obj M ⟶ (S.obj T)⟦(2 : ℤ)⟧)
    (b : S.obj N ⟶ (S.obj P)⟦(2 : ℤ)⟧)
    (h : S.map q ≫ b = a ≫ (S.map r)⟦(2 : ℤ)⟧')
    (hg : g ≫ q = i) (hr : r = r') :
    S.map i ≫ b = S.map g ≫ a ≫ (S.map r')⟦(2 : ℤ)⟧' := by
  rw [← hg, Functor.map_comp, Category.assoc, h, hr]

private theorem normalized_scalar_arrow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (a : F ⊣ R.mapDerivedCategory) [a.CommShift ℤ]
    {M T : C} {N P : D}
    (f : F.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj N)
    (g : F.obj ((DerivedCategory.singleFunctor C 0).obj T) ⟶
      (DerivedCategory.singleFunctor D 0).obj P)
    (u : M ⟶ R.obj N) (v : T ⟶ R.obj P)
    (hf : a.homEquiv _ _ f.hom = (DerivedCategory.singleFunctor C 0).map u ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)
    (hg : a.homEquiv _ _ g = (DerivedCategory.singleFunctor C 0).map v ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app P)
    (z : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj T)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor C 0).map u ≫
      mapSingleArrow R (2 : ℤ)
        (f.inv ≫ F.map z ≫ (F.commShiftIso (2 : ℤ)).hom.app _ ≫ g⟦(2 : ℤ)⟧') =
      z ≫ ((DerivedCategory.singleFunctor C 0).map v)⟦(2 : ℤ)⟧' := by
  have h := local_shifted_adjunction F R.mapDerivedCategory a f g z
  rw [hf, hg] at h
  simp only [(shiftFunctor _ (2 : ℤ)).map_comp, Category.assoc] at h
  dsimp only [mapSingleArrow]
  rw [reassoc_of% h]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← (shiftFunctor _ (2 : ℤ)).map_comp
    ((R.mapDerivedCategorySingleFunctor 0).inv.app P)
    ((R.mapDerivedCategorySingleFunctor 0).hom.app P),
    Iso.inv_hom_id_app, (shiftFunctor _ (2 : ℤ)).map_id]
  dsimp only [Functor.comp_obj]
  exact congrArg (fun b ↦ z ≫ b) (Category.comp_id _)

private theorem exact_underlying_arrow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    {H : Type*} [Category H] [Abelian H] [HasDerivedCategory H]
    (F : C ⥤ D) (U : C ⥤ H) (V : D ⥤ H)
    [F.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : F ⋙ V ≅ U) {M T : C} {N P : D}
    (f : F.obj M ≅ N) (g : F.obj T ≅ P)
    (z : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj T)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor H 0).map (e.inv.app M ≫ V.map f.hom) ≫
      mapSingleArrow V (2 : ℤ)
        ((DerivedCategory.singleFunctor D 0).map f.inv ≫ mapSingleArrow F (2 : ℤ) z ≫
          ((DerivedCategory.singleFunctor D 0).map g.hom)⟦(2 : ℤ)⟧') =
    mapSingleArrow U (2 : ℤ) z ≫
      ((DerivedCategory.singleFunctor H 0).map
        (e.inv.app T ≫ V.map g.hom))⟦(2 : ℤ)⟧' := by
  have h := mapSingleArrow_natIso U (F ⋙ V) e.symm (2 : ℤ) z
  simp only [Iso.symm_hom] at h
  rw [mapSingleArrow_precompose, mapSingleArrow_postcompose,
    mapSingleArrow_composite]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (DerivedCategory.singleFunctor H 0).map_comp_assoc
    (V.map f.hom) (V.map f.inv)]
  rw [← V.map_comp, f.hom_inv_id, V.map_id,
    (DerivedCategory.singleFunctor H 0).map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg
    (fun b ↦ b ≫ ((DerivedCategory.singleFunctor H 0).map (V.map g.hom))⟦(2 : ℤ)⟧') h

private theorem source_exact_ext_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {I : D} {M N : C} (g : I ⟶ F.obj M) (e : Ext M N 2)
    (e' : Ext I (F.obj N) 2)
    (a : (DerivedCategory.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧)
    (he : e.hom = a)
    (h : (DerivedCategory.singleFunctor D 0).map g ≫
      SpTowerClasses.mapSingleArrow F (2 : ℤ) a = e'.hom) :
    (Ext.mk₀ g).comp (e.mapExactFunctor F) (zero_add 2) = e' := by
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    DiagonalTrace.mapSingleArrow_ext, he]
  exact h

private theorem normalized_ext_endpoints
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {X' X Y Y' : C} (a : X' ⟶ X) (n : ℕ) (β : Ext X Y n) (b : Y ⟶ Y') :
    (Ext.mk₀CompMk₀ a β b).hom =
      (DerivedCategory.singleFunctor C 0).map a ≫ β.hom ≫
        ((DerivedCategory.singleFunctor C 0).map b)⟦(n : ℤ)⟧' := by
  simp only [Ext.mk₀CompMk₀, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

private theorem scalar_underlying_arrow
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)]
    {M T : Modules R X} {N P : Modules S X}
    {u : M.X ⟶ N.X} {v : T.X ⟶ P.X}
    (f : Endpoint a M N u) (g : Endpoint a T P v)
    (z : (DerivedCategory.singleFunctor (Modules R X) 0).obj M ⟶
      ((DerivedCategory.singleFunctor (Modules R X) 0).obj T)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor _ 0).map u ≫
      mapSingleArrow (Mod.forget _) (2 : ℤ)
        (f.iso.inv ≫ (derivedScalars a X).map z ≫ g.shift a) =
      mapSingleArrow (Mod.forget _) (2 : ℤ) z ≫
        ((DerivedCategory.singleFunctor _ 0).map v)⟦(2 : ℤ)⟧' := by
  let := RootEndpointTranspose.ShiftHelpers.scalarAdjunction_commShift a X
  have h := normalized_scalar_arrow (Mod.comap (coefficientMap a X))
    (derivedScalars a X) (UniformizerSquareData.scalarAdjunction a X)
    f.iso g.iso.hom f.semilinear.hom g.semilinear.hom
    (RootEndpointTranspose.ShiftHelpers.scalarEndpoint_transpose a f)
    (RootEndpointTranspose.ShiftHelpers.scalarEndpoint_transpose a g) z
  have hh := congrArg (fun b ↦ mapSingleArrow (Mod.forget _) (2 : ℤ) b) h
  rw [mapSingleArrow_precompose, mapSingleArrow_postcompose,
    mapSingleArrow_composite] at hh
  change (DerivedCategory.singleFunctor _ 0).map f.semilinear.hom.hom ≫
      mapSingleArrow (Mod.forget _) (2 : ℤ)
        (f.iso.inv ≫ (derivedScalars a X).map z ≫ g.shift a) =
      mapSingleArrow (Mod.forget _) (2 : ℤ) z ≫
        ((DerivedCategory.singleFunctor _ 0).map g.semilinear.hom.hom)⟦(2 : ℤ)⟧' at hh
  simpa only [f.semilinear.underlying, g.semilinear.underlying] using hh

private theorem integer_map_unit (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Functor.LaxMonoidal.ε (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      diagonalCoefficientIntegerMap X R = η[(completedAbFunctor X).obj R] := by
  rw [MonObj.ofIso_one, Functor.obj.η_def]
  simp only [Category.assoc]
  congr 1

private theorem finite_constant_comparison_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Functor.whiskerRight
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A)))
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) ≫
      (finiteConstantAbComparison A X).hom.hom =
    toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A)) := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction (Scheme.ProEt.topology X)
      (ModuleCat.forget₂CoinduceAdj A)
  unfold finiteConstantAbComparison
  change _ ≫ ((constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).hom.app (ModuleCat.of A A)).hom = _
  rw [constantCommuteCompose_hom_app_hom, sheafComposeIso_inv_fac_assoc,
    ← toSheafify_naturality]
  rfl

private theorem site_generator_cast (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    DiagonalTrace.siteIntegralGenerator A X ≫ (finiteConstantAbComparison A X).hom =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        η[AddCommGrpCat.of A] := by
  let castOne : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of A :=
    η[AddCommGrpCat.of A]
  change DiagonalTrace.siteIntegralGenerator A X ≫ (finiteConstantAbComparison A X).hom =
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map castOne
  apply DiagonalTrace.constantAb_ext_one
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [DiagonalTrace.siteIntegralGenerator_section]
  have hc := congr_app (finite_constant_comparison_unit A X)
    (op (Scheme.ProEt.mk (𝟙 X)))
  have hc' := ConcreteCategory.congr_hom hc (1 : A)
  change (ConcreteCategory.hom ((finiteConstantAbComparison A X).hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 X)))))
      ((ConcreteCategory.hom ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.ProEt.mk (𝟙 X))))) (1 : A)) =
    (ConcreteCategory.hom ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app
        (op (Scheme.ProEt.mk (𝟙 X))))) (1 : A) at hc'
  have hn := congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map castOne))
      (op (Scheme.ProEt.mk (𝟙 X)))
  have hn' := ConcreteCategory.congr_hom hn (ULift.up 1)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply,
    Functor.const_map_app] at hn'
  have hη : castOne.hom (ULift.up (1 : ℤ)) = (1 : A) := by
    change (η[AddCommGrpCat.of A]).hom (ULift.up (1 : ℤ)) = (1 : A)
    rw [AddCommGrpCat.ringMonObj_one_apply, Int.cast_one]
  have he := congrArg (fun x : A ↦
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app
        (op (Scheme.ProEt.mk (𝟙 X)))).hom x) hη
  let oneSection := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
      (op (Scheme.ProEt.mk (𝟙 X))) (ULift.up 1)
  change _ = (sheafifyMap (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map castOne)).app (op (Scheme.ProEt.mk (𝟙 X))) oneSection
  simpa only [oneSection, Int.cast_one] using hc'.trans (he.symm.trans hn')

private theorem finite_image_hom (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0)
    (k : Etale.ordinaryFiniteUnit A X ⟶ Etale.p1DecompositionTwist A N hA X 1 2) :
    (DiagonalTrace.finiteEtaleProImage A X N hA
      ((Etale.ordinaryFiniteExtHomEquiv A X (Etale.ordinaryFiniteConstant A X)
        (Scheme.finiteEtaleTateLine X N A hA) 2).symm k)).hom =
      (finiteUnitComparison A X).inv ≫ (geoP1Comparison A X).map k ≫
        (finiteLineComparison A N hA X).hom := by
  have hb : ((Etale.ordinaryFiniteExtHomEquiv A X (Etale.ordinaryFiniteConstant A X)
      (Scheme.finiteEtaleTateLine X N A hA) 2).symm k).hom = k := by
    exact (Etale.ordinaryFiniteExtHomEquiv A X (Etale.ordinaryFiniteConstant A X)
      (Scheme.finiteEtaleTateLine X N A hA) 2).apply_symm_apply k
  rw [DiagonalTrace.finiteEtaleProImage_apply]
  rw [normalized_ext_endpoints]
  simp only [Ext.mapExactFunctor_hom, ShiftedHom.map, Category.assoc]
  rw [hb]
  have hc := eq_of_heq (whisker_eqToIso_inv_app_map_heq (geoP1Comparison A X)
    (Etale.ordinaryFiniteSingleFunctor_eq A X) (Etale.ordinaryFiniteConstant A X) k)
  simp only [finiteUnitComparison, Functor.compIsoApp, finiteSingleComparison,
    finiteLineComparison, Etale.p1DecompositionShiftedComparison,
    DiagonalTrace.finiteEtaleConstantIso, DiagonalTrace.finiteEtaleLineIso,
    finiteConstantComparison, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.refl_hom, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% hc]
  simp only [geoP1Comparison, Functor.map_comp, Nat.cast_ofNat]

private theorem completed_projection_hom (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (z : DiagonalTrace.completedUnit l T ⟶
      (DiagonalTrace.completedLine l T)⟦(2 : ℤ)⟧) :
    letI : HasDerivedCategory.{u + 1} (DiagonalAb T) :=
      DiagonalTraceLocalizations.ab (ℓ := l) (X := T)
    (completedIntegralProjection l T A n hA hT z).hom =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (localCompletedGenerator l T) ≫
        mapSingleArrow (localCompletedForget l T) (2 : ℤ) z ≫
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            ((localCompletedRoots l T).hom ≫
              limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n) ≫
                cartierProRootMap A (l ^ (n + 1)) hA T
                  (pow_pos (Fact.out : l.Prime).pos _) hT))⟦(2 : ℤ)⟧' := by
  let : HasDerivedCategory.{u + 1} (DiagonalAb T) :=
    DiagonalTraceLocalizations.ab (ℓ := l) (X := T)
  unfold completedIntegralProjection
  dsimp only [Ext.hom]
  exact Ext.homEquiv.apply_symm_apply _

private def completedUnderlying (s : UniformizerChernNormalizationData l Y) :
    s.completedP.F ⋙ Mod.forget _ ≅ localCompletedForget l (ProjectiveLine Y) :=
  NatIso.ofComponents (fun M ↦ s.completedP.underlying.app M)
    (by intro M N f; exact s.completedP.underlying.hom.naturality f)

private theorem normalized_source (s : UniformizerChernNormalizationData l Y) :
    localCompletedGenerator l (ProjectiveLine Y) ≫
      (completedUnderlying l Y s).inv.app (SheafOfModules.unit
        (Scheme.purTwistRing (ProjectiveLine Y)
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
      s.completedP.unitIso.hom.hom ≫
      coefficientMap (integralMap l s.E) (ProjectiveLine Y) ≫
      coefficientMap (quotientMap l s.E s.π s.n) (ProjectiveLine Y) ≫
      s.eP.underlying.inv.app (Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (completedResidue l s.E s.π s.n))
          (ProjectiveLine Y))) ≫ (cartierForget _ _).map s.eP.unitIso.hom =
    DiagonalTrace.siteIntegralGenerator
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y) := by
  let X := ProjectiveLine Y
  let A := ULift.{u + 1} (completedResidue l s.E s.π s.n)
  apply (cancel_mono (finiteConstantAbComparison A X).hom).mp
  simp only [Category.assoc]
  rw [s.eP.unit_normalization, site_generator_cast]
  dsimp only [localCompletedGenerator]
  let ε := Functor.LaxMonoidal.ε
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  apply (cancel_epi ε).mp
  dsimp only [ε]
  rw [constant_ab_ε, ← Category.assoc, integer_map_unit]
  let : MonObj ((sfbConstantRing X).obj (RingCat.of A)).X :=
    ((sfbConstantRing X).obj (RingCat.of A)).mon
  have h₀ := unitRealization_one l X s.completedP
  change η[(completedAbFunctor X).obj (Scheme.purTwistZlCompletion X l)] ≫
    (completedUnderlying l Y s).inv.app (SheafOfModules.unit
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≫
        s.completedP.unitIso.hom.hom =
      η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X] at h₀
  have hunit := congrArg (fun f ↦ f ≫
    coefficientMap (integralMap l s.E) X ≫
      coefficientMap (quotientMap l s.E s.π s.n) X ≫ s.eP.coefficient.hom.hom) h₀
  simp only [Category.assoc] at hunit
  have hcoeff := s.eP.coefficient.hom.isMonHom_hom.one_hom
  conv_rhs at hunit =>
    rw [IsMonHom.one_hom_assoc, IsMonHom.one_hom_assoc, hcoeff]
  rw [hunit]
  change Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        η[AddCommGrpCat.of A] =
    Functor.LaxMonoidal.ε (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        η[AddCommGrpCat.of A]
  rw [constant_ab_ε]

/-- The integral image of a scalar-reduced arrow is its actual finite root projection.
This concerns every completed arrow, without any Chern or Kummer hypothesis.

Source: blueprint latest, diagonal tower coefficient changes proof (1), integral and
uniformizer reduction; diagonal tower trace proof (1), the normalized section endpoints.
(blueprint: lem-diagonal-local-chern-integral-projection).

Proof: write the local composite as four successive endpoint-normalized arrows:
completed realization, integral scalar extension, quotient scalar extension, and
finite realization. Naturality of the exact-single comparison gives the underlying
abelian-sheaf squares for the two realizations. The shifted scalar adjunction and
Endpoint.normalization give the other two squares. Compose these four squares.

On the source, the completed unit realization carries the integral generator to
one. Both scalar coefficient maps and the specified finite coefficient isomorphism
preserve one. The finite unit normalization and the constant-sheaf comparison
therefore identify the composite source arrow with siteIntegralGenerator.

On the target, completedP.line_normalization identifies the first arrow with the
integral root map. The integral-root transition formula followed by the quotient
line normalization identifies the composite with the n-th root projection followed
by finiteRoots.toLine. The canonical finite-root comparison identifies this last
map with cartierProRootMap.

The cached exact-single comparison identifies the finite image of the class
represented by k with the fourth normalized arrow, using hk. The integral-image
formula then identifies its underlying integral Ext class with the composite square
precomposed by the integral generator. Ext.hom is injective, so the resulting
identity of derived arrows proves the stated equality. No nonzero assumption is
used: zero arrows, the zero coefficient ring, n=0, and the empty scheme are covered. -/
theorem localChern_transport_integral_projection
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison (ProjectiveLine Y)).inv
      ((Etale.ordinaryFiniteClass
        (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)
        (Scheme.finiteEtaleTateLine (ProjectiveLine Y) (l ^ (s.n + 1))
          (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA) 2
          (LocalFiniteArrow.toHom l Y s k)).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} (ProjectiveLine Y)))
      ((forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).hom.app (Scheme.finiteEtaleTateLine (ProjectiveLine Y)
          (l ^ (s.n + 1)) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA)) =
    completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (Etale.ordinaryFiniteP1_isUnit (l ^ (s.n + 1)) Y s.hYpow) z := by
  let X := ProjectiveLine Y
  let : HasDerivedCategory.{u + 1} (DiagonalAb X) :=
    DiagonalTraceLocalizations.ab (ℓ := l) (X := X)
  let A := ULift.{u + 1} (completedResidue l s.E s.π s.n)
  let F₁ := derivedScalars (integralMap l s.E) X
  let F₂ := derivedScalars (quotientMap l s.E s.π s.n) X
  let S₁ := DerivedCategory.singleFunctor
    (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0
  let S₄ := DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} A)) 0
  let z₁ := S₁.map s.completedP.unitIso.inv ≫
    SpTowerClasses.mapSingleArrow s.completedP.F (2 : ℤ) z ≫
      (S₁.map s.completedP.lineIso.hom)⟦(2 : ℤ)⟧'
  let z₂ := (s.toIntegral.units X).iso.inv ≫ F₁.map z₁ ≫
    s.toIntegral.lineP.shift (integralMap l s.E)
  let z₃ := (s.scalar.units X).iso.inv ≫ F₂.map z₂ ≫
    s.scalar.lineP.shift (quotientMap l s.E s.π s.n)
  let z₄ := S₄.map s.eP.unitIso.inv ≫
    SpTowerClasses.mapSingleArrow s.eP.F (2 : ℤ) z₃ ≫
      (S₄.map (s.lineP.iso l).hom)⟦(2 : ℤ)⟧'
  have hlocal : LocalComposite l Y s z =
      (finiteUnitComparison A X).hom ≫ z₄ ≫
        (finiteLineComparison A (l ^ (s.n + 1)) s.hA X).inv := by
    dsimp only [z₄, z₃, z₂, z₁, F₁, F₂, S₁, S₄]
    unfold LocalComposite localUnitInv localLine localFunctor
      ChernCoefficientDiagram.localUnitIso diagram
    simp only [SpTowerClasses.mapSingleArrow, Endpoint.shift,
      CompletedRealization.shiftedLine, QuotientLineRealization.shifted,
      FiniteRealization.shiftedLine, Iso.trans_inv, Iso.symm_inv,
      Iso.app_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc,
      id_eq, Functor.comp_map]
    rfl
  let U := SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  let L := Scheme.purTwistZlModule X l
  let e₀ := completedUnderlying l Y s
  let q₀ := e₀.inv.app U ≫ s.completedP.unitIso.hom.hom
  let q₁ := coefficientMap (integralMap l s.E) X
  let q₂ := coefficientMap (quotientMap l s.E s.π s.n) X
  let q₃ := s.eP.underlying.inv.app _ ≫ (cartierForget A X).map s.eP.unitIso.hom
  let r₀ := e₀.inv.app L ≫ s.completedP.lineIso.hom.hom
  let r₁ := integralLineMap l s.E X
  let r₂ := quotientLineMap l s.E s.π s.n X
  let r₃ := s.eP.underlying.inv.app _ ≫
    (cartierForget A X).map (s.lineP.iso l).hom
  let S := DerivedCategory.singleFunctor (DiagonalAb X) 0
  have h₁ : S.map q₀ ≫ mapSingleArrow (Mod.forget _) (2 : ℤ) z₁ =
      mapSingleArrow (localCompletedForget l X) (2 : ℤ) z ≫
        (S.map r₀)⟦(2 : ℤ)⟧' := by
    exact exact_underlying_arrow s.completedP.F (localCompletedForget l X)
      (Mod.forget _) e₀ s.completedP.unitIso s.completedP.lineIso z
  have h₂ : S.map q₁ ≫ mapSingleArrow (Mod.forget _) (2 : ℤ) z₂ =
      mapSingleArrow (Mod.forget _) (2 : ℤ) z₁ ≫ (S.map r₁)⟦(2 : ℤ)⟧' := by
    exact scalar_underlying_arrow (integralMap l s.E) X
      (s.toIntegral.units X) s.toIntegral.lineP z₁
  have h₃ : S.map q₂ ≫ mapSingleArrow (Mod.forget _) (2 : ℤ) z₃ =
      mapSingleArrow (Mod.forget _) (2 : ℤ) z₂ ≫ (S.map r₂)⟦(2 : ℤ)⟧' := by
    exact scalar_underlying_arrow (quotientMap l s.E s.π s.n) X
      (s.scalar.units X) s.scalar.lineP z₂
  have h₄ : S.map q₃ ≫ mapSingleArrow (cartierForget A X) (2 : ℤ) z₄ =
      mapSingleArrow (Mod.forget _) (2 : ℤ) z₃ ≫ (S.map r₃)⟦(2 : ℤ)⟧' := by
    exact exact_underlying_arrow s.eP.F (Mod.forget _) (cartierForget A X)
      s.eP.underlying s.eP.unitIso (s.lineP.iso l) z₃
  have hroute : S.map (q₀ ≫ q₁ ≫ q₂ ≫ q₃) ≫
      mapSingleArrow (cartierForget A X) (2 : ℤ) z₄ =
      mapSingleArrow (localCompletedForget l X) (2 : ℤ) z ≫
        (S.map (r₀ ≫ r₁ ≫ r₂ ≫ r₃))⟦(2 : ℤ)⟧' := by
    exact normalized_four_squares S h₁ h₂ h₃ h₄
  have hsource : localCompletedGenerator l X ≫ q₀ ≫ q₁ ≫ q₂ ≫ q₃ =
      DiagonalTrace.siteIntegralGenerator A X := by
    simpa only [q₀, q₁, q₂, q₃, e₀, Category.assoc] using normalized_source l Y s
  have htarget : r₀ ≫ r₁ ≫ r₂ ≫ r₃ =
      (localCompletedRoots l X).hom ≫
        limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op s.n) ≫
        cartierProRootMap A (l ^ (s.n + 1)) s.hA X
          (pow_pos (Fact.out : l.Prime).pos _)
          (Etale.ordinaryFiniteP1_isUnit (l ^ (s.n + 1)) Y s.hYpow) := by
    have hr : r₀ = s.completedP.roots.hom := eq_of_heq s.completedP.line_normalization
    have ht := diagonalIntegralRoots_transition l X s.E s.completedP.roots s.lineP.1
    have hn := s.lineP.2.2.normalization
    change s.lineP.1.hom ≫ r₂ ≫ r₃ = _ at hn
    have hf := finiteRoots_toLine_eq_cartierProRootMap s.lineP.2.1 A s.hA
      (pow_pos (Fact.out : l.Prime).pos _)
      (Etale.ordinaryFiniteP1_isUnit (l ^ (s.n + 1)) Y s.hYpow)
    have hid : (localCompletedRoots l X).hom = 𝟙 _ := rfl
    exact normalized_target_chain hr ht hn hf hid
  let b := (Etale.ordinaryFiniteExtHomEquiv A X (Etale.ordinaryFiniteConstant A X)
    (Scheme.finiteEtaleTateLine X (l ^ (s.n + 1)) A s.hA) 2).symm
      (LocalFiniteArrow.toHom l Y s k)
  have hb : (DiagonalTrace.finiteEtaleProImage A X (l ^ (s.n + 1)) s.hA b).hom = z₄ := by
    have hf := hk.symm.trans hlocal
    unfold FiniteComparison at hf
    exact (finite_image_hom A X (l ^ (s.n + 1)) s.hA
      (LocalFiniteArrow.toHom l Y s k)).trans
        (normalized_iso_transport (finiteUnitComparison A X)
          (finiteLineComparison A (l ^ (s.n + 1)) s.hA X) hf)
  have hi := DiagonalTrace.integralImage A X (l ^ (s.n + 1)) s.hA b
  have he : Etale.ordinaryFiniteExtHomEquiv A X (Etale.ordinaryFiniteConstant A X)
      (Scheme.finiteEtaleTateLine X (l ^ (s.n + 1)) A s.hA) 2 b =
      LocalFiniteArrow.toHom l Y s k := Equiv.apply_symm_apply _ _
  have hclass := congrArg (fun c ↦
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison X).inv
      ((Etale.ordinaryFiniteClass A X
        (Scheme.finiteEtaleTateLine X (l ^ (s.n + 1)) A s.hA) 2 c).mapExactFunctor
          (comparisonUpperStar AddCommGrpCat.{u + 1} X))
      ((forgetComparisonIso A X).hom.app
        (Scheme.finiteEtaleTateLine X (l ^ (s.n + 1)) A s.hA))) he
  refine (hi.trans hclass).symm.trans ?_
  apply source_exact_ext_eq (cartierForget A X)
    (DiagonalTrace.siteIntegralGenerator A X) _ _ z₄ hb
  exact (normalized_square_precompose S (localCompletedGenerator l X)
    (DiagonalTrace.siteIntegralGenerator A X) (q₀ ≫ q₁ ≫ q₂ ≫ q₃)
    (r₀ ≫ r₁ ≫ r₂ ≫ r₃) _ _ _ hroute hsource htarget).trans
      (completed_projection_hom l X A s.n s.hA
        (Etale.ordinaryFiniteP1_isUnit (l ^ (s.n + 1)) Y s.hYpow) z).symm

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
