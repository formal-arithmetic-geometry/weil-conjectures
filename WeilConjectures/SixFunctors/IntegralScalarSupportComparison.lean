/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteScalarMateData
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor

/-! # Integral scalar comparison on constructible compact support

Source: current blueprint coefficient-extension exceptional-image proof,
sec-six-functors-basics/sk-prop-scalar-six; Stacks 0941, 079P and 07A6
(blueprint: lem-coef-integral-scalar-support-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteScalarMate

attribute [local irreducible] integralComparisonDerivedSequenceScalar
  integralScalarExtensionOfUniverses

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

variable {l E L i D hl f c}

private def completionIso (W : Scheme.{u}) :
    (sfIntegralConstructible l E W).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E L i W) ≅
      (sfIntegralConstructible l E W).ι ⋙ integralScalarExtensionOfUniverses l E L i W :=
  NatIso.ofComponents
    (fun K ↦ IntegralFiniteExtension.completion l E L i W K.obj K.property.1)
    (fun g ↦ (completedScalarComparison l E L i W).naturality g.hom)

private theorem inputFiniteTor (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] (K : sfIntegralConstructibleCategory l E X) :
    finiteTorConstructibleIntegral l E X K.obj := by
  have primeUnit : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit.map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom)).invertible
  rw [← (integral_residue_tor D l hl E X).2]
  exact K.property

private def ordinarySupportIso :
    (sfIntegralConstructible l E X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E) c ⋙
          pbcDerivedExtend (completedCoefficientMap l E L i Y) ≅
      (sfIntegralConstructible l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E L i X) ⋙
          PurCompactSupport.image (PurCompactSupport.completed l L) c :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _
      ((PurCompactSupport.comparison (PurCompactSupport.completedChange l E L i) c).app K.obj)
      ((PurCompactSupport.integralCoefficientComparison l E L i D hl f c
        K.obj (inputFiniteTor D hl K)).2.2.2.1))
    (fun g ↦ (PurCompactSupport.comparison
      (PurCompactSupport.completedChange l E L i) c).naturality g.hom)

private theorem composeSquares {C : Type*} [Category* C]
    {A B C₀ A' B' C' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : C₀ ⟶ C'}
    {u : A ⟶ B} {v : B ⟶ C₀} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : f ≫ u' = u ≫ g) (hv : g ≫ v' = v ≫ h) :
    f ≫ (u' ≫ v') = (u ≫ v) ≫ h := by
  rw [← Category.assoc, hu, Category.assoc, hv, ← Category.assoc]

private theorem mapSquare {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B A' B' : C} {f : A ⟶ A'} {g : B ⟶ B'}
    {u : A ⟶ B} {u' : A' ⟶ B'} (hu : f ≫ u' = u ≫ g) :
    F.map f ≫ F.map u' = F.map u ≫ F.map g := by
  rw [← F.map_comp, hu, F.map_comp]

private def ambientIntegralIso (a : Context l E L i D hl f c) :
    (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⋙
        a.TIY) ⋙ (sfIntegralConstructible l L Y).ι ≅
      (a.TIX ⋙ sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c L) ⋙ (sfIntegralConstructible l L Y).ι :=
  NatIso.ofComponents (fun K ↦
    (completionIso (l := l) (E := E) (L := L) (i := i) Y).symm.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj K) ≪≫
      (pbcDerivedExtend (completedCoefficientMap l E L i Y)).mapIso
        ((sfQcqsCompactSupportRealization l E D.k
          (finiteFieldDatumPrimeUnit D l hl) c).app K).symm ≪≫
      (ordinarySupportIso (l := l) (E := E) (L := L) (i := i) (D := D)
        (hl := hl) (f := f) (c := c)).app K ≪≫
      (PurCompactSupport.image (PurCompactSupport.completed l L) c).mapIso
        ((completionIso (l := l) (E := E) (L := L) (i := i) X).app K) ≪≫
      (sfQcqsCompactSupportRealization l L D.k
        (finiteFieldDatumPrimeUnit D l hl) c).app (a.TIX.obj K)) (by
    intro K J g
    have h₁ := (completionIso (l := l) (E := E) (L := L) (i := i) Y).inv.naturality
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E).map g)
    have h₂ := (sfQcqsCompactSupportRealization l E D.k
      (finiteFieldDatumPrimeUnit D l hl) c).inv.naturality g
    have h₃ := (ordinarySupportIso (l := l) (E := E) (L := L) (i := i)
      (D := D) (hl := hl) (f := f) (c := c)).hom.naturality g
    have h₄ := (completionIso (l := l) (E := E) (L := L) (i := i) X).hom.naturality g
    have h₅ := (sfQcqsCompactSupportRealization l L D.k
      (finiteFieldDatumPrimeUnit D l hl) c).hom.naturality (a.TIX.map g)
    exact composeSquares h₁ (composeSquares
      (mapSquare (pbcDerivedExtend (completedCoefficientMap l E L i Y)) h₂)
      (composeSquares h₃ (composeSquares
        (mapSquare (PurCompactSupport.image (PurCompactSupport.completed l L) c) h₄) h₅))))

private def integralIso (a : Context l E L i D hl f c) :
    sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⋙
        a.TIY ≅ a.TIX ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c L :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((ambientIntegralIso a).app K))
    (fun g ↦ ObjectProperty.hom_ext _ ((ambientIntegralIso a).hom.naturality g))

private theorem integralIso_normalization (a : Context l E L i D hl f c)
    (K : sfIntegralConstructibleCategory l E X) :
    ((integralIso a).hom.app K).hom = a.integralAlphaComponent K := by
  dsimp only [integralIso, ambientIntegralIso, ordinarySupportIso, NatIso.ofComponents,
    ObjectProperty.isoMk,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, completionIso]
  rfl

variable (l E L i D hl f c)

/-- The actual completion-conjugated support comparison is an invertible natural map.
Source: finite-free completed comparison and compact-support coefficient comparison,
current blueprint coefficient-extension compact-support proof
(blueprint: lem-coef-integral-scalar-support-comparison).

Proof: residue Tor identifies the integral constructible domain with the finite-Tor
constructible domain. The integral coefficient comparison is therefore invertible
on every object of that domain. Whisker the ordinary completed scalar comparison
with the inclusion of the constructible domain and use componentwise invertibility
to form its natural isomorphism. The finite-free completion comparisons are natural
isomorphisms on X and Y. Conjugate the ordinary comparison by their inverses at the
source and their forward maps at the target, and by the two recorded compact-support
realizations. Full faithfulness of the constructible inclusion lifts this ambient
natural isomorphism. Expanding its five factors gives exactly integralAlphaComponent,
in the displayed order. This works also for identity extensions and zero objects. -/
theorem integralScalarSupportComparison (a : Context l E L i D hl f c) :
    ∃ α : sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E ⋙ a.TIY ≅
      a.TIX ⋙ sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c L,
      ∀ K : sfIntegralConstructibleCategory l E X,
        (α.hom.app K).hom = a.integralAlphaComponent K := by
  exact ⟨integralIso a, integralIso_normalization a⟩

end WeilConjectures.FiniteScalarMate
