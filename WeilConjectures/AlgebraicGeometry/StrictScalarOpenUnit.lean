/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantScalarTowerMates
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenArrows
import all WeilConjectures.CategoryTheory.DerivedExactSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenArrows

/-! # Scalar extension preserves the strict open adjunction unit

Source: Stacks Project, sites-modules.tex, Tag 0E8I, and sites-cohomology.tex,
Tag 07A6; the open-unit calculation in auxiliary refinement Steps 3--4.
(blueprint: lem-pur-strict-scalar-open-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] T U scalarAdj properRestriction openTensor
  AlgebraicGeometry.ProEtale.StrictTower.G AlgebraicGeometry.ProEtale.StrictTower.J
  AlgebraicGeometry.ProEtale.StrictTower.jAdj

-- Transpose the two scalar mates and use the restriction/open unit equation.
private theorem scalar_mate_open_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {TW : A ⥤ C} {UW : C ⥤ A} {TU : B ⥤ D} {UU : D ⥤ B}
    {JA : B ⥤ A} {GA : A ⥤ B} {JB : D ⥤ C} {GB : C ⥤ D}
    (a : TW ⊣ UW) (b : TU ⊣ UU) (jA : JA ⊣ GA) (jB : JB ⊣ GB)
    (t : UW ⋙ GA ≅ GB ⋙ UU) (d : UU ⋙ JA ≅ JB ⋙ UW)
    (hd : ∀ N, UU.map (jB.unit.app N) ≫ t.inv.app (JB.obj N) =
      jA.unit.app (UU.obj N) ≫ GA.map (d.hom.app N))
    (M : B) :
    TU.map (jA.unit.app M) ≫
        ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).app (JA.obj M) ≫
        GB.map (((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).app M) =
      jB.unit.app (TU.obj M)  := by
  let p : GA ⋙ TU ⟶ TW ⋙ GB :=
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans
  let q : JA ⋙ TW ⟶ TU ⋙ JB :=
    ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans
  change TU.map (jA.unit.app M) ≫ p.app (JA.obj M) ≫ GB.map (q.app M) = _
  apply (b.homEquiv M _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h₁ : GA.map (a.unit.app (JA.obj M)) ≫ t.hom.app (TW.obj (JA.obj M)) =
      b.unit.app (GA.obj (JA.obj M)) ≫ UU.map (p.app (JA.obj M)) :=
    unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ t.hom) (JA.obj M)
  have h₂ : JA.map (b.unit.app M) ≫ d.hom.app (TU.obj M) =
      a.unit.app (JA.obj M) ≫ UW.map (q.app M) :=
    unit_mateEquiv_symm b a (TwoSquare.mk _ _ _ _ d.hom) M
  rw [b.unit_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% h₁]
  have hn := t.hom.naturality (q.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← GA.map_comp_assoc, ← h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [jA.unit_naturality_assoc]
  dsimp only [Functor.comp_obj]
  have h := congrArg (fun f ↦ f ≫ t.hom.app (JB.obj (TU.obj M))) (hd (TU.obj M))
  simp only [Category.assoc, Iso.inv_hom_id_app] at h
  dsimp only [Functor.comp_obj] at h
  simp only [Category.comp_id] at h
  rw [← h]

private theorem leftAdjointUniq_ofNatIsoRight_hom
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (d : R' ≅ R) :
    ((a.ofNatIsoRight d.symm).leftAdjointUniq b).hom =
      (conjugateEquiv b a).symm d.hom := by
  ext M
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_counit]

private theorem scalar_pull_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {TW : A ⥤ C} {UW : C ⥤ A} {TU : B ⥤ D} {UU : D ⥤ B}
    {GA : A ⥤ B} {RA : B ⥤ A} {GB : C ⥤ D} {RB : D ⥤ C}
    (a : TW ⊣ UW) (b : TU ⊣ UU) (gA : GA ⊣ RA) (gB : GB ⊣ RB)
    (t : UW ⋙ GA ≅ GB ⋙ UU) (d : RB ⋙ UW ≅ UU ⋙ RA)
    (hd : (mateEquiv gB gA (TwoSquare.mk _ _ _ _ t.hom)).natTrans = d.hom) :
    (((gA.comp b).ofNatIsoRight d.symm).leftAdjointUniq (a.comp gB)).hom =
      ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans := by
  rw [leftAdjointUniq_ofNatIsoRight_hom]
  apply (conjugateEquiv (a.comp gB) (gA.comp b)).injective
  rw [Equiv.apply_symm_apply, ← iterated_mateEquiv_conjugateEquiv a b gA gB]
  rw [Equiv.apply_symm_apply]
  exact hd.symm

private theorem derivedSquare_symm
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : A ⥤ B} {G : A ⥤ C} {H : B ⥤ D} {L' : C ⥤ D}
    [L.Additive] [G.Additive] [H.Additive] [L'.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    (t : G ⋙ L' ≅ L ⋙ H) :
    (Functor.mapDerivedCategorySquareIso t.symm).hom =
      (Functor.mapDerivedCategorySquareIso t).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem derived_mate_normalized
    {A B C D : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (a : L ⊣ R) (b : L' ⊣ R') (t : G ⋙ L' ≅ L ⋙ H)
    (c : R ⋙ G ≅ H ⋙ R')
    (hc : (mateEquiv a b (TwoSquare.mk _ _ _ _ t.hom)).natTrans = c.hom)
    (d : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hd : unitCompatible R R' H G c d) :
    (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso t).hom)).natTrans =
        d.hom := by
  have hordinary (N : B) : H.map (a.counit.app N) =
      t.inv.app (R.obj N) ≫ L'.map (c.hom.app N) ≫ b.counit.app (H.obj N) := by
    have h := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ t.hom) N
    rw [show (mateEquiv a b (TwoSquare.mk _ _ _ _ t.hom)).app N =
      c.hom.app N from congrArg (fun z ↦ z.app N) hc] at h
    change L'.map (c.hom.app N) ≫ b.counit.app (H.obj N) =
      t.hom.app (R.obj N) ≫ H.map (a.counit.app N) at h
    rw [h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hderived := CategoryTheory.ExactDerivedSquare.square_counit
    R R' H G L L' a b t.symm c hordinary d (by
      simpa only [unitCompatible, derivedUnit, Functor.rightDerivedFunctorUnitQ,
        NatIso.mapHomologicalComplex] using hd)
  let m : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor :=
    (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso t).hom)).natTrans
  change m = d.hom
  apply NatTrans.ext
  funext N
  apply (b.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have hm : L'.mapDerivedCategory.map (m.app N) ≫
      b.mapDerivedCategoryRightDerivedAdjunction.counit.app
        (H.mapDerivedCategory.obj N) =
      (Functor.mapDerivedCategorySquareIso t).hom.app (R.rightDerivedFunctor.obj N) ≫
        H.mapDerivedCategory.map
          (a.mapDerivedCategoryRightDerivedAdjunction.counit.app N) :=
    mateEquiv_counit a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso t).hom) N
  rw [hm]
  have h := hderived N
  rw [derivedSquare_symm] at h
  rw [h]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem whisker_mate_app
    {A B C D I : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category I]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (t : G ⋙ L' ⟶ L ⋙ H)
    (d : (Functor.whiskeringRight I _ _).obj G ⋙
        (Functor.whiskeringRight I _ _).obj L' ⟶
      (Functor.whiskeringRight I _ _).obj L ⋙
        (Functor.whiskeringRight I _ _).obj H)
    (hd : ∀ N n, (d.app N).app n = t.app (N.obj n)) (N : I ⥤ B) (n : I) :
    (((mateEquiv (a.whiskerRight I) (b.whiskerRight I)
      (TwoSquare.mk _ _ _ _ d)).natTrans.app N).app n) =
        (mateEquiv a b (TwoSquare.mk _ _ _ _ t)).natTrans.app (N.obj n) := by
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp,
    Adjunction.whiskerRight_unit_app_app, Adjunction.whiskerRight_counit_app_app,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj, NatTrans.id_app, hd]

-- Lift by components without expanding the underlying sheaf functors.
private noncomputable def whiskerSquareIso
    {A B C D I : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category I]
    {L : A ⥤ B} {L' : C ⥤ D} {G : A ⥤ C} {H : B ⥤ D}
    (t : G ⋙ L' ≅ L ⋙ H) :
    (Functor.whiskeringRight I _ _).obj G ⋙
        (Functor.whiskeringRight I _ _).obj L' ≅
      (Functor.whiskeringRight I _ _).obj L ⋙
        (Functor.whiskeringRight I _ _).obj H :=
  NatIso.ofComponents
    (fun N ↦ NatIso.ofComponents (fun n ↦ t.app (N.obj n))
      (fun f ↦ t.hom.naturality (N.map f))) (by
        intro N M f
        apply NatTrans.ext
        funext n
        exact t.hom.naturality (f.app n))

private noncomputable def ordinaryPull
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (s : X ⟶ Y) :
    restrict l E F i Y ⋙
        towerPullback (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s ≅
      towerPullback (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s ⋙
        restrict l E F i X := by
  let t := proEtaleRingRestrictionPullbackInv s
    ((constants l E).ring Y) ((constants l F).ring Y)
    ((constants l E).ring X) ((constants l F).ring X)
    (constantMap l E F i Y) (constantMap l E F i X)
    ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)
  have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso s
    ((constants l E).ring Y) ((constants l F).ring Y)
    ((constants l E).ring X) ((constants l F).ring X)
    (constantMap l E F i Y) (constantMap l E F i X)
    ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)
  exact whiskerSquareIso (asIso t)

private theorem ordinary_pull_mate
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (s : X ⟶ Y) :
    (mateEquiv
      ((proEtaleRingModuleAdjunction s ((constants l F).ring Y)
        ((constants l F).ring X) ((constants l F).pull s)).whiskerRight ℕᵒᵖ)
      ((proEtaleRingModuleAdjunction s ((constants l E).ring Y)
        ((constants l E).ring X) ((constants l E).pull s)).whiskerRight ℕᵒᵖ)
      (TwoSquare.mk _ _ _ _ (ordinaryPull l E F i s).hom)).natTrans =
        (properRestrictionOrdinary l E F i s).hom := by
  let d := proEtaleRingRestrictionDirectImage s
    ((constants l E).ring Y) ((constants l F).ring Y)
    ((constants l E).ring X) ((constants l F).ring X)
    (constantMap l E F i Y) (constantMap l E F i X)
    ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)
  have hd : whiskerSquareIso (I := ℕᵒᵖ) d =
      properRestrictionOrdinary l E F i s := by
    apply (properRestrictionOrdinary_existsUnique l E F i s).choose_spec.2
    intro N n V
    apply heq_of_eq
    funext x
    exact (proEtaleRingRestrictionDirectImage_existsUnique s
      ((constants l E).ring Y) ((constants l F).ring Y)
      ((constants l E).ring X) ((constants l F).ring X)
      (constantMap l E F i Y) (constantMap l E F i X)
      ((constants l E).pull s) ((constants l F).pull s)
      ((change l E F i).square s)).choose_spec.1 (N.obj (Opposite.op n)) V x
  apply Eq.trans (b := (whiskerSquareIso (I := ℕᵒᵖ) d).hom)
  · apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext n
    let t := proEtaleRingRestrictionPullbackInv s
      ((constants l E).ring Y) ((constants l F).ring Y)
      ((constants l E).ring X) ((constants l F).ring X)
      (constantMap l E F i Y) (constantMap l E F i X)
      ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)
    exact (whisker_mate_app
      (proEtaleRingModuleAdjunction s ((constants l F).ring Y)
        ((constants l F).ring X) ((constants l F).pull s))
      (proEtaleRingModuleAdjunction s ((constants l E).ring Y)
        ((constants l E).ring X) ((constants l E).pull s))
      t (ordinaryPull l E F i s).hom (by intro N n; rfl) N n).trans
      (congrArg (fun t ↦ t.app (N.obj n))
      (restrictionPullback_mate s
        ((constants l E).ring Y) ((constants l F).ring Y)
        ((constants l E).ring X) ((constants l F).ring X)
        (constantMap l E F i Y) (constantMap l E F i X)
        ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)))
  · exact congrArg Iso.hom hd

private theorem ordinary_open_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (s : X ⟶ Y) [IsOpenImmersion s]
    (N : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X) :
    (restrict l E F i X).map
        (((moduleJAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).whiskerRight
          ℕᵒᵖ).unit.app N) ≫
        (ordinaryPull l E F i s).inv.app
          ((towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).obj N) =
      ((moduleJAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).whiskerRight
        ℕᵒᵖ).unit.app ((restrict l E F i X).obj N) ≫
        (towerPullback (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).map
          ((openRestrictionOrdinary l E F i s).hom.app N) := by
  have := proEtaleRingRestrictionPullbackInv_isIso s
    ((constants l E).ring Y) ((constants l F).ring Y)
    ((constants l E).ring X) ((constants l F).ring X)
    (constantMap l E F i Y) (constantMap l E F i X)
    ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s)
  apply NatTrans.ext
  funext n
  exact unit_mateEquiv_symm
    (PurCompactSupport.openAdjunction (constants l F) s)
    (PurCompactSupport.openAdjunction (constants l E) s)
    (TwoSquare.mk _ _ _ _
      (inv (proEtaleRingRestrictionPullbackInv s
        ((constants l E).ring Y) ((constants l F).ring Y)
        ((constants l E).ring X) ((constants l F).ring X)
        (constantMap l E F i Y) (constantMap l E F i X)
        ((constants l E).pull s) ((constants l F).pull s) ((change l E F i).square s))))
    (N.obj n)

/-- The normalized scalar/open square preserves the open adjunction unit.
Source: Stacks Tags 0E8I and 07A6; auxiliary refinement Steps 3--4
(blueprint: lem-pur-strict-scalar-open-unit).
Proof: compute on complexes of strict towers. The ordinary open adjunction unit
identifies a section on the open with its original extension-by-zero summand.
The coefficient pullback comparison preserves that section and its tensor factor;
the open tensor comparison sends that same tensor to the same open summand.
Their composite is consequently the open unit over the extended coefficient ring.
These sectionwise maps are balanced, commute with sheafification, differentials
and every tower transition. Exact localization retains the unit equation.
The whole-complex unit normalization of properRestriction identifies its geometric
left-adjoint comparison with this pullback comparison, by uniqueness of adjoints.
The inverse-mate formula defining openTensor, applied to the localized ordinary
restriction square, identifies the other factor with the ordinary open tensor map.
The displayed uniqueness isomorphism is definitionally strictScalarPull, so this
uses the published maps without selecting a new comparison or invoking faithfulness
of level evaluation. No closedness, quasi-compactness or finite-origin assumption
is required. -/
theorem strictScalarOpenUnit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {U W : Scheme.{u}} (s : U ⟶ W) [IsOpenImmersion s]
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) U) :
    let h := (((adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).comp
      (scalarAdj l E F i U)).ofNatIsoRight (properRestriction l E F i s).symm).leftAdjointUniq
        ((scalarAdj l E F i W).comp
          (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s))
    (T l E F i U).map
        ((jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).unit.app M) ≫
        h.hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).map
          ((openTensor l E F i s).app M) =
      (jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).unit.app
        ((T l E F i U).obj M)  := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let t := ordinaryPull l E F i s
  let c := properRestrictionOrdinary l E F i s
  let aE := (proEtaleRingModuleAdjunction s (coefficients A W)
    (coefficients A U) (constantRingIso A s)).whiskerRight ℕᵒᵖ
  let aF := (proEtaleRingModuleAdjunction s (coefficients B W)
    (coefficients B U) (constantRingIso B s)).whiskerRight ℕᵒᵖ
  let td : WeilConjectures.PurStrictScalar.U l E F i W ⋙ G A s ≅
      G B s ⋙ WeilConjectures.PurStrictScalar.U l E F i U := by
    unfold WeilConjectures.PurStrictScalar.U G
    exact Functor.mapDerivedCategorySquareIso t
  let d : (towerDirectImage B s).rightDerivedFunctor ⋙
        (restrict l E F i W).mapDerivedCategory ≅
      (restrict l E F i U).mapDerivedCategory ⋙
        (towerDirectImage A s).rightDerivedFunctor := by
    have h := properRestriction l E F i s
    unfold R WeilConjectures.PurStrictScalar.U at h
    exact h
  have hd : unitCompatible (towerDirectImage B s) (towerDirectImage A s)
      (restrict l E F i U) (restrict l E F i W) c d := by
    dsimp only [d, c, A, B, id]
    unfold properRestriction
    exact (properRestriction_existsUnique l E F i s).choose_spec.1
  have ht₀ := derived_mate_normalized aF aE t c (ordinary_pull_mate l E F i s) d hd
  have ht : (mateEquiv (adj B s) (adj A s)
      (TwoSquare.mk _ _ _ _ td.hom)).natTrans = (properRestriction l E F i s).hom := by
    dsimp only [td, id]
    unfold adj
    unfold G R WeilConjectures.PurStrictScalar.U
    exact ht₀
  have hh := scalar_pull_eq (scalarAdj l E F i W) (scalarAdj l E F i U)
    (adj A s) (adj B s) td (properRestriction l E F i s) ht
  have hu (N : Derived B U) :
      (WeilConjectures.PurStrictScalar.U l E F i U).map ((jAdj B s).unit.app N) ≫
          td.inv.app ((J B s).obj N) =
        (jAdj A s).unit.app ((WeilConjectures.PurStrictScalar.U l E F i U).obj N) ≫
          (G A s).map ((openRestriction l E F i s).hom.app N) := by
    have h := exact_mate ((moduleJAdj B s).whiskerRight ℕᵒᵖ)
      ((moduleJAdj A s).whiskerRight ℕᵒᵖ) t.symm
      (openRestrictionOrdinary l E F i s)
      (exactAdj ((moduleJAdj B s).whiskerRight ℕᵒᵖ))
      (exactAdj ((moduleJAdj A s).whiskerRight ℕᵒᵖ))
      (exactAdj_unit ((moduleJAdj B s).whiskerRight ℕᵒᵖ))
      (exactAdj_unit ((moduleJAdj A s).whiskerRight ℕᵒᵖ))
      (fun K ↦ (ordinary_open_unit l E F i s K).symm) N
    rw [derivedSquare_symm] at h
    dsimp only [td, id]
    unfold WeilConjectures.PurStrictScalar.U J G openRestriction
    simpa only [exactAdj_jAdj] using h.symm
  dsimp only
  rw [hh]
  unfold openTensor
  exact scalar_mate_open_unit (scalarAdj l E F i W) (scalarAdj l E F i U)
    (jAdj A s) (jAdj B s) td (openRestriction l E F i s) hu M

end WeilConjectures.PurStrictScalar
