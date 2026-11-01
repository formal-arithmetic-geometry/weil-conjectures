/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointTensor
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalDoubleCounit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedMatesCompositionPasting
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
/-!
# Finite etale dualizing normalization

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization).

We use the canonical etale-origin coordinates of the finite etale normalization. The
functor rho is constructed by adjunction
conjugacy from the graph-normalized proper-support comparison. Its value eta on the
unit, the compositor c, theta, beta, sigma and E are specified constructions, never
fields that can be filled with unrelated endpoint isomorphisms. Equations are tested
on every etale representative whose comparison image belongs to pro-etale Dctf.
Full faithfulness, and the canonical tensor/pullback/unit/support comparisons, identify
these with the named pro-etale maps; naturality makes them independent of origins.

## Main definitions and statement

* `FiniteEtaleNormalization.rho` and `.eta`: the counit-normalized etale comparisons.
* `FiniteEtaleNormalization.comp`, `.sigma`, `.sourceEtale`, `.beta`: the specified maps.
* `FiniteEtaleDualizingNormalization`: their normalization and compatibility equations.
* `finite_etale_dualizing_normalization`: all these equations hold.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
  AlgebraicGeometry.Etale.lowerStar AlgebraicGeometry.Etale.etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem exchangeCancellation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {L M N O P : D} {V W Z Q : C}
    (i' : L ≅ M) (r' : N ≅ L) (c' : O ≅ N) (q : O ≅ P)
    (c : P ≅ F.obj V) (r : V ≅ W) (i : W ≅ Z) (u : W ≅ Q)
    (B : M ⟶ F.obj Z)
    (hB : B = i'.inv ≫ r'.inv ≫ c'.inv ≫ q.hom ≫ c.hom ≫
      F.map r.hom ≫ F.map i.hom) :
    i'.hom ≫ B ≫ F.map i.inv ≫ F.map u.hom ≫
        F.map (r ≪≫ u).inv ≫ c.inv = r'.inv ≫ c'.inv ≫ q.hom := by
  rw [hB]
  simp only [Iso.trans_inv, Functor.map_comp, Category.assoc]
  simp only [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id,
    Category.comp_id]

private theorem inverseNormalization
    {C : Type*} [Category C] {W V Z Q : C}
    (t : W ≅ V) (s : W ≅ Z) (c : Z ≅ Q) (a : Q ≅ V)
    (h : s.inv ≫ t.hom = c.hom ≫ a.hom) :
    t.inv ≫ s.hom = a.inv ≫ c.inv := by
  apply (cancel_epi t.hom).1
  have hh := congrArg (fun q ↦ s.hom ≫ q ≫ a.inv ≫ c.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh.symm

private theorem mateApp
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R')
    {G : C ⥤ E} {H : D ⥤ F} (α : G ⋙ L' ⟶ L ⋙ H) (K : D) :
    (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).app K =
      a'.homEquiv _ _ (α.app (R.obj K) ≫ H.map (a.counit.app K)) := by
  apply (a'.homEquiv _ _).symm.injective
  change (a'.homEquiv (G.obj (R.obj K)) (H.obj K)).symm
    ((mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).app K) =
    (a'.homEquiv (G.obj (R.obj K)) (H.obj K)).symm
      (a'.homEquiv (G.obj (R.obj K)) (H.obj K) _)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, mateEquiv_counit]

private theorem mateTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R')
    {G G' : C ⥤ E} {H H' : D ⥤ F} (i : G ≅ G') (j : H ≅ H')
    (α : G ⋙ L' ⟶ L ⋙ H) :
    (mateEquiv a a' (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight i.inv L' ≫ α ≫ Functor.whiskerLeft L j.hom))).natTrans =
      Functor.whiskerLeft R i.inv ≫
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).natTrans ≫
          Functor.whiskerRight j.hom R' := by
  ext K
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [a'.counit_naturality]
  rw [mateEquiv_counit]
  simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← j.hom.naturality]
  have hm := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ α) K
  simpa only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj,
    Functor.comp_obj, Category.assoc] using congrArg
    (fun z ↦ L'.map (i.inv.app (R.obj K)) ≫ z ≫ j.hom.app K) hm.symm

private theorem tensorTransposeTransport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {V V' : C} (i : V ≅ V') (K : D)
    (p : F.obj (G.obj (𝟙_ D)) ⊗ K ⟶ F.obj (G.obj (𝟙_ D) ⊗ V))
    [IsIso p] :
    (G.obj (𝟙_ D) ◁ i.hom) ≫ (β_ (G.obj (𝟙_ D)) V').hom ≫
        adj.homEquiv _ K
          (F.map (β_ V' (G.obj (𝟙_ D))).hom ≫
            inv (p ≫ F.map (G.obj (𝟙_ D) ◁ i.hom)) ≫
            adj.counit.app (𝟙_ D) ▷ K ≫ (λ_ K).hom) =
      adj.homEquiv _ _ (inv p ≫ adj.counit.app (𝟙_ D) ▷ K) ≫
        G.map (λ_ K).hom := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left,
    ← adj.homEquiv_naturality_right]
  congr 1
  simp only [IsIso.inv_comp, ← F.map_inv, ← F.map_comp_assoc, Category.assoc]
  rw [SymmetricCategory.symmetry_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]

private theorem tensorNormalizationTransport
    {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    {W V V' H : C} (i : V ≅ V') (j : H ≅ V) (eta : W ≅ 𝟙_ C)
    (tau : V' ⊗ W ⟶ H) (theta : W ⊗ V ⟶ H)
    (ht : tau ≫ j.hom ≫ i.hom = V' ◁ eta.hom ≫ (ρ_ V').hom)
    (hθ : W ◁ i.hom ≫ (β_ W V').hom ≫ tau = theta) :
    theta ≫ j.hom = eta.hom ▷ V ≫ (λ_ V).hom := by
  apply (cancel_mono i.hom).1
  rw [← hθ]
  simp only [Category.assoc]
  rw [ht, ← BraidedCategory.braiding_naturality_left_assoc,
    braiding_rightUnitor]
  rw [whisker_exchange_assoc, leftUnitor_naturality]

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

/-- Finiteness of the actual coefficient quotient A = O_E/varpi_E^n, including its size lift.
Source: main-20261015, etale-locality Step 1, the finite coefficient datum of
def-pur-conventions (blueprint: lem-pur-finite-etale-dualizing-normalization).
This local instance inlines the finite-coefficient construction recorded with
def-pur-co-smoothness, so the item does not import that legacy comparison module.
-/
noncomputable instance coefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The coefficient unit in the same monoidal instance used by `derivedTensor`.
Source: main-20261015, etale-locality Step 1, the coefficient complex Lambda
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev coefficientUnit
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) := 𝟙_ _

/-- Tensoring the specified unit comparison and then applying the left unitor.
Assemble this map before coefficient specialization so that the tensor and unit share
one monoidal instance. Source: main-20261015, etale-locality Step 1, clause (1)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorUnitMap
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a : M ≅ coefficientUnit A X) :
    ((Etale.derivedTensor A X).obj M).obj N ⟶ N :=
  ((Etale.derivedTensor A X).map a.hom).app N ≫
    (Etale.derivedTensorLeftUnitor A X N).hom

section TensorTransport

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

private theorem tensorTransposeDerived (U X : Scheme.{u})
    {F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)} (adj : F ⊣ G)
    {V V' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)} (i : V ≅ V')
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (p : ((Etale.derivedTensor A X).obj (F.obj (G.obj (coefficientUnit A X)))).obj K ⟶
      F.obj (((Etale.derivedTensor A U).obj (G.obj (coefficientUnit A X))).obj V))
    [IsIso p] :
    ((Etale.derivedTensor A U).obj (G.obj (coefficientUnit A X))).map i.hom ≫
      ((Etale.derivedTensorSymmetry A U).hom.app (G.obj (coefficientUnit A X))).app V' ≫
      adj.homEquiv _ K
        (F.map (((Etale.derivedTensorSymmetry A U).hom.app V').app
            (G.obj (coefficientUnit A X))) ≫
          inv (p ≫ F.map
            (((Etale.derivedTensor A U).obj (G.obj (coefficientUnit A X))).map i.hom)) ≫
          ((Etale.derivedTensor A X).map (adj.counit.app (coefficientUnit A X))).app K ≫
          (Etale.derivedTensorLeftUnitor A X K).hom) =
      adj.homEquiv _ _
        (inv p ≫ ((Etale.derivedTensor A X).map
          (adj.counit.app (coefficientUnit A X))).app K) ≫
        G.map (Etale.derivedTensorLeftUnitor A X K).hom := by
  let := _root_.DerivedCategory.symmetricCategory (Sheaf U.smallEtaleTopology A)
  simpa only [Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map,
    Etale.derivedTensorLeftUnitor, Etale.derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app,
    Etale.derivedTensor, coefficientUnit, MonoidalCategory.curriedTensor_obj_obj,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
    Functor.flip_obj_obj] using
      tensorTransposeTransport adj i K p

private theorem tensorNormalizationDerived (U : Scheme.{u})
    {W V V' H : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (i : V ≅ V') (j : H ≅ V) (eta : W ≅ coefficientUnit A U)
    (tau : ((Etale.derivedTensor A U).obj V').obj W ⟶ H)
    (theta : ((Etale.derivedTensor A U).obj W).obj V ⟶ H)
    (ht : tau ≫ j.hom ≫ i.hom =
      ((Etale.derivedTensor A U).obj V').map eta.hom ≫
        (Etale.derivedTensorRightUnitor A U V').hom)
    (hθ : ((Etale.derivedTensor A U).obj W).map i.hom ≫
      ((Etale.derivedTensorSymmetry A U).hom.app W).app V' ≫ tau = theta) :
    theta ≫ j.hom = tensorUnitMap A U W V eta := by
  let := _root_.DerivedCategory.symmetricCategory (Sheaf U.smallEtaleTopology A)
  simpa only [tensorUnitMap, Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map,
    Etale.derivedTensorLeftUnitor, Etale.derivedTensorRightUnitor,
    Etale.derivedTensorSymmetry, _root_.DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app,
    Etale.derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app] using
      tensorNormalizationTransport i j eta tau theta ht hθ

end TensorTransport

section TensorTransportFinite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

private theorem tensorCanonicalTranspose {U X : Scheme.{u}} (e : U ⟶ X)
    [HasCompactification e]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      let W := Etale.dualizingComplex Λ e
    let V' := (Etale.upperStar (ModuleCat.{u + 1} Λ) e).mapDerivedCategory.obj K
    let i := (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) e).app K
    let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) e
    let adj := Etale.rightDerivedUpperShriekAdjunction Λ e
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj W).map i.hom ≫
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} Λ) U).hom.app W).app V' ≫
      adj.homEquiv _ K
        (F.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} Λ) U).hom.app V').app W) ≫
          inv (((Etale.projectionMap (ModuleCat.{u + 1} Λ) e).app W).app K ≫ F.map
            (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj W).map i.hom)) ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).map
            (adj.counit.app (coefficientUnit (ModuleCat.{u + 1} Λ) X))).app K ≫
          (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X K).hom) =
      Etale.dualizingComplexTensorMap Λ e K := by
  dsimp only
  simpa only [Etale.dualizingComplexTensorMap, Etale.lowerShriekRightAdjointUnitTensorMap,
    Etale.lowerShriekRightAdjointTensorMap, Adjunction.projectionTensorMap,
    Etale.dualizingComplex, coefficientUnit, Etale.derivedTensor_map_app,
    Etale.derivedTensorLeftUnitor, Etale.derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
    Functor.flip_obj_obj, Functor.id_obj, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map] using
      tensorTransposeDerived (ModuleCat.{u + 1} Λ) U X (Etale.rightDerivedUpperShriekAdjunction Λ e)
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) e).app K) K
        (((Etale.projectionMap (ModuleCat.{u + 1} Λ) e).app (Etale.dualizingComplex Λ e)).app K)

end TensorTransportFinite

variable (P : WeilConjectures.PurityFiniteSetting.{u})
/-- The fixed Nagata compactification interface; no absolute separatedness is required.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev compactification
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    : HasCompactification f :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  (HasCompactification.compactification f).hasCompactification

private theorem fieldSchemeNoetherian
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] : IsNoetherian X :=
  { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k)) }

/-- The existing etale exceptional functor, with its compactification supplied internally.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev exceptional
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X :=
  letI := compactification P f
  Etale.rightDerivedUpperShriek P.Coefficient f

/-- The existing compact-support functor, in the same supplied compactification.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def lower
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient X ⥤
      Etale.DerivedCategoryModule P.Coefficient Y :=
  letI := compactification P f
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f

/-- The existing exceptional counit, with the same supplied compactification.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def counit
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    exceptional P f ⋙ lower P f ⟶ 𝟭 _ :=
  letI := compactification P f
  (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).counit

/-- The canonical derived restriction in the same coefficient coordinates.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

/-- The dualizing object is the unit value of the existing exceptional functor.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
abbrev omega
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Etale.DerivedCategoryModule P.Coefficient X :=
  letI := compactification P f
  Etale.dualizingComplex P.Coefficient f

/-- The specified counit mate theta in omega-first order, as in the published API.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorMap
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
      (omega P f)).obj ((pull P f).obj K) ⟶ (exceptional P f).obj K :=
  letI := compactification P f
  Etale.dualizingComplexTensorMap P.Coefficient f K

/-- Construct the canonical graph-normalized support comparison before specializing
the coefficient ring. Its sheaf graph extension and homotopy descent are the specified
canonical construction, so no representative is selected from an existence theorem.
Source: lem-asd-etale-compact-support-normalization, canonical graph comparison
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def graphSupportModel (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  fun e _ _ _ _ c ↦ Etale.canonicalEtaleCompactSupportComparison A e c

private theorem graphSupportModel_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) :
    graphSupportModel A e c = Etale.canonicalEtaleCompactSupportComparison A e c := rfl

/-- The canonical proper-support/sum comparison. The graph-extension equation and
homotopy-representative normalization in `etaleSupportMapCompatibility` determine the
chosen comparison uniquely: this choice is of the specified map, not an arbitrary iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def support
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    lower P e ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} P.Coefficient) e
        inferInstance).mapDerivedCategory :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  letI := compactification P e
  (Etale.rightDerivedLowerShriekIso P.Coefficient
      (HasCompactification.compactification e)).symm ≪≫
    graphSupportModel P.Coefficient e
      (HasCompactification.compactification e)

/-- The unique counit-preserving comparison: conjugate of inverse proper-support/sum,
then the inverse exact-to-left-derived restriction comparison. No purity is used.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def rho
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    exceptional P e ≅ pull P e :=
  letI := compactification P e
  conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
      ((Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) e inferInstance).mapDerivedCategoryAdjunction)
      (support P e).symm ≪≫
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) e).symm

/-- Eta is rho at the coefficient unit followed by the canonical pullback-unit iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def eta
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e] :
    omega P e ≅ coefficientUnit (ModuleCat.{u + 1} P.Coefficient) X :=
  (rho P e).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
    Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) e

/-- The exceptional compositor is precisely the conjugate of the specified
compact-support compositor, whose origin transport is `originCompositionModel`.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def comp
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    exceptional P (f ≫ g) ≅ exceptional P g ⋙ exceptional P f :=
  letI := compactification P f
  letI := compactification P g
  letI := compactification P (f ≫ g)
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (f ≫ g))
    ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).comp
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient g))
    (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f g)

/-- Canonical exceptional comparison for equal composites, by conjugacy of support
congruence. This inserts only the equality of morphisms in a Cartesian square.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def congr
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (w : f = g) :
    exceptional P f ≅ exceptional P g :=
  letI := compactification P f
  letI := compactification P g
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient g)
    (Etale.unboundedEtaleLowerShriekCongr P.Coefficient w.symm)

/-- Sigma is the specified tensor mate followed by inverse exceptional composition.
The finite coefficient ring is fixed before any specialization, preserving its unit instance.
Source: main-20261015, etale-locality Step 1, definition of sigma
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sigma
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [cf : HasCompactification f] [cg : HasCompactification g]
    [cfg : HasCompactification (f ≫ g)]
    (c : Etale.rightDerivedUpperShriek Λ (f ≫ g) ≅
      Etale.rightDerivedUpperShriek Λ g ⋙ Etale.rightDerivedUpperShriek Λ f) :=
  Etale.dualizingComplexTensorMap Λ f (Etale.dualizingComplex Λ g) ≫
    c.inv.app (𝟙_ _)

/-- The tensor normalization equation, assembled with one finite coefficient ring
before specialization. The comparison argument is the actual rho, and its
unit component is eta. Source: main-20261015, etale-locality Step 1, clause (1)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def tensorUnitEquation
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (e : X ⟶ Y) [ce : HasCompactification e]
    (r : Etale.rightDerivedUpperShriek Λ e ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  Etale.dualizingComplexTensorMap Λ e K ≫ r.hom.app K =
    tensorUnitMap (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ e)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj K)
      (r.app (coefficientUnit (ModuleCat.{u + 1} Λ) Y) ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e)

/-- The source-etale sigma equation with its actual compositor and rho supplied.
The left side expands E as c at the unit followed by rho at omega_h. Source:
main-20261015, etale-locality Step 1, clause (3)
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sourceEtaleEquation
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (h : Y ⟶ Z)
    [ce : HasCompactification e] [ch : HasCompactification h]
    [ceh : HasCompactification (e ≫ h)]
    (r : Etale.rightDerivedUpperShriek Λ e ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor)
    (c : Etale.rightDerivedUpperShriek Λ (e ≫ h) ≅
      Etale.rightDerivedUpperShriek Λ h ⋙ Etale.rightDerivedUpperShriek Λ e) : Prop :=
  sigma Λ e h c ≫ c.hom.app (coefficientUnit (ModuleCat.{u + 1} Λ) Z) ≫
      r.hom.app (Etale.dualizingComplex Λ h) =
    tensorUnitMap (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ e)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ h))
      (r.app (coefficientUnit (ModuleCat.{u + 1} Λ) Y) ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e)

/-- The source-etale comparison E is c at the unit followed by rho at omega_h.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def sourceEtale
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    omega P (e ≫ h) ≅ (pull P e).obj (omega P h) :=
  (comp P e h).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
    (rho P e).app (omega P h)

/-- The specified exceptional base-change natural transformation, with both
compactifications supplied from the given finite-type field setting.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def baseChange
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (sq : IsPullback g₁ f₁ f g) :
    exceptional P f ⋙ pull P g₁ ⟶ pull P g ⋙ exceptional P f₁ :=
  letI := compactification P f
  letI := compactification P f₁
  Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq

/-- The specified dualizing base-change mate beta, including the pullback-unit map.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def beta
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (sq : IsPullback g₁ f₁ f g) :
    (pull P g₁).obj (omega P f) ⟶ omega P f₁ :=
  (baseChange P f f₁ g g₁ sq).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≫
    (exceptional P f₁).map
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) g).hom

/-- The target unit identification, assembled from rho at the unit, the canonical
pullback-unit comparisons and the tensor right unitor, before specialization.
Source: main-20261015, etale-locality Step 1, coefficient-unit identifications
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def targetUnit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)
    [cf : HasCompactification f] [ce : HasCompactification e]
    (r : Etale.rightDerivedUpperShriek Λ e ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj (Etale.dualizingComplex Λ f)).mapIso
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.mapIso
          (r.app (𝟙_ _) ≪≫ Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e) ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f) ≪≫
    Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X (Etale.dualizingComplex Λ f)

/-- The canonical exceptional identity identification, conjugate of support identity.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def exceptionalId
    {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] :
    exceptional P (𝟙 X) ≅ 𝟭 (Etale.DerivedCategoryModule P.Coefficient X) :=
  letI := compactification P (𝟙 X)
  conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (𝟙 X))
    (Adjunction.id : (𝟭 (Etale.DerivedCategoryModule P.Coefficient X)) ⊣ 𝟭 _)
    (Etale.unboundedEtaleLowerShriekId P.Coefficient X).symm

/-- The canonical identity identification for derived pullback.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def pullId (X : Scheme.{u}) :
    pull P (𝟙 X) ≅ 𝟭 (Etale.DerivedCategoryModule P.Coefficient X) :=
  Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} P.Coefficient) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Test the original pro-etale Dctf domain on all etale-origin representatives.
This is the domain convention of def-pur-co-smoothness, with no separatedness added.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def domain (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule P.Coefficient X) : Prop :=
  ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X
    ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K)

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

namespace AlgebraicGeometry.ProEtale

open FiniteEtaleNormalization

namespace FiniteEtaleNormalization.Laws

/-- The counit uniquely normalizes rho, on every object of the original domain.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (support P e).hom.app ((exceptional P e).obj K) ≫
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} P.Coefficient) e
        inferInstance).mapDerivedCategory.map
        ((rho P e).hom.app K ≫
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) e).hom.app K) ≫
      ((Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) e
          inferInstance).mapDerivedCategoryAdjunction).counit.app K =
        (FiniteEtaleNormalization.counit P e).app K

/-- Clause (1) in the published omega-first tensor order (the node uses symmetry).
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def TensorUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    tensorUnitEquation P.Coefficient e
      (ce := compactification P e) (rho P e) K

/-- Clause (2), identity, with both canonical identity comparisons inserted.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Identity
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀ (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (rho P (𝟙 X)).hom.app K ≫ (pullId P X).hom.app K =
      (exceptionalId P).hom.app K

/-- Clause (2), actual rho composition, not merely pullback composition.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def Composition
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {T : Scheme.{u}}
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (v : X ⟶ T) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Etale v]
    (K : Etale.DerivedCategoryModule P.Coefficient T), domain P T K →
    (rho P (e ≫ v)).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e v).hom.app K =
      (comp P e v).hom.app K ≫ (rho P e).hom.app ((exceptional P v).obj K) ≫
        (pull P e).map ((rho P v).hom.app K)

/-- Clause (2), eta under every allowed Cartesian change of base.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def EtaBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {U₁ X₁ : Scheme.{u}}
    [U₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₁ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    (e₁ : U₁ ⟶ X₁) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (w : X₁ ⟶ X) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (w₁ : U₁ ⟶ U) [w₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated w₁] [LocallyOfFiniteType w₁] [QuasiCompact w₁]
    (sq : IsPullback w₁ e₁ e w),
    beta P e e₁ w w₁ sq ≫ (eta P e₁).hom =
      (pull P w₁).map (eta P e).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) w₁).hom

/-- Clause (3), E sigma is exactly tensoring eta with the identity.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def SourceEtale
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {S : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (h : X ⟶ S) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    , sourceEtaleEquation P.Coefficient e h
        (ce := compactification P e) (ch := compactification P h)
        (ceh := compactification P (e ≫ h)) (rho P e) (comp P e h)

/-- The sigma inverse in clause (3) exists for this particular canonical map.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def TargetSigmaIsIso
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {R R₁ : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [R₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (R₁ ↘ Spec (.of P.field.k))]
    (h : R ⟶ X) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    (h₁ : R₁ ⟶ U) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    [Smooth h₁]
    (e₁ : R₁ ⟶ R) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (_sq : IsPullback e₁ h₁ h e), IsIso (sigma P.Coefficient h₁ e
        (cf := compactification P h₁) (cg := compactification P e)
        (cfg := compactification P (h₁ ≫ e)) (comp P h₁ e))

/-- Clause (3), inverse-free form of beta = sigma inverse composed with E inverse.
`targetUnit.inv` inserts exactly the target identification via eta_e.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def SmoothBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {R R₁ : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [R₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (R₁ ↘ Spec (.of P.field.k))]
    (h : R ⟶ X) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Smooth h]
    (h₁ : R₁ ⟶ U) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    [Smooth h₁]
    (e₁ : R₁ ⟶ R) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (sq : IsPullback e₁ h₁ h e),
    beta P h h₁ e e₁ sq ≫ (targetUnit P.Coefficient h₁ e
        (cf := compactification P h₁) (ce := compactification P e) (rho P e)).inv ≫
      sigma P.Coefficient h₁ e
        (cf := compactification P h₁) (cg := compactification P e)
        (cfg := compactification P (h₁ ≫ e)) (comp P h₁ e) =
      (sourceEtale P e₁ h).inv ≫ (congr P (e₁ ≫ h) (h₁ ≫ e) sq.w).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _)

/-- Genuine open restriction: compare rho on the pulled-back map with restricted rho,
through the specified exceptional base change and the canonical pullback square.
Source: main-20261015, etale-locality Step 1, the corresponding displayed identity
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
def OpenRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop :=
  ∀
    {U₁ X₁ : Scheme.{u}}
    [U₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₁ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    (e₁ : U₁ ⟶ X₁) [e₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₁] [LocallyOfFiniteType e₁] [QuasiCompact e₁]
    [Etale e₁]
    (j : X₁ ⟶ X) [j.IsOver (Spec (.of P.field.k))]
    [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (j₁ : U₁ ⟶ U) [j₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated j₁] [LocallyOfFiniteType j₁] [QuasiCompact j₁]
    [IsOpenImmersion j] [IsOpenImmersion j₁]
    (sq : IsPullback j₁ e₁ e j)
    (K : Etale.DerivedCategoryModule P.Coefficient X), domain P X K →
    (baseChange P e e₁ j j₁ sq).app K ≫ (rho P e₁).hom.app ((pull P j).obj K) =
      (pull P j₁).map ((rho P e).hom.app K) ≫
        Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq K

end FiniteEtaleNormalization.Laws

namespace FiniteEtaleNormalization

open Etale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

set_option backward.isDefEq.respectTransparency.types false in
private theorem exactFactorh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (_root_.DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        _root_.DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : _root_.DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    _root_.DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  change (𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ 𝟙 _) =
    F.mapDerivedCategoryFactors.hom.app P
  simp only [Category.id_comp, Category.comp_id]

private theorem exactAdjCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex D ℤ) :
    a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) := by
  have h := a.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  change a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) = _ at h
  rw [h]
  change F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) = _
  rw [exactFactorh, exactFactorh]

private theorem exactAdjLocalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    : let _ : CatCommSq (F.mapHomologicalComplex (.up ℤ))
        _root_.DerivedCategory.Q _root_.DerivedCategory.Q F.mapDerivedCategory :=
          ⟨F.mapDerivedCategoryFactors.symm⟩
      let _ : CatCommSq (G.mapHomologicalComplex (.up ℤ))
        _root_.DerivedCategory.Q _root_.DerivedCategory.Q G.mapDerivedCategory :=
          ⟨G.mapDerivedCategoryFactors.symm⟩
      (a.mapHomologicalComplex (.up ℤ)).localization
          _root_.DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
          _root_.DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
          F.mapDerivedCategory G.mapDerivedCategory = a.mapDerivedCategoryAdjunction := by
  dsimp only
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ))
  intro K
  rw [exactAdjCounit]
  simp only [Adjunction.localization_counit_app, CatCommSq.iso, Iso.symm_inv]

private theorem derivedAdj_eq (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction =
      derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance := by
  symm
  unfold derivedEtaleLowerShriekUpperStarAdjunction
  exact exactAdjLocalization
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)

section
variable
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]

variable [HasCompactification e] [IsNoetherian U] [IsNoetherian X]

attribute [local irreducible] Etale.canonicalEtaleCompactSupportComparison

set_option linter.unusedSectionVars false in
private theorem support_eq :
    support P e = Etale.etaleSumSupportIso P.Coefficient e
       := by
  simp only [support, Etale.etaleSumSupportIso, graphSupportModel_eq]

private theorem rho_exact :
    rho P e ≪≫ Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) e =
      Etale.etaleSumRightAdjointIso P.Coefficient e (exceptional P e)
        (Etale.rightDerivedUpperShriekAdjunction _ e)
         := by
  simp only [rho, support_eq, Etale.etaleSumRightAdjointIso, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
  rw [derivedAdj_eq]

private theorem eta_sum :
    Etale.etaleSumRightAdjointUnitIso P.Coefficient e (exceptional P e)
      (Etale.rightDerivedUpperShriekAdjunction _ e) = eta P e := by
  unfold Etale.etaleSumRightAdjointUnitIso
  rw [← rho_exact P e]
  apply Iso.ext
  simp only [Etale.etaleSumPullbackUnitIso, eta, Etale.constantComplex,
    coefficientUnit, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem support_chosen :
    support P e = Etale.canonicalEtaleCompactSupportComparison P.Coefficient e
      (HasCompactification.compactification e) := by
  rw [support_eq]
  unfold Etale.etaleSumSupportIso Etale.rightDerivedLowerShriekIso
  rw [(Etale.unboundedEtaleCompactSupport_comparison_coherence P.Coefficient e).1]
  exact Iso.refl_trans _

private theorem rho_tensor :
    rho P e ≪≫ Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) e =
      Etale.etaleTensorRho P.Coefficient e (HasCompactification.compactification e)
        (exceptional P e) (Etale.rightDerivedUpperShriekAdjunction _ e) := by
  simp only [rho, support_chosen, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl,
    Etale.etaleTensorRho, ← derivedAdj_eq]
  rfl

private theorem rho_canonical :
    conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction
        P.Coefficient e)
      (Etale.derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) e inferInstance)
      (Etale.etaleCanonicalCompactSupportComparison P.Coefficient e
        (Etale.canonicalEtaleCompactSupportNormalization P.Coefficient)).symm =
    rho P e ≪≫ Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) e := by
  rw [rho_exact]
  unfold Etale.etaleSumRightAdjointIso
  congr 1

attribute [local irreducible] rho support Etale.etaleTensorRho Etale.etaleTensorTau
  conjugateIsoEquiv Adjunction.mapDerivedCategoryAdjunction
  Etale.rightDerivedUpperShriekAdjunction Etale.leftDerivedUpperStarIsoMapDerivedCategory

private theorem tensor_eta :
    Etale.etaleTensorEta P.Coefficient e (HasCompactification.compactification e)
      (exceptional P e) (Etale.rightDerivedUpperShriekAdjunction _ e) = eta P e := by
  unfold Etale.etaleTensorEta
  rw [← rho_tensor P e]
  apply Iso.ext
  simp only [Etale.etaleSumPullbackUnitIso, eta, Etale.constantComplex,
    coefficientUnit, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem tensor_transpose (K : Etale.DerivedCategoryModule P.Coefficient X) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) U).obj (omega P e)).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) e).hom.app K) ≫
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} P.Coefficient) U).hom.app
        (omega P e)).app
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).mapDerivedCategory.obj K) ≫
      Etale.etaleTensorTau P.Coefficient e (HasCompactification.compactification e)
        (exceptional P e) (Etale.rightDerivedUpperShriekAdjunction _ e) K =
      Etale.dualizingComplexTensorMap P.Coefficient e K := by
  have hθ := tensorCanonicalTranspose P.Coefficient e K
  simpa only [Etale.etaleTensorTau, Etale.etaleTensorInverseTranspose,
    Etale.etaleTensorProjection, Etale.dualizingComplexTensorMap,
    Etale.constantComplex, coefficientUnit,
    omega, Etale.dualizingComplex, exceptional, Iso.app_hom, Functor.id_obj,
    Etale.rightDerivedLowerShriek, Etale.projectionMap, Functor.flip_obj_obj] using hθ

private theorem tensor_law (K : Etale.DerivedCategoryModule P.Coefficient X) :
    tensorMap P e K ≫ (rho P e).hom.app K =
      tensorUnitMap (ModuleCat.{u + 1} P.Coefficient) U (omega P e)
        ((pull P e).obj K) (eta P e) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let i := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).app K
  let tau := Etale.etaleTensorTau P.Coefficient e (HasCompactification.compactification e)
    (exceptional P e) (Etale.rightDerivedUpperShriekAdjunction _ e) K
  have ht := (Etale.etaleSumRightAdjointTensor P.Coefficient e
    (HasCompactification.compactification e)
    (exceptional P e) (Etale.rightDerivedUpperShriekAdjunction _ e)).2.1 K
  rw [tensor_eta P e, ← rho_tensor P e] at ht
  simp only [Iso.trans_hom, NatTrans.comp_app] at ht
  have hout := tensorNormalizationDerived C U i ((rho P e).app K) (eta P e) tau
    (Etale.dualizingComplexTensorMap P.Coefficient e K) ht (tensor_transpose P e K)
  exact hout

attribute [local irreducible] Etale.derivedTensor Etale.derivedTensorRightUnitor
  Etale.leftDerivedUpperStarUnitIso

set_option linter.unusedSectionVars false in
private theorem pull_comp_transport
    {T : Scheme.{u}} (v : X ⟶ T) (K : Etale.DerivedCategoryModule P.Coefficient T) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e v).hom.app K ≫
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) e).hom.app ((pull P v).obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) v).hom.app K) =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (e ≫ v)).hom.app K ≫
      (Etale.unboundedEtaleUpperStarCompIso P.Coefficient e v).hom.app K := by
  simp only [Etale.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Etale.leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    Etale.unboundedEtaleUpperStarCompIso]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

end
end FiniteEtaleNormalization

namespace FiniteEtaleNormalization

open Etale

private theorem lowerCongr_symm
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    (Etale.unboundedEtaleLowerShriekCongr A w).inv =
      (Etale.unboundedEtaleLowerShriekCongr A w.symm).hom := by
  subst w
  rfl

private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

private theorem pull_square_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K ≫
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) f').hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) f').mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) g).hom.app K) =
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g').hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (Etale.exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K := by
  simp only [Etale.derivedSquareUpperStarIso, Etale.leftDerivedUpperStarComp,
    Etale.exactDerivedSquareUpperStarIso, Etale.squareUpperStarIso,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Etale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
    derived_iso_trans, derived_iso_symm,
    Iso.inv_hom_id_app_assoc]
  simp only [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

private theorem chosen_support_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w) :
    Etale.unboundedEtaleCompactSupportBaseChange A sq =
      (Etale.etaleNormalizedSupportExchange A sq (HasCompactification.compactification e)
        (HasCompactification.compactification e')).hom := by
  have h := (Etale.unboundedEtaleCompactSupport_baseChange A sq).2
    (HasCompactification.compactification e)
  rw [Etale.rightDerivedLowerShriekIso,
    (Etale.unboundedEtaleCompactSupport_comparison_coherence A e).1] at h
  ext M
  have hh := NatTrans.congr_app h M
  simp only [Iso.refl_inv, Etale.unboundedEtaleCompactSupportExchange,
    Etale.etaleNormalizedSupportExchange, Etale.rightDerivedLowerShriekIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, asIso_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Category.assoc,
    Etale.rightDerivedLowerShriek] at hh ⊢
  have hid := (Etale.upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map_id
    ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification e)).obj M)
  erw [hid, Category.id_comp] at hh
  exact hh

private theorem baseChange_exact
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (sq : IsPullback g₁ f₁ f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X₁] [IsNoetherian Y₁]
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (baseChange P f f₁ g g₁ sq).app K ≫
        (exceptional P f₁).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) g).hom.app K) =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) g₁).hom.app ((exceptional P f).obj K) ≫
        (Etale.etaleHorizontalCounitRightExchange P.Coefficient sq
          (Etale.rightDerivedUpperShriekAdjunction _ f)
          (Etale.rightDerivedUpperShriekAdjunction _ f₁)).app K := by
  let := compactification P f
  let := compactification P f₁
  let C := ModuleCat.{u + 1} P.Coefficient
  let i := Etale.leftDerivedUpperStarIsoMapDerivedCategory C g₁
  let j := Etale.leftDerivedUpperStarIsoMapDerivedCategory C g
  let B := Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  have ht := mateTransport (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f₁) i j (inv B)
  have := (Etale.unboundedEtaleCompactSupport_baseChange P.Coefficient sq).1
  have hinv : inv (Etale.unboundedEtaleCompactSupportBaseChange P.Coefficient sq) =
      Functor.whiskerRight i.inv _ ≫ inv B ≫ Functor.whiskerLeft _ j.hom := by
    ext M
    apply (cancel_epi
      ((Etale.unboundedEtaleCompactSupportBaseChange P.Coefficient sq).app M)).1
    simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id]
    simp only [Etale.unboundedEtaleCompactSupportBaseChange,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc]
    dsimp only [C, i, j, B]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, NatIso.isIso_inv_app,
      IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app]
    rfl
  rw [← hinv] at ht
  have hh := NatTrans.congr_app ht K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
  apply (cancel_epi (i.inv.app ((exceptional P f).obj K))).1
  simp only [C, i, Iso.inv_hom_id_app_assoc]
  simpa only [baseChange, Etale.rightDerivedUpperShriekBaseChangeMap,
    Etale.etaleHorizontalCounitRightExchange, Etale.etaleHorizontalSupportBaseChangeIso,
    asIso_inv, C, i, j, B, TwoSquare.natTrans] using hh.symm

private theorem sum_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [Etale f] [IsSeparated f] [QuasiCompact f] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f'] (sq : IsPullback g' f' f g)
    (G : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (G' : Etale.DerivedCategoryModule A Y' ⥤ Etale.DerivedCategoryModule A X')
    (a : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ G)
    (a' : Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' ⊣ G') :
    Etale.etaleSumRightAdjointBaseChange A sq G G' a a' =
      (Etale.etaleHorizontalCounitRightExchange A sq a a').app
          (Etale.constantComplex A Y) ≫
        G'.map (Etale.etaleSumPullbackUnitIso A g).hom := by
  have := (Etale.unboundedEtaleCompactSupport_baseChange A sq).1
  unfold Etale.etaleSumRightAdjointBaseChange
  rw [← Category.assoc, a'.homEquiv_naturality_right]
  apply congrArg (fun q ↦ q ≫ G'.map (Etale.etaleSumPullbackUnitIso A g).hom)
  simpa only [NatIso.isIso_inv_app,
    Etale.etaleHorizontalCounitRightExchange,
    Etale.etaleHorizontalSupportBaseChangeIso, asIso_inv, TwoSquare.mk,
    TwoSquare.natTrans, Functor.id_obj, Functor.comp_obj] using
    (mateApp a a' (inv (Etale.unboundedEtaleCompactSupportBaseChange A sq))
      (Etale.constantComplex A Y)).symm

section
variable
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]

attribute [local irreducible] rho support conjugateIsoEquiv
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Etale.leftDerivedUpperStarIsoMapDerivedCategory Etale.lowerShriekRightAdjointUnitTensorMap

private theorem eta_baseChange_law : Laws.EtaBaseChange P e := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  intro U₁ X₁ _ _ _ _ _ _ e₁ _ _ _ _ _ w _ _ _ _ w₁ _ _ _ _ sq
  let := fieldSchemeNoetherian P U₁
  let := fieldSchemeNoetherian P X₁
  let := compactification P e₁
  have hb := Etale.etaleSumRightAdjoint_baseChange P.Coefficient sq
    (exceptional P e) (exceptional P e₁)
    (Etale.rightDerivedUpperShriekAdjunction _ e)
    (Etale.rightDerivedUpperShriekAdjunction _ e₁)
  rw [eta_sum P e, eta_sum P e₁] at hb
  let C := ModuleCat.{u + 1} P.Coefficient
  have hu : (Etale.leftDerivedUpperStarUnitIso C w).hom =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory C w).hom.app
          (Etale.constantComplex P.Coefficient X) ≫
        (Etale.etaleSumPullbackUnitIso P.Coefficient w).hom := by
    simp only [Etale.etaleSumPullbackUnitIso, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, C, Iso.hom_inv_id_app_assoc]
  have hbexact := baseChange_exact P e e₁ w w₁ sq
    (Etale.constantComplex P.Coefficient X)
  have hbeta := congrArg
    (fun q ↦ q ≫ (exceptional P e₁).map
      (Etale.etaleSumPullbackUnitIso P.Coefficient w).hom) hbexact
  simp only [Category.assoc, ← Functor.map_comp] at hbeta
  erw [← hu] at hbeta
  change beta P e e₁ w w₁ sq = _ at hbeta
  rw [hbeta, Category.assoc, ← sum_baseChange P.Coefficient sq, hb]
  rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) w₁).hom.naturality_assoc]
  simp only [Etale.etaleSumPullbackUnitIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.hom_inv_id_app_assoc]

private theorem source_etale_law : Laws.SourceEtale P e := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  intro S _ _ _ h _ _ _ _ _
  let := compactification P h
  let := compactification P (e ≫ h)
  have ht := tensor_law P e (omega P h)
  simp only [sourceEtaleEquation, sigma, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact ht

private theorem target_sigma_law : Laws.TargetSigmaIsIso P e := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  intro R R₁ _ _ _ _ _ _ h _ _ _ _ _ h₁ _ _ _ _ _ e₁ _ _ _ _ _ sq
  obtain ⟨s, hs, _, _⟩ := P.dualizingComposite_inverse h₁ e (eta P e)
  have he : sigma P.Coefficient h₁ e (comp P h₁ e) =
      WeilConjectures.PurityFiniteSetting.dualizingCompositeSigma P.Coefficient h₁ e := by
    simp only [sigma, WeilConjectures.PurityFiniteSetting.dualizingCompositeSigma,
      WeilConjectures.PurityFiniteSetting.dualizingCompositeConjugate,
      WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition, comp,
      Etale.dualizingComplexTensorMap, Iso.app_inv]
  rw [he, ← hs]
  infer_instance

private theorem smooth_baseChange_law : Laws.SmoothBaseChange P e := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  intro R R₁ _ _ _ _ _ _ h _ _ _ _ _ h₁ _ _ _ _ _ e₁ _ _ _ _ _ sq
  let := fieldSchemeNoetherian P R
  let := fieldSchemeNoetherian P R₁
  let := compactification P h
  let := compactification P h₁
  let := compactification P e₁
  let := compactification P (e₁ ≫ h)
  let := compactification P (h₁ ≫ e)
  let C := ModuleCat.{u + 1} P.Coefficient
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  let cs : ChosenCartesianSquare e₁ h₁ h e :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hd := Etale.etaleHorizontalDoubleCounit_compositors P.Coefficient cs N
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h₁)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e₁)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e₁ ≫ h))
  have hex := Etale.etaleHorizontalDoubleCounit_exchange P.Coefficient cs N
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h₁)
  obtain ⟨s, hs, hi, _⟩ := P.dualizingComposite_inverse h₁ e (eta P e)
  have hi' : (targetUnit P.Coefficient h₁ e (rho P e)).inv ≫
      sigma P.Coefficient h₁ e (comp P h₁ e) =
    (Etale.rightDerivedUpperShriek P.Coefficient h₁).map (eta P e).inv ≫
      (comp P h₁ e).inv.app (coefficientUnit C X) := by
    have hr := inverseNormalization
      (WeilConjectures.PurityFiniteSetting.dualizingCompositeTrivialization
        P.Coefficient h₁ e (eta P e)) s
      (WeilConjectures.PurityFiniteSetting.dualizingCompositeConjugate P.Coefficient h₁ e)
      ((exceptional P h₁).mapIso (eta P e)) hi
    rw [hs] at hr
    have ht : targetUnit P.Coefficient h₁ e (rho P e) =
        WeilConjectures.PurityFiniteSetting.dualizingCompositeTrivialization
          P.Coefficient h₁ e (eta P e) := by rfl
    have hσ : sigma P.Coefficient h₁ e (comp P h₁ e) =
        WeilConjectures.PurityFiniteSetting.dualizingCompositeSigma
          P.Coefficient h₁ e := by
      simp only [sigma, WeilConjectures.PurityFiniteSetting.dualizingCompositeSigma,
        WeilConjectures.PurityFiniteSetting.dualizingCompositeConjugate,
        WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition, comp,
        Etale.dualizingComplexTensorMap, Iso.app_inv]
    rw [← ht, ← hσ] at hr
    exact hr
  rw [hi']
  have hx : conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e₁ ≫ h))
      ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient h₁).comp
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e))
      (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient h₁ e ≪≫
        (Etale.unboundedEtaleLowerShriekCongr P.Coefficient sq.w).symm) =
    congr P (e₁ ≫ h) (h₁ ≫ e) sq.w ≪≫ comp P h₁ e := by
    apply Iso.ext
    simp only [FiniteEtaleNormalization.congr, comp, conjugateIsoEquiv_apply_hom, Iso.trans_hom,
      Iso.symm_hom]
    rw [lowerCongr_symm, conjugateEquiv_comp]
  rw [rho_canonical P e, rho_canonical P e₁, hx] at hd
  have heq := congrArg (fun q ↦ q.hom.app (coefficientUnit C X)) hd
  rw [hex] at heq
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] at heq
  have hb := baseChange_exact P h h₁ e e₁ sq (coefficientUnit C X)
  have hbl : (baseChange P h h₁ e e₁ sq).app (coefficientUnit C X) =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e₁).hom.app
          ((exceptional P h).obj (coefficientUnit C X)) ≫
        (Etale.etaleHorizontalCounitRightExchange P.Coefficient sq
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h₁)).app (coefficientUnit C X) ≫
        (exceptional P h₁).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).inv.app
            (coefficientUnit C X)) := by
    apply (cancel_mono ((exceptional P h₁).map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).hom.app
        (coefficientUnit C X)))).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact hb
  have hc := exchangeCancellation (exceptional P h₁)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e₁).app (omega P h))
    ((rho P e₁).app (omega P h))
    ((comp P e₁ h).app (coefficientUnit C X))
    ((congr P (e₁ ≫ h) (h₁ ≫ e) sq.w).app (coefficientUnit C X))
    ((comp P h₁ e).app (coefficientUnit C X))
    ((rho P e).app (coefficientUnit C X))
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).app (coefficientUnit C X))
    (Etale.leftDerivedUpperStarUnitIso C e)
    ((Etale.etaleHorizontalCounitRightExchange P.Coefficient sq
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient h₁)).app (coefficientUnit C X)) heq
  simpa only [beta, hbl, sourceEtale, eta, Iso.trans_inv, Iso.app_inv,
    Iso.app_hom, Category.assoc, C, omega, Etale.dualizingComplex] using hc

end

end FiniteEtaleNormalization

attribute [local irreducible] Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction Etale.leftDerivedUpperStarIsoMapDerivedCategory
  Etale.dualizingComplex Etale.lowerShriekRightAdjointUnitTensorMap

/-- All clauses of finite etale normalization, in canonical etale-origin coordinates.
Each field is an equation of the specified morphisms. The final field compares the
restriction of rho with rho on the restricted square, using the actual exceptional
base-change mate and the canonical pullback square, rather than an endpoint iso.
Source: main-20261015, etale-locality Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
structure FiniteEtaleDualizingNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : Prop where
  /-- The counit uniquely normalizes rho, on every object of the original domain. -/
  counit : FiniteEtaleNormalization.Laws.Counit P e
  /-- Clause (1) in the published omega-first tensor order (the node uses symmetry). -/
  tensor_unit : FiniteEtaleNormalization.Laws.TensorUnit P e
  /-- Clause (2), identity, with both canonical identity comparisons inserted. -/
  identity : FiniteEtaleNormalization.Laws.Identity P e
  /-- Clause (2), actual rho composition, not merely pullback composition. -/
  composition : FiniteEtaleNormalization.Laws.Composition P e
  /-- Clause (2), eta under every allowed Cartesian change of base. -/
  eta_base_change : FiniteEtaleNormalization.Laws.EtaBaseChange P e
  /-- Clause (3), E sigma is exactly tensoring eta with the identity. -/
  source_etale : FiniteEtaleNormalization.Laws.SourceEtale P e
  /-- The sigma inverse in clause (3) exists for this particular canonical map. -/
  target_sigma_iso : FiniteEtaleNormalization.Laws.TargetSigmaIsIso P e
  /-- Clause (3), inverse-free form of beta = sigma inverse composed with E inverse.
`targetUnit.inv` inserts exactly the target identification via eta_e. -/
  smooth_base_change : FiniteEtaleNormalization.Laws.SmoothBaseChange P e
  /-- Genuine open restriction: compare rho on the pulled-back map with restricted rho,
through the specified exceptional base change and the canonical pullback square. -/
  open_restriction : FiniteEtaleNormalization.Laws.OpenRestriction P e

/-- Finite etale dualizing normalization, with no orientation or Tate twist.

Proof: finite-type schemes over the coefficient field are Noetherian. The support
model is the canonical graph-derived comparison. Comparing localized counits identifies
the two derived sum adjunctions. Conjugacy gives the counit equation; the sum-adjoint
tensor theorem, transported through the exact/left-derived comparison and symmetry,
gives the omega-first tensor equation. The sum-adjoint identity, composition and
base-change equations give their stated counterparts after the same transport.
Source-etale cancellation is the tensor equation at the dualizing object. The
canonical dualizing-composite inverse gives target sigma invertibility and its
normalized inverse formula. The horizontal double-counit compositor formula identifies
the actual exceptional base-change mate; cancellation with the normalized inverse
formula gives smooth base change. Finally, the normalized-mates open-restriction
formula and the canonical pullback-square transport give open restriction.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/
lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-finite-etale-dualizing-normalization). -/
theorem finite_etale_dualizing_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    : FiniteEtaleDualizingNormalization P e := by
  let := fieldSchemeNoetherian P U
  let := fieldSchemeNoetherian P X
  let := compactification P e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K _
    simp only [rho, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    rw [conjugateEquiv_counit]
    simp [FiniteEtaleNormalization.counit]
  · intro K _
    exact tensor_law P e K
  · intro K _
    let := compactification P (𝟙 X)
    have hi := Etale.etaleSumRightAdjoint_id P.Coefficient X
      (exceptional P (𝟙 X)) (Etale.rightDerivedUpperShriekAdjunction _ (𝟙 X))
    have := congrArg (fun q ↦ q.hom.app K) hi
    simpa only [← rho_exact P (𝟙 X), Iso.trans_hom, NatTrans.comp_app,
      pullId, exceptionalId, Etale.unboundedEtaleUpperStarIdIso, Category.assoc] using this
  · intro T _ _ _ v _ _ _ _ _ K _
    let := fieldSchemeNoetherian P T
    let := compactification P v
    let := compactification P (e ≫ v)
    let C := ModuleCat.{u + 1} P.Coefficient
    have hc := Etale.etaleSumRightAdjoint_comp P.Coefficient e v
      (exceptional P e) (exceptional P v) (exceptional P (e ≫ v))
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient v)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e ≫ v)) K
    rw [← rho_exact P (e ≫ v), ← rho_exact P e, ← rho_exact P v] at hc
    simp only [
      Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc
    let d := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).app
        ((pull P v).obj K) ≪≫ (Etale.upperStar C e).mapDerivedCategory.mapIso
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C v).app K)
    apply (cancel_mono d.hom).1
    change _ ≫ ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).hom.app
      ((pull P v).obj K) ≫ (Etale.upperStar C e).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C v).hom.app K)) = _
    rw [Category.assoc, pull_comp_transport P e v K]
    rw [hc]
    rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e).hom.naturality_assoc]
    simp only [Etale.etaleSumRightAdjointCompIso, comp, d, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, C, pull, Category.assoc]
  · exact eta_baseChange_law P e
  · exact source_etale_law P e
  · exact target_sigma_law P e
  · exact smooth_baseChange_law P e
  · intro U₁ X₁ _ _ _ _ _ _ e₁ _ _ _ _ _ j _ _ _ _ j₁ _ _ _ _ _ _ sq K _
    let := fieldSchemeNoetherian P U₁
    let := fieldSchemeNoetherian P X₁
    let := compactification P e₁
    let C := ModuleCat.{u + 1} P.Coefficient
    have ho := Etale.etaleNormalizedMates_openRestriction P.Coefficient sq
      (HasCompactification.compactification e) (HasCompactification.compactification e₁)
      (exceptional P e) (exceptional P e₁)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e₁) K
    have hr : Etale.etaleNormalizedRightExchange P.Coefficient sq
        (HasCompactification.compactification e) (HasCompactification.compactification e₁)
        (exceptional P e) (exceptional P e₁)
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e₁) =
      Etale.etaleHorizontalCounitRightExchange P.Coefficient sq
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e₁) := by
      have he : Etale.etaleNormalizedSupportExchange P.Coefficient sq
          (HasCompactification.compactification e)
          (HasCompactification.compactification e₁) =
          Etale.etaleHorizontalSupportBaseChangeIso P.Coefficient sq := by
        apply Iso.ext
        simpa only [Etale.etaleHorizontalSupportBaseChangeIso, asIso_hom] using
          (chosen_support_exchange P.Coefficient sq).symm
      simp only [Etale.etaleNormalizedRightExchange, he,
        Etale.etaleHorizontalCounitRightExchange, Etale.rightDerivedLowerShriek]
    rw [hr] at ho
    change _ ≫ (Etale.etaleTensorRho P.Coefficient e₁ _ _ _).hom.app _ =
      (Etale.upperStar C j₁).mapDerivedCategory.map
        ((Etale.etaleTensorRho P.Coefficient e _ _ _).hom.app K) ≫ _ at ho
    rw [← rho_tensor P e₁, ← rho_tensor P e] at ho
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at ho
    apply (cancel_mono ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C e₁).hom.app
      ((pull P j).obj K) ≫ (Etale.upperStar C e₁).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C j).hom.app K))).1
    simp only [Category.assoc, Etale.derivedSquareUpperStarIsoInvApp]
    rw [pull_square_transport P.Coefficient sq.toCommSq K]
    have hn := (Etale.leftDerivedUpperStarIsoMapDerivedCategory C e₁).hom.naturality
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C j).hom.app K)
    rw [← Category.assoc, ← hn, Category.assoc]
    have hrn := (rho P e₁).hom.naturality
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C j).hom.app K)
    rw [← reassoc_of% hrn]
    rw [← Category.assoc, baseChange_exact P e e₁ j j₁ sq K]
    rw [Category.assoc, ho]
    rw [← (Etale.leftDerivedUpperStarIsoMapDerivedCategory C j₁).hom.naturality_assoc]

end AlgebraicGeometry.ProEtale
