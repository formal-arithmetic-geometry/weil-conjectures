/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # The canonical module-valued Čech comparison

Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ and its proof
(blueprint: def-sc-module-cech-comparison).

The Čech complex of an `O_X`-module `F` for a family `U` of opens is the source's
`(cechComplexFunctor U).obj F.presheafModuleCat` (Mathlib's Čech complex of the presheaf of
`Γ(X, ⊤)`-modules `F.presheafModuleCat`), as in `nonempty_cechComplex_linearEquiv_H`.

## Main definitions and statements

- `cechComplexFunctor_presheafModuleCat_additive`: the Čech complex is additive in `F`.
- `moduleCechDouble`: the Čech double complex of an injective resolution.
- `moduleCechAlpha`, `moduleCechBeta`: the restrictions and augmentation into its total.
- `moduleCechAlpha_isIso`: `H^p(α)` is invertible for an open cover.
- `IsModuleCechComparison`: a map `Ȟ^p(U, F) ⟶ H^p(X, F)` is the canonical comparison
  `H^p(β) ∘ H^p(α)⁻¹` (composed with the resolution identification), for every injective
  resolution.

## Implementation notes

The comparison is characterized by `c ≫ (resolution identification) ≫ H^p(α) = H^p(β)` rather
than defined as `H^p(β) ≫ inv H^p(α) ≫ …`: `inv` of a morphism whose invertibility is not yet
proved would be data chosen from an unproved statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The Čech complex of the presheaf of `Γ(X, ⊤)`-modules underlying an `O_X`-module is
additive in the module. Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison).
Proof: the cochain maps apply the module morphism on each component; therefore they
preserve zero and addition, and equality of maps follows from the product projections. -/
theorem cechComplexFunctor_presheafModuleCat_additive (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) :
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U).Additive := by
  constructor
  intro F G f g
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro y
  simp [CategoryTheory.cechComplexFunctor, ← Preadditive.comp_add]
  rfl

attribute [instance] cechComplexFunctor_presheafModuleCat_additive

/-- The double complex `C^q(U, I^p)` with resolution degree first and Čech degree second.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechDouble {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : InjectiveResolution F) :
    HomologicalComplex₂ (ModuleCat.{u} Γ(X, ⊤)) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

/-- Restriction of the structure sheaf from the whole space to itself is the identity.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison).
Proof: the unique initial morphism from the whole open set to itself is the identity;
functoriality of the structure sheaf sends it to the identity ring morphism. -/
theorem moduleCech_top_restriction (X : Scheme.{u}) :
    (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤) := by
  have h : isTerminalTop.op.to (op ⊤) = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [h]
  change (X.ringCatSheaf.obj.map (𝟙 _)).hom = _
  rw [X.ringCatSheaf.obj.map_id]
  rfl


/-- Restrictions of a global section, as a zero cochain.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechZero {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F ⟶
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).X 0 :=
  (ModuleCat.restrictScalarsId'App
      (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom
      (moduleCech_top_restriction X) (F.val.obj (op ⊤))).inv ≫
    Pi.lift fun y : Fin 1 → ι =>
      F.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op

/-- Components of the map from global sections of the resolution to its Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechAlphaComponent {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F) (n : ℕ) :
    (RingedSpace.globalSectionsComplex I).X n ⟶
      ((moduleCechDouble U I).total (ComplexShape.up ℕ)).X n :=
  moduleCechZero U (I.cocomplex.X n) ≫
    (moduleCechDouble U I).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)

/-- The alpha components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-module-cech-comparison).
Proof: restrictions commute with the resolution differential. The Čech differential
of the restrictions of a global section is zero. The total differential on the (n,0)
summand is the resolution differential plus (-1)^n times that zero differential. -/
theorem moduleCechAlpha_comm {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : InjectiveResolution F) (n m : ℕ) :
    moduleCechAlphaComponent U I n ≫
        ((moduleCechDouble U I).total (ComplexShape.up ℕ)).d n m =
      (RingedSpace.globalSectionsComplex I).d n m ≫ moduleCechAlphaComponent U I m := by
  sorry

/-- The map alpha of Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechAlpha {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : InjectiveResolution F) :
    RingedSpace.globalSectionsComplex I ⟶
      (moduleCechDouble U I).total (ComplexShape.up ℕ) where
  f := moduleCechAlphaComponent U I
  comm' := fun n m _ => moduleCechAlpha_comm U I n m

/-- Components of the augmentation beta into the Čech total complex.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechBetaComponent {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).X n ⟶
      ((moduleCechDouble U I).total (ComplexShape.up ℕ)).X n :=
  ((CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (I.ι.f 0).val)).f n ≫
    (moduleCechDouble U I).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

/-- The beta components commute with the differential. Source: Stacks 01EQ
(blueprint: def-sc-module-cech-comparison).
Proof: Čech differentials commute with the augmentation. The augmentation followed by
the resolution differential is zero. On the (0,n) summand the Čech differential has sign +1. -/
theorem moduleCechBeta_comm {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : InjectiveResolution F) (n m : ℕ) :
    moduleCechBetaComponent U I n ≫
        ((moduleCechDouble U I).total (ComplexShape.up ℕ)).d n m =
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d n m ≫
        moduleCechBetaComponent U I m := by
  by_cases h : n + 1 = m
  · subst m
    dsimp [moduleCechBetaComponent]
    rw [HomologicalComplex₂.total_d, Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [HomologicalComplex₂.d₁_eq' _ _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
      HomologicalComplex₂.d₂_eq _ _ 0 (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
        (n + 1) (by simp)]
    simp only [PresheafOfModules.forgetToPresheafModuleCat_map, ComplexShape.ε₁_def,
      one_smul, ComplexShape.ε₂_def, ComplexShape.ε_zero, Preadditive.comp_add]
    let T := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    have hz : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
      simp
    have hz' : (T.map (I.ι.f 0)).f n ≫ (T.map (I.cocomplex.d 0 1)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, ← T.map_comp, hz, T.map_zero]
      rfl
    have hc := (T.map (I.ι.f 0)).comm n (n + 1)
    change (T.map (I.ι.f 0)).f n ≫ (T.map (I.cocomplex.d 0 1)).f n ≫ _ +
      (T.map (I.ι.f 0)).f n ≫ (T.obj (I.cocomplex.X 0)).d n (n + 1) ≫ _ = _
    rw [← Category.assoc, hz', zero_comp, zero_add, ← Category.assoc, hc,
      Category.assoc]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h]
    simp

/-- The map beta of Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
noncomputable def moduleCechBeta {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F : X.Modules} (I : InjectiveResolution F) :
    (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (moduleCechDouble U I).total (ComplexShape.up ℕ) where
  f := moduleCechBetaComponent U I
  comm' := fun n m _ => moduleCechBeta_comm U I n m

/-- Alpha induces isomorphisms on cohomology for every open cover. Source: Stacks 01EQ,
using injective Čech acyclicity 01EP (blueprint: def-sc-module-cech-comparison).
Proof: each injective resolution term is Čech-acyclic and its zeroth Čech cohomology is
its global sections by gluing. The map alpha thus induces an isomorphism on every row
cohomology. The first-quadrant spectral sequence comparison gives an isomorphism on
all finite filtration quotients, and induction on the filtration gives the result. -/
theorem moduleCechAlpha_isIso {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {F : X.Modules} (I : InjectiveResolution F) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) p) := by
  sorry

/-- A map `c : Ȟ^p(U, F) ⟶ H^p(X, F)` is the canonical comparison of Stacks 01EQ: for every
injective resolution `F → I^•`, `c` followed by the identification `H^p(X, F) ≅ H^p(Γ(X, I^•))`
and by `H^p(α)` is `H^p(β)`; that is, `c = H^p(β) ≫ H^p(α)⁻¹ ≫ (identification)⁻¹`, as
`H^p(α)` is invertible for an open cover (`moduleCechAlpha_isIso`).
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
def IsModuleCechComparison {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) (p : ℕ)
    (c : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) : Prop :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  ∀ I : InjectiveResolution F,
    c ≫ (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).hom ≫
        HomologicalComplex.homologyMap (moduleCechAlpha U I) p =
      HomologicalComplex.homologyMap (moduleCechBeta U I) p

end AlgebraicGeometry.Scheme.Modules
