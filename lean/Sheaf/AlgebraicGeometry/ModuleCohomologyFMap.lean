/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.PQFCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Maps on module cohomology induced by scheme maps

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8, 01FA, 01FB, 01EZ
(blueprint: def-weil-pbc-module-cohomology-fmap).

Nonnegative complexes are encoded by Mathlib's natural-number indexed complexes.
The choices in the resolution construction are bundled below; only their existence is
postponed. The map itself is the induced horizontal map followed by the inverse of the
induced vertical map, transported through the standard resolution comparisons.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Choices for the construction of the cohomology map of an `h`-map. The comparison `a`
is the identity on sections, using `h⁻¹(Y) = X`. The component formula pins it to this
canonical comparison, rather than an arbitrary isomorphism.
Source: Stacks Project, Tag 01FB (blueprint: def-weil-pbc-module-cohomology-fmap). -/
structure ModuleCohomologyFMapData {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : G ⟶ (pushforward h).obj F) where
  I : InjectiveResolution F
  J : InjectiveResolution G
  K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ
  injective : ∀ n : ℕ, Injective (K.X n)
  lambda : ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ K
  quasiIso : QuasiIso lambda
  β : J.cocomplex ⟶ K
  compatible : J.ι.f 0 ≫ β.f 0 = φ ≫ (pushforward h).map (I.ι.f 0) ≫ lambda.f 0
  a : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  sections : ∀ n : ℕ, a.inv.f n = (Scheme.Modules.presheaf (I.cocomplex.X n)).map
    (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op
  invertible : ∀ p : ℕ, IsIso ((HomologicalComplex.homologyFunctor
    AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map (a.hom ≫
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map lambda))

/-- The resolution choices needed for the construction exist.
Source: Stacks Project, Tags 01FB, 01EZ (blueprint: def-weil-pbc-module-cohomology-fmap).

Proof: (1) Enough injectives gives resolutions I and J of F and G, respectively
(def-sp-injective-resolutions; lem-weil-pbc-scheme-modules-enough-injectives).
(2) Resolve the nonnegative complex h_*I by a nonnegative complex K of injectives,
obtaining lambda (lem-weil-pbc-complex-injective-resolution-mono).
(3) Lift the map from G[0] to K across G[0] to J. This gives β with the displayed
augmentation equation (lem-weil-pbc-lift-along-injective-quasi-iso). The uniqueness
up to homotopy is lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.
(4) Sections of h_*I on Y are sections of I on X, with identical differentials;
these identity maps give a. By lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso,
Γ(Y, lambda) is a quasi-isomorphism. Hence all homology maps of a followed by Γ(Y, lambda)
are invertible. (5) The unit, restriction unit, and identity are module morphisms,
so the same construction applies to the three named cases. -/
theorem moduleCohomologyFMapData_nonempty {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : G ⟶ (pushforward h).obj F) : Nonempty (ModuleCohomologyFMapData h G F φ) := by
  sorry

/-- The map of cohomology groups computed from a system of choices `D`:
H(Γβ) followed by H(μ) inverse, with `μ = a ≫ Γ(Y, λ)`, transported through the
resolution comparisons `isoRightDerivedObj` and the forgetful homology comparisons.
Source: Stacks Project, Equation 01FA and Remark 01FB
(blueprint: def-weil-pbc-module-cohomology-fmap). -/
def ModuleCohomologyFMapData.map {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :=
  (forget₂ _ AddCommGrpCat.{u}).map
      (D.J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) ≫
    inv (I := D.invertible p) ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) p).map (D.a.hom ≫
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
            D.lambda)) ≫
    (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).hom ≫
    (forget₂ _ AddCommGrpCat.{u}).map
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).inv

/-- The map of cohomology groups of an `h`-map: H(Γβ) followed by H(μ) inverse, for a
system of choices whose existence is `moduleCohomologyFMapData_nonempty`.
Source: Stacks Project, Equation 01FA and Remark 01FB
(blueprint: def-weil-pbc-module-cohomology-fmap). -/
def moduleCohomologyFMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :=
  (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)).map p

/-- Pullback on module cohomology is the map of the tensor-pullback adjunction unit.
Source: Stacks Project, Tag 01F7 (blueprint: def-weil-pbc-module-cohomology-fmap). -/
def moduleCohomologyPullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap h
    ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app G) p

/-- Restriction on module cohomology is the map of the restriction-adjunction unit.
Its components are precisely restriction from V to V ∩ U.
Source: Stacks Project, Tag 01F7; Sheaves, Tag 00A1
(blueprint: def-weil-pbc-module-cohomology-fmap). -/
def moduleCohomologyRestriction {Y : Scheme.{u}} (U : Y.Opens)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p

/-- The edge map is the cohomology map of the identity on the direct image.
Source: Stacks Project, Tag 01F7 (blueprint: def-weil-pbc-module-cohomology-fmap). -/
def moduleCohomologyEdgeMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    (F : SheafOfModules.{u} X.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap h (𝟙 ((pushforward h).obj F)) p

end AlgebraicGeometry.Scheme.Modules
