/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients

/-! # Finite free resolutions of scalar models

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
ctf-equals-bc proof, Local models; Stacks Tags 03EI, 06YQ, 06YS, 06YP and 06YU
(blueprint: lem-sfb-scalar-model-finite-flat-resolution).

## Main definitions

- `CategoryTheory.siteConstantModuleFunctorIndependent`: constant modules at independent
  coefficient universe, preserving the existing dependency interface by import.
- `CategoryTheory.commutativeConstantModuleIndependent`: its commutative-ring presentation.

## Main statements

- `scalarModel_finite_flat_resolution_dvr`: the DVR resolution and tensor computation.
- `scalarModel_finite_free_field`: the field case without flatness of the algebra sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The constant module presheaf with identity restrictions, in independent universes.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def siteConstantModulePresheafIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

variable (J : GrothendieckTopology C) [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J RingCat.{r}] [HasSheafify J CommRingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}]
  [J.WEqualsLocallyBijective CommRingCat.{r}]

/-- Constant module sheafification over the constant ring sheaf.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def siteConstantModuleFunctorIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ SheafOfModules.{r}
      ((constantSheaf J RingCat.{r}).obj (RingCat.of R)) :=
  siteConstantModulePresheafIndependent (C := C) R ⋙
    PresheafOfModules.sheafification
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

/-- The same coefficient ring, formed in commutative rings before forgetting.
Source: Stacks 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev independentConstantRing (R : Type r) [CommRing R] : Sheaf J CommRingCat.{r} :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of R)

/-- The commutative-ring sheafification unit with commutativity forgotten.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def independentConstantRingUnit (R : Type r) [CommRing R] :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
        (independentConstantRing J R)).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat.{r} RingCat.{r})

-- Keep the existing instance parameters in the public interface.
set_option linter.unusedSectionVars false in
/-- Forgetting commutativity preserves local bijectivity of the coefficient unit.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-model-finite-flat-resolution).
Proof: the functions on sections and their equalizer and image covering sieves do not
change under forgetting commutativity. The ring-sheafification unit is locally bijective. -/
theorem independentConstantRingUnit_locallyBijective (R : Type r) [CommRing R] :
    Presheaf.IsLocallyInjective J (independentConstantRingUnit J R) ∧
      Presheaf.IsLocallySurjective J (independentConstantRingUnit J R) := by
  constructor
  · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J (Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{r}))
    infer_instance
  · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J (Functor.whiskerRight (toSheafify J
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) (forget CommRingCat.{r}))
    infer_instance

/-- Sheafify the same constant module presheaf over the commutative coefficient presentation.
Source: Stacks 03CY and 093T (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def commutativeConstantModuleIndependent (R : Type r) [CommRing R] :
    ModuleCat.{r} R ⥤ SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj (independentConstantRing J R)) :=
  letI := (independentConstantRingUnit_locallyBijective J R).1
  letI := (independentConstantRingUnit_locallyBijective J R).2
  siteConstantModulePresheafIndependent (C := C) R ⋙
    PresheafOfModules.sheafification (independentConstantRingUnit J R)

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- Module sheaves over the given commutative ring sheaf, using the existing category.
Source: Stacks 03DA (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelModules (B : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)

variable [EssentiallySmall.{r} C]

/-- Finite powers, including rank zero, are the existing categorical finite products.
Source: blueprint Local models (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelPower {B : Sheaf J CommRingCat.{r}}
    (N : scalarModelModules B) (n : ℕ) :=
  ∏ᶜ (fun _ : Fin n ↦ N)

/-- The two-term complex is Mathlib's double complex in precisely degrees -1 and 0.
Source: blueprint Local models (blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
abbrev scalarModelTwoTerm {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
    [HasZeroObject A] {X Y : A} (f : X ⟶ Y) : CochainComplex A ℤ :=
  HomologicalComplex.double f (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

variable [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]

/-- The scalar model is the existing sheafified change of rings applied to the constant
module sheaf. Thus it is B tensor over R_C with P_C, with its B-module structure.
Source: Stacks 03EK; blueprint Local models
(blueprint: lem-sfb-scalar-model-finite-flat-resolution). -/
def scalarModel (R : Type r) [CommRing R] {B : Sheaf J CommRingCat.{r}}
    (α : independentConstantRing J R ⟶ B) (P : ModuleCat.{r} R) : scalarModelModules B :=
  changeOfRingsOfUniverses.{v, u, r, r} α
    ((commutativeConstantModuleIndependent.{u, v, r} J R).obj P)

/-- Over a DVR the flat scalar model has a finite free length-one resolution and that
very two-term K-flat complex computes tensor with every module sheaf.

Source: blueprint main-20261015, ctf-equals-bc proof, Local models; Stacks 03EI,
06YQ, 06YS, 06YP and 06YU (blueprint: lem-sfb-scalar-model-finite-flat-resolution).

Proof:
1. Take a finite presentation of P. Its kernel is finitely generated and torsion-free
inside R^n, hence finite free by lem-sc-dvr-fg-torsionfree-free.
2. Constant presheaves preserve the resulting short exact scalar sequence sectionwise.
The exact sheafification of lem-weil-pbc-site-r-module-presheaf-sheafification-exact
preserves it and identifies finite constant powers with powers of R_C.
3. Flatness of B preserves the sequence under extension of scalars. The coordinate
maps b tensor (x_i) to (b*x_i), with inverse summing b_i tensor e_i, identify its free
terms with B^m and B^n, also at rank zero.
4. Its two-term augmentation has H^-1=0, H^0=M and other cohomology zero. Thus it is a
quasi-isomorphism. Finite free module sheaves are flat by the same coordinate tensor
maps and exactness of finite products, including zero powers.
5. The bounded-above flat complex is K-flat by lem-pc-bounded-above-flat-kflat-site.
Resolve N by lem-pc-kflat-resolution and use lem-weil-pbc-site-derived-tensor-descent.
The quasi-isomorphism invariance lem-pur-kflat-tensor-quasiiso-independent replaces
that resolution of N by N[0]. The signed interchange of the tensor factors identifies
the stated order of derived tensor. Coordinate tensor maps identify the two terms
with N^m and N^n and transport the differential of this same resolution. -/
theorem scalarModel_finite_flat_resolution_dvr
    (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (B : Sheaf J CommRingCat.{r}) (α : independentConstantRing J R ⟶ B)
    (P : ModuleCat.{r} R) [Module.FinitePresentation R P]
    (hB : IsFlatOnSite (R := independentConstantRing J R)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map α)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B))))
    [HasDerivedCategory.{w} (scalarModelModules B)] :
    ∃ (m n : ℕ)
      (f : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) m ⟶
        scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n)
      (g : scalarModelPower
          (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n ⟶
        scalarModel R α P) (h : f ≫ g = 0),
      (ShortComplex.mk f g h).ShortExact ∧
      ∃ ε : scalarModelTwoTerm f ⟶
          (CochainComplex.singleFunctor (scalarModelModules B) 0).obj (scalarModel R α P),
        QuasiIso ε ∧ CochainComplex.IsKFlatIndependentCoefficients (scalarModelTwoTerm f) ∧
        ∀ N : scalarModelModules B,
          ∃ (em : (siteSheafTensorRight N).obj
              (scalarModelPower (unit ((sheafCompose J
                (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) m) ≅ scalarModelPower N m)
            (en : (siteSheafTensorRight N).obj
              (scalarModelPower (unit ((sheafCompose J
                (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n) ≅ scalarModelPower N n),
            Nonempty ((siteDerivedTensorIndependentCoefficients J B).obj
              (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
                (scalarModelModules B) 0).obj (scalarModel R α P)),
               DerivedCategory.Q.obj ((CochainComplex.singleFunctor
                (scalarModelModules B) 0).obj N)) ≅
              DerivedCategory.Q.obj (scalarModelTwoTerm
                (em.inv ≫ (siteSheafTensorRight N).map f ≫ en.hom))) := sorry

/-- Over a field the scalar model is finite free and its derived tensor is a finite
power in degree zero, without any flatness hypothesis on B over the constant ring.

Source: blueprint main-20261015, ctf-equals-bc proof, Local models; Stacks 03EI,
06YQ, 06YS, 06YP and 06YU (blueprint: lem-sfb-scalar-model-finite-flat-resolution).

Proof:
1. A finite presentation gives a finite spanning list. Delete dependent vectors by
solving a nontrivial linear relation over the field. Induction gives a finite basis,
including the empty basis for P=0.
2. The resulting scalar isomorphism R^r to P remains an isomorphism after constant
sheafification and extension to B. Exact constant sheafification preserves finite
products by lem-weil-pbc-site-r-module-presheaf-sheafification-exact. Coordinate
balanced-tensor maps identify the result with B^r; no flatness of B is used.
3. Finite free B-module sheaves are flat; their degree-zero complex is K-flat by
lem-pc-bounded-above-flat-kflat-site. Resolve N using lem-pc-kflat-resolution.
Apply lem-weil-pbc-site-derived-tensor-descent and
lem-pur-kflat-tensor-quasiiso-independent to compute the tensor by B^r[0] tensor N[0].
The coordinate maps give N^r[0], and the signed symmetry gives the asserted order. -/
theorem scalarModel_finite_free_field
    (R : Type r) [Field R] (B : Sheaf J CommRingCat.{r})
    (α : independentConstantRing J R ⟶ B)
    (P : ModuleCat.{r} R) [Module.FinitePresentation R P]
    [HasDerivedCategory.{w} (scalarModelModules B)] :
    ∃ n : ℕ,
      Nonempty (scalarModel R α P ≅
        scalarModelPower (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj B)) n) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((CochainComplex.singleFunctor (scalarModelModules B) 0).obj (scalarModel R α P)) ∧
      ∀ N : scalarModelModules B,
        Nonempty ((siteDerivedTensorIndependentCoefficients J B).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj (scalarModel R α P)),
           DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj N)) ≅
          DerivedCategory.Q.obj ((CochainComplex.singleFunctor
            (scalarModelModules B) 0).obj (scalarModelPower N n))) := sorry

end SheafOfModules
