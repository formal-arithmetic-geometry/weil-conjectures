/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# Prime-power cohomological dimension

Source: blueprint `sk-def-cd`, order 1506; Stacks Project, Tag 0F10
(blueprint: sk-def-cd).

The common annihilator diagram gives the canonical filtered-colimit torsion condition
on both sites. Its local sectionwise form is also stated for the pro-étale site.
The comparison and finiteness statements are the corresponding blueprint clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- A sheaf is locally `ℓ`-power torsion: every section is locally killed by a power of `ℓ`.
This is equivalent to the canonical map from the filtered colimit of the kernels of
`ℓ ^ r` to the sheaf being an isomorphism, with the inclusions as transition maps.
Source: blueprint `sk-def-cd`, opening local torsion convention
(blueprint: sk-def-cd). -/
def IsEllPowerTorsionLocal {X : Scheme.{u}} (ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ ⦃U : X.ProEtᵒᵖ⦄ (s : F.obj.obj U),
    ∃ S ∈ Scheme.ProEt.topology X U.unop,
      ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U.unop), S f →
        ∃ r : ℕ, (ℓ ^ r) • (F.obj.map f.op).hom s = 0

/-- The `r`th annihilator subsheaf `F[ℓ ^ r]`, defined as the kernel of scalar
multiplication by `ℓ ^ r`.
Source: blueprint `sk-def-cd`, opening local torsion convention (blueprint: sk-def-cd). -/
noncomputable def ellPowerKernel {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} (r : ℕ) : A :=
  kernel ((ℓ ^ r : ℕ) • 𝟙 F)

/-- The scalar-power annihilation identity needed by the kernel lift.
Source: blueprint `sk-def-cd`, opening kernel transition convention (blueprint: sk-def-cd).
Proof: write s = r + (s - r). Multiplication by `ℓ ^ s` factors as multiplication
by `ℓ ^ r` followed by multiplication by `ℓ ^ (s - r)`; the kernel inclusion
annihilates the first factor, so their composite is zero. -/
theorem ellPowerKernelMap_condition {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (h : r ≤ s) :
    kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F) ≫ ((ℓ ^ s : ℕ) • 𝟙 F) = 0 := by
  sorry

/-- The inclusion `F[ℓ ^ r] ⟶ F[ℓ ^ s]` for `r ≤ s`. Its underlying map is the
canonical kernel lift; the annihilation identity is the scalar-power identity.
Source: blueprint `sk-def-cd`, opening local torsion convention
(blueprint: sk-def-cd). -/
noncomputable def ellPowerKernelMap {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (h : r ≤ s) :
    ellPowerKernel ℓ (F := F) r ⟶ ellPowerKernel ℓ (F := F) s :=
  kernel.lift ((ℓ ^ s : ℕ) • 𝟙 F) (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))
    (ellPowerKernelMap_condition ℓ h)

/-- Identity law for the annihilator transition maps.
Source: blueprint `sk-def-cd`, opening filtered kernel diagram (blueprint: sk-def-cd).
Proof: uniqueness of kernel lifts for the identity transition. -/
theorem ellPowerKernelFunctor_map_id {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} (r : ℕ) :
    ellPowerKernelMap ℓ (F := F) (le_refl r) = 𝟙 _ := by
  sorry

/-- Composition law for the annihilator transition maps.
Source: blueprint `sk-def-cd`, opening filtered kernel diagram (blueprint: sk-def-cd).
Proof: uniqueness of kernel lifts and transitivity of `≤`. -/
theorem ellPowerKernelFunctor_map_comp {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s t : ℕ}
    (f : r ⟶ s) (g : s ⟶ t) :
    ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom (f ≫ g)) =
      ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f) ≫
        ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom g) := by
  sorry

/-- The filtered diagram of annihilator subsheaves with its canonical inclusion maps.
Source: blueprint `sk-def-cd`, opening local torsion convention
(blueprint: sk-def-cd). -/
noncomputable def ellPowerKernelFunctor {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} : ℕ ⥤ A where
  obj r := ellPowerKernel ℓ (F := F) r
  map f := ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f)
  map_id := fun r ↦ ellPowerKernelFunctor_map_id ℓ r
  map_comp := fun f g ↦ ellPowerKernelFunctor_map_comp ℓ f g

/-- Naturality of the annihilator inclusions into `F`.
Source: blueprint `sk-def-cd`, opening filtered kernel cocone (blueprint: sk-def-cd).
Proof: the defining equation of the kernel lift. -/
theorem ellPowerKernelCocone_naturality {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (f : r ⟶ s) :
    ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f) ≫
        kernel.ι ((ℓ ^ s : ℕ) • 𝟙 F) = kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F) := by
  sorry

/-- The cocone of the annihilator inclusions into `F`.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
noncomputable def ellPowerKernelCocone {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} :
    Cocone (ellPowerKernelFunctor ℓ (F := F)) where
  pt := F
  ι := { app := fun r ↦ by
           simpa [ellPowerKernelFunctor, ellPowerKernel] using
             (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))
         naturality := by
           intro r s f
           simpa [ellPowerKernelFunctor] using ellPowerKernelCocone_naturality ℓ (F := F) f }

/-- The canonical map from the filtered colimit of the annihilator subsheaves to `F`.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
noncomputable def ellPowerKernelColimitMap {A : Type v} [Category.{w} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) {F : A} :
    colimit (ellPowerKernelFunctor ℓ (F := F)) ⟶ F :=
  colimit.desc _ (ellPowerKernelCocone ℓ (F := F))

/-- Prime-power torsion in the canonical local-colimit convention.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
def IsEllPowerTorsion {A : Type v} [Category.{w} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (F : A) : Prop :=
  IsIso (ellPowerKernelColimitMap ℓ (F := F))

/-- The canonical colimit condition is equivalent to the local annihilator formulation.
Proof: kernels are computed sectionwise, so sections represented in the filtered
colimit are precisely sections locally annihilated by a power of `ℓ`. Sheafification
makes local representability surjectivity; the transition maps are monomorphisms,
so the canonical map is also a monomorphism. This proves both implications.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
theorem isEllPowerTorsion_iff_local {X : Scheme.{u}} (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsionLocal ℓ hℓ F := by
  sorry

/-- The classicality predicate on an abelian pro-étale sheaf, obtained from the underlying
set-valued sheaf and the canonical affine-presentation continuity maps
(blueprint: `sk-def-pe-classical-definition`, `det-pe-classical-definition-continuity-map`).
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
def IsClassicalAbelian {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) : Prop :=
  ProEtale.IsClassical
    ((sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).obj F)

/-- The nonvanishing predicate for pro-étale cohomology in degree `q`.
Source: blueprint `sk-def-cd`, first displayed supremum and derived-notation paragraph
(blueprint: sk-def-cd). -/
def IsNonzeroProEtaleCohomology {X : Scheme.{u}} (F :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) : Prop :=
  ¬ IsZero
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- The nonvanishing predicate for the `q`th higher direct image on the small pro-étale sites.
Source: blueprint `sk-def-cd`, second displayed supremum and derived-notation paragraph
(blueprint: sk-def-cd). -/
def IsNonzeroProEtaleHigherDirectImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) : Prop :=
  ¬ IsZero
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- The `ℓ`-cohomological dimension of a scheme, as a supremum in `WithTop ℕ`; the
supremum of the empty set is `0`. For a field `K`, `cd_ℓ(K)` denotes this expression
at `Spec (.of K)`.
Source: blueprint `sk-def-cd`, first displayed supremum and field notation
(blueprint: sk-def-cd). -/
noncomputable def cohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
      IsClassicalAbelian F ∧ IsEllPowerTorsion ℓ hℓ F ∧ IsNonzeroProEtaleCohomology F n}

/-- The relative `ℓ`-cohomological dimension of a morphism of schemes, as a supremum in
`WithTop ℕ`; the supremum of the empty set is `0`.
Source: blueprint `sk-def-cd`, second displayed supremum (blueprint: sk-def-cd). -/
noncomputable def relativeCohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
      IsClassicalAbelian F ∧ IsEllPowerTorsion ℓ hℓ F ∧
        IsNonzeroProEtaleHigherDirectImage g F n}

/-- The corresponding étale cohomological dimension, used in the comparison clause.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
noncomputable def etaleCohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsEllPowerTorsion ℓ hℓ F ∧
        ¬ IsZero ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X (n : ℤ)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))}

/-- Pro-étale and étale cohomology give the same `ℓ`-cohomological dimension for a qcqs
scheme.
Proof: `det-pe-classical-sheaves-modules` gives the exact equivalence of étale sheaves
with classical pro-étale sheaves. Exactness preserves annihilator kernels, and the
left adjoint preserves the filtered colimit and its canonical map. Thus it preserves
and reflects local prime-power torsion. `sk-prop-sf-comparison` identifies cohomology
in every nonnegative degree. The sets of degrees in the two suprema agree.
The comparison is via the exact classical-sheaf comparison functor
(blueprint: `sk-def-cd`; Stacks, Tags 099V and 099W).
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
theorem cohomologicalDimension_eq_etaleCohomologicalDimension
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] :
    cohomologicalDimension ℓ hℓ X = etaleCohomologicalDimension ℓ hℓ X := by
  sorry

/-- The relative pro-étale/étale comparison for a qcqs morphism.
Proof: the exact classical-sheaf equivalence preserves and reflects the annihilator
colimit condition. `sk-thm-pe-direct-image-comparison` identifies each higher direct
image with the exact fully faithful comparison of the étale higher direct image.
Full faithfulness reflects zero objects, so both sets of nonvanishing degrees agree.
Source: blueprint `sk-def-cd`, displayed definitions and local torsion convention
(blueprint: sk-def-cd). -/
theorem relativeCohomologicalDimension_eq_etale
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    relativeCohomologicalDimension ℓ hℓ g =
      sSup {q : WithTop ℕ |
        ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          IsEllPowerTorsion ℓ hℓ F ∧
            ¬ IsZero
              ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
                ((AlgebraicGeometry.Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))} := by
  sorry

/-- Over a field of finite `ℓ`-cohomological dimension, a finite-type morphism between
finite-type schemes over that field has finite relative dimension.
Source: blueprint `sk-def-cd`, final sentence; Stacks Tag 0F10 (blueprint: sk-def-cd).
Proof: finite-type schemes over a field are Noetherian, hence qcqs; every morphism from
such a source is qcqs, since inverse images of affine opens, also for its diagonal,
are quasi-compact opens of a Noetherian scheme. A locally prime-power torsion sheaf
is torsion by the local-section criterion of `lem-weil-pbc-torsion-sheaf-characterizations`.
Apply `lem-kun-0f10` to the underlying étale torsion sheaves and
use the relative comparison (`sk-thm-pe-direct-image-comparison`) to transport its
uniform vanishing bound to classical prime-power torsion sheaves. -/
theorem relativeCohomologicalDimension_lt_top_of_finiteType
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {K : Type u} [Field K]
    (hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤)
    {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of K))]
    [LocallyOfFiniteType g] [QuasiCompact g] :
    @relativeCohomologicalDimension ℓ hℓ X Y g inferInstance
      (@QuasiSeparated.of_quasiSeparatedSpace X Y g
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))))) < ⊤ := by
  sorry

/-- Over a field of finite `ℓ`-cohomological dimension, every finite-type scheme has
finite absolute dimension.
Source: blueprint `sk-def-cd`, final sentence; Stacks Tag 0F10 (blueprint: sk-def-cd).
Proof: use `lem-kun-0f10` for a relative bound e on the structure morphism. The field
hypothesis and the comparison give an absolute bound c for prime-power torsion sheaves
on the field. By `lem-sbc-qcqs-higher-images-prime-torsion`, all higher direct images
are again locally prime-power torsion, using exact conservative geometric stalks and
filtered colimits to identify this with the kernel-colimit convention. Apply
`lem-sc-leray-vanishing-bound` to obtain the bound c + e, then use the absolute
comparison. Finite type over a field gives a Noetherian source, so the scheme and
its structure morphism are qcqs, as in the relative finiteness proof.
Empty schemes satisfy the same bound. -/
theorem cohomologicalDimension_lt_top_of_finiteType
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {K : Type u} [Field K]
    (hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤)
    {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    @cohomologicalDimension ℓ hℓ X
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K)))
      (@IsLocallyNoetherian.quasiSeparatedSpace X
        (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K)))) < ⊤ := by
  sorry

end ProEtale

end AlgebraicGeometry
