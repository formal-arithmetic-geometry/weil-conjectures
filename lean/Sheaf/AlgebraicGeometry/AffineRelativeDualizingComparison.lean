/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import Sheaf.AlgebraicGeometry.DerivedGlobalScalar
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

import Sheaf.AlgebraicGeometry.PseudoCoherentQCoh
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion

/-! # Affine comparison of coherent relative dualizing pairs

Source: Stacks Project, Duality for Schemes, Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison).

## Main definitions and statement

* `relativeDualizingAffineTilde`: the recorded affine equivalence followed by inclusion.
* `degreeZeroDerivedMultiplication`: multiplication after monoidal localization.
* `relativeDualizingDerivedExtension`: K-flat extension of scalars.
* `relativeDualizingModuleDiagonal`, `relativeDualizingModuleMultiplication`, and
  `relativeDualizingModuleClassMap`: the affine diagonal algebra and its class map.
* `relativeDualizingProductChart`: the affine product chart.
* `relativeDualizingExtensionCounit` and `IsRelativeDualizingExtensionTensorComparison`:
  the counit normalization of the scalar-extension tensor comparison.
* `relativeDualizingHomLocalization` and `relativeDualizingLocalizedClassMap`:
  evaluation and the multiplication transpose recomputed on a smaller affine open.
* `relativeDualizingModuleFirstPullback` and `relativeDualizingModuleHom`:
  named components of the affine comparison.
* `affine_relativeDualizing_comparison`: the complete affine comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w v c

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The affine equivalence already recorded by the affine-derived-equivalence node,
followed by the inclusion of quasi-coherent derived objects.
Source: Stacks Project, Tag 06Z0, used in Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingAffineTilde (A : Type u) [CommRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedCategory (Spec (.of A)) :=
  (Classical.choose (exists_affineQCohDerivedEquivalence A)).functor ⋙
    (schemeDerivedQCohProperty (Spec (.of A))).ι

end AlgebraicGeometry

namespace CategoryTheory

/-- The multiplication on a degree-zero algebra in the derived category, obtained from
its ordinary multiplication and the localization tensor comparison.
Source: Stacks Project, Tag 0E2U, multiplication by the diagonal class
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def degreeZeroDerivedMultiplication
    {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [MonoidalCategory (DerivedCategory C)]
    [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (D : C) (m : D ⊗ D ⟶ D) :
    DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj D) ⊗
      DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj D) ⟶
        DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj D) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
    DerivedCategory.Q.map
      ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C) D
        ((HomologicalComplex.single C (.up ℤ) 0).obj D)).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorLeft D) (.up ℤ) 0).hom.app D ≫
      (HomologicalComplex.single C (.up ℤ) 0).map m)

end CategoryTheory

namespace AlgebraicGeometry

/-- Derived extension of scalars, with its K-flat construction from the shared module API.
Source: Stacks Project, Tags 06Y0 and 08DW, used in Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingDerivedExtension {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} B)] :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  haveI := ModuleCat.extendScalars_preservesKFlatQuasiIso φ
  exact (ModuleCat.extendScalars φ).leftDerivedFunctor

/-- The diagonal B-module A in degree zero, for B = A tensor_R A and the multiplication map.
Source: Stacks Project, Tag 0E2U, affine diagonal
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingModuleDiagonal (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))] :
    DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
    ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R (S := A)).toRingHom).obj
      (ModuleCat.of A A)))

/-- Derived multiplication of the diagonal module, using ordinary multiplication in A.
Source: Stacks Project, Tag 0E2U, affine diagonal algebra
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingModuleMultiplication (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))] :
    relativeDualizingModuleDiagonal R A ⊗ relativeDualizingModuleDiagonal R A ⟶
      relativeDualizingModuleDiagonal R A := by
  letI : Algebra (A ⊗[R] A) A := (Algebra.TensorProduct.lmul' R (S := A)).toRingHom.toAlgebra
  exact degreeZeroDerivedMultiplication (ModuleCat.of (A ⊗[R] A) A)
    (ModuleCat.ofHom (LinearMap.mul' (A ⊗[R] A) A))

/-- Multiplication by the algebraic diagonal class, transposed by the derived closed tensor.
Source: Stacks Project, Tag 0E2U, affine dualizing class
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingModuleClassMap (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (M₁ : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)))
    (ξ : relativeDualizingModuleDiagonal R A ⟶ M₁) :
    relativeDualizingModuleDiagonal R A ⟶
      (ihom (relativeDualizingModuleDiagonal R A)).obj M₁ :=
  MonoidalClosed.curry (relativeDualizingModuleMultiplication R A ≫ ξ)

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- The product of an affine chart with itself, as an open in X ×_S X.
Source: Stacks 0E2U, affine fibre product
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingProductChart {X S : Scheme.{u}} (f : X ⟶ S)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ jR) :
    Spec (.of (A ⊗[R] A)) ⟶ pullback f f :=
  (pullbackSpecIso R A A).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) f f jA jA jR h.symm h.symm

/-- The counit of the K-flat scalar-extension construction used in this comparison.
Source: Stacks Project, Tags 06Y0 and 08DW, used in Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingExtensionCounit {B C : Type u}
    [CommRing B] [CommRing C] (φ : B →+* C)
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)] :
    DerivedCategory.Qh ⋙ relativeDualizingDerivedExtension φ ⟶
      (ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  haveI := ModuleCat.extendScalars_preservesKFlatQuasiIso φ
  exact (ModuleCat.extendScalars φ).leftDerivedFunctorCounit

/-- The tensor comparison for affine restriction is pinned by its K-flat counits
and the ordinary scalar-extension tensor comparison, rather than an arbitrary family
of isomorphisms. The equation is imposed on all homotopy complexes, hence in particular
on every pair of K-flat representatives, where its vertical maps are invertible.
Source: Stacks Project, Tags 08DW and 08DX, used in Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
def IsRelativeDualizingExtensionTensorComparison {B C : Type u}
    [CommRing B] [CommRing C] (φ : B →+* C)
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)]
    (τ : ∀ P Q : DerivedCategory (ModuleCat.{u} B),
      (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
        (relativeDualizingDerivedExtension φ).obj P ⊗
          (relativeDualizingDerivedExtension φ).obj Q) : Prop :=
  (∀ (P P' Q Q' : DerivedCategory (ModuleCat.{u} B)) (p : P ⟶ P') (q : Q ⟶ Q'),
    (relativeDualizingDerivedExtension φ).map (p ⊗ₘ q) ≫ (τ P' Q').hom =
      (τ P Q).hom ≫
        ((relativeDualizingDerivedExtension φ).map p ⊗ₘ
          (relativeDualizingDerivedExtension φ).map q)) ∧
  ∀ P Q : HomotopyCategory (ModuleCat.{u} B) (.up ℤ),
    (τ (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q)).hom ≫
        ((relativeDualizingExtensionCounit φ).app P ⊗ₘ
          (relativeDualizingExtensionCounit φ).app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P)
          (((ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj Q) =
      (relativeDualizingDerivedExtension φ).map (Functor.LaxMonoidal.μ DerivedCategory.Qh P Q) ≫
        (relativeDualizingExtensionCounit φ).app (P ⊗ Q) ≫
        DerivedCategory.Qh.map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
            (ModuleCat.extendScalars φ)).app P).app Q)

/-- The canonical Hom localization map: extend evaluation, then transpose using the
normalized scalar-extension tensor comparison. Its target is the Hom computed over C.
Source: Stacks Project, Tags 0A6H and 08DL, used in Tag 0E2U
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingHomLocalization {B C : Type u}
    [CommRing B] [CommRing C] (φ : B →+* C)
    [HasDerivedCategory.{u} (ModuleCat.{u} B)]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)]
    (τ : ∀ P Q : DerivedCategory (ModuleCat.{u} B),
      (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
        (relativeDualizingDerivedExtension φ).obj P ⊗
          (relativeDualizingDerivedExtension φ).obj Q)
    (D E : DerivedCategory (ModuleCat.{u} B)) :
    (relativeDualizingDerivedExtension φ).obj ((ihom D).obj E) ⟶
      (ihom ((relativeDualizingDerivedExtension φ).obj D)).obj
        ((relativeDualizingDerivedExtension φ).obj E) :=
  MonoidalClosed.curry
    ((τ D ((ihom D).obj E)).inv ≫
      (relativeDualizingDerivedExtension φ).map ((ihom.ev D).app E))

/-- The smaller affine open's class map, recomputed from its localized diagonal
multiplication and localized class. It is not defined by transporting the old transpose.
Source: Stacks Project, Tag 0E2U, restriction of multiplication and tensor-Hom evaluation
(blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingLocalizedClassMap (R A C : Type u)
    [CommRing R] [CommRing A] [CommRing C] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    [HasDerivedCategory.{u} (ModuleCat.{u} C)] (φ : (A ⊗[R] A) →+* C)
    (τ : ∀ P Q : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)),
      (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
        (relativeDualizingDerivedExtension φ).obj P ⊗
          (relativeDualizingDerivedExtension φ).obj Q)
    (E : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)))
    (ξ : relativeDualizingModuleDiagonal R A ⟶ E) :
    (relativeDualizingDerivedExtension φ).obj (relativeDualizingModuleDiagonal R A) ⟶
      (ihom ((relativeDualizingDerivedExtension φ).obj
        (relativeDualizingModuleDiagonal R A))).obj
        ((relativeDualizingDerivedExtension φ).obj E) :=
  MonoidalClosed.curry
    ((τ (relativeDualizingModuleDiagonal R A) (relativeDualizingModuleDiagonal R A)).inv ≫
      (relativeDualizingDerivedExtension φ).map (relativeDualizingModuleMultiplication R A) ≫
      (relativeDualizingDerivedExtension φ).map ξ)

/-- The first pullback module on the affine product chart.
Source: Stacks Project, Tag 0E2U (blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingModuleFirstPullback (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (M : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  (relativeDualizingDerivedExtension
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj M

/-- The Hom on the original affine product chart.
Source: Stacks Project, Tag 0E2U (blueprint: lem-trf-affine-relative-dualizing-comparison). -/
noncomputable def relativeDualizingModuleHom (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (M : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  (ihom (relativeDualizingModuleDiagonal R A)).obj (relativeDualizingModuleFirstPullback R A M)

/-- Affine translation of a supplied coherent relative dualizing pair.
The three comparisons identify the diagonal, the first pullback, and their derived Hom.
Both squares concern the specified class, not an unspecified algebraic isomorphism.
For every smaller affine open Spec C of Spec B, scalar extension constructs the
restricted diagonal and first pullback. The Hom is recomputed over C, and its comparison
is the transpose of extended evaluation. The tensor comparison is normalized by the
K-flat counits and the ordinary extension-of-scalars comparison. The localized class is
independently the transpose of localized multiplication followed by the localized class;
the final equations identify this construction with restriction of the original class.
All the comparisons are maps of module sheaves, so they commute with the A-action
through a ↦ a tensor 1 on B, including its action by precomposition on Hom.

Source: Stacks Project, Tag 0E2U, lemma-relative-dualizing-complex-algebra
(blueprint: lem-trf-affine-relative-dualizing-comparison).
Proof:
1. The affine flatness and finite-presentation criteria give the asserted properties
of R → A. Local Noetherianity makes R Noetherian and finite type makes A and B
Noetherian.
2. The product chart is Spec B. On D(b) its diagonal has sections A localized at
μ(b), giving the associated sheaf of the multiplication B-module A.
3. Restriction of pseudo-coherence, quasi-coherence of pseudo-coherent complexes,
and the affine equivalence give M and its bounded-above finite-free model.
4. The relative affine Tor criterion (Stacks 0DHY), using a finite affine cover,
gives a single interval for every R-module. Testing R itself bounds M below.
5. Affine pullback is K-flat extension of scalars. Flatness of B over A preserves
the lower bound of M. Since A is finite over Noetherian B, its degree-zero complex
has a bounded-above finite-free B-resolution.
6. Open restriction of derived Hom and the finite-free/bounded-below Hom comparison
give the third isomorphism. Only finitely many factors occur in each Hom degree.
7. Full faithfulness of the affine equivalence defines the inverse image of ξ.
The Hom comparison respects evaluation on the finite-free resolution. Thus both
class squares commute and the algebraic transpose is an isomorphism.
8. On an affine open Spec C of Spec B, scalar extension is flat and computes
restriction of both the diagonal A[0] and M₁. Derive the ordinary tensor comparison
using K-flat resolutions; its counit square gives the displayed normalization.
Transpose extended evaluation to obtain the canonical map to the Hom recomputed
over C. A bounded-above finite-free resolution of A and a bounded-below model of M₁
compute this Hom degreewise by finite products; flat extension therefore commutes
with this Hom, making the canonical map invertible. Multiplication and evaluation
commute with the same fraction restriction maps. The tensor-Hom adjunction now
identifies extension of the original transpose with the transpose of the localized
multiplication and class. Composing the tilde restriction comparison gives the
last sheaf square, whose target is this recomputed Hom. Scalars act through their
images in C in all constructions. For a smaller pair of affine charts U', V',
C = A' tensor_{R'} A' and C tensor_B A is canonically A'; tensor associativity
identifies C tensor_B M₁ with the first pullback of A' tensor_A M. Thus this is
the comparison constructed on those smaller charts as well. Empty affine opens
give zero complexes throughout; the identity case uses the tensor unitors. -/
theorem affine_relativeDualizing_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hKξ : IsCoherentRelativeDualizingPair f K ξ)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (jA : Spec (.of A) ⟶ X) (jR : Spec (.of R) ⟶ S)
    [IsOpenImmersion jA] [IsOpenImmersion jR]
    (h : jA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ jR) :
    (algebraMap R A).Flat ∧ Algebra.FinitePresentation R A ∧
    IsNoetherianRing R ∧ IsNoetherianRing A ∧
    ∃ M : DerivedCategory (ModuleCat.{u} A),
      DerivedCategory.IsPseudoCoherent M ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ (N : ModuleCat.{u} R) (i : ℤ),
        i < a ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj M) ⊗
              DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj N)))) ∧
      Nonempty ((derivedPullback jA).obj K ≅ (relativeDualizingAffineTilde A).obj M) ∧
      ∃ (eD : (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj
        (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)) ≅ (relativeDualizingAffineTilde
        (A ⊗[R] A)).obj (relativeDualizingModuleDiagonal R A))
        (eM : (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj ((derivedPullback
          (pullback.fst f f)).obj K) ≅ (relativeDualizingAffineTilde (A ⊗[R] A)).obj
          (relativeDualizingModuleFirstPullback R A M))
        (eH : (derivedPullback (relativeDualizingProductChart f R A jA jR h)).obj
          ((derivedInternalHom (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
          (pullback f f).sheaf).obj
            (op (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)),
              (derivedPullback (pullback.fst f f)).obj K)) ≅ (relativeDualizingAffineTilde (A ⊗[R]
                A)).obj (relativeDualizingModuleHom R A M))
        (ξU : (relativeDualizingModuleDiagonal R A) ⟶ (relativeDualizingModuleFirstPullback R A M)),
        eD.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map ξU = (derivedPullback
          (relativeDualizingProductChart f R A jA jR h)).map ξ ≫ eM.hom ∧
        eD.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map (relativeDualizingModuleClassMap R A
          (relativeDualizingModuleFirstPullback R A M) ξU) =
          (derivedPullback (relativeDualizingProductChart f R A jA jR h)).map
            (relativeDualizingClassMap f K ξ) ≫ eH.hom ∧
        IsIso (relativeDualizingModuleClassMap R A (relativeDualizingModuleFirstPullback R A M) ξU)
          ∧
        (∀ (a : A)
          (s : RingCat.sectionsSubring ((Spec (.of (A ⊗[R] A))).sheaf.obj ⋙ forget₂ CommRingCat
            RingCat)),
          s.val (op ⊤) = (Scheme.ΓSpecIso (.of (A ⊗[R] A))).inv.hom
            ((Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] A)) a) →
          schemeDerivedScalar (Spec (.of (A ⊗[R] A))) s (𝟙 _) ≫ eD.hom =
            eD.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map
              (((Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] A)) a) • 𝟙
              (relativeDualizingModuleDiagonal R A)) ∧
          schemeDerivedScalar (Spec (.of (A ⊗[R] A))) s (𝟙 _) ≫ eM.hom =
            eM.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map
              (((Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] A)) a) • 𝟙
              (relativeDualizingModuleFirstPullback R A M)) ∧
          schemeDerivedScalar (Spec (.of (A ⊗[R] A))) s (𝟙 _) ≫ eH.hom =
            eH.hom ≫ (relativeDualizingAffineTilde (A ⊗[R] A)).map
              (((Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] A)) a) • 𝟙
              (relativeDualizingModuleHom R A M))) ∧
        ∀ (C : Type u) [CommRing C] [HasDerivedCategory.{u} (ModuleCat.{u} C)]
          (φ : (A ⊗[R] A) →+* C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))],
          ∃ τ : ∀ P Q : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)),
              (relativeDualizingDerivedExtension φ).obj (P ⊗ Q) ≅
                (relativeDualizingDerivedExtension φ).obj P ⊗
                  (relativeDualizingDerivedExtension φ).obj Q,
            IsRelativeDualizingExtensionTensorComparison φ τ ∧
          ∃ ρ : (relativeDualizingAffineTilde (A ⊗[R] A)) ⋙ (derivedPullback (Spec.map
            (CommRingCat.ofHom φ))) ≅ (relativeDualizingDerivedExtension φ ⋙
            relativeDualizingAffineTilde C),
            IsIso (relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
              (relativeDualizingModuleFirstPullback R A M)) ∧
            (relativeDualizingDerivedExtension φ).map
                (relativeDualizingModuleClassMap R A (relativeDualizingModuleFirstPullback R A M)
                  ξU) ≫
                relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
                  (relativeDualizingModuleFirstPullback R A M) =
              relativeDualizingLocalizedClassMap R A C φ τ (relativeDualizingModuleFirstPullback R A
                M) ξU ∧
            (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map eD.hom ≫ ρ.hom.app
              (relativeDualizingModuleDiagonal R A) ≫ (relativeDualizingDerivedExtension φ ⋙
              relativeDualizingAffineTilde C).map ξU =
              (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map ((derivedPullback
                (relativeDualizingProductChart f R A jA jR h)).map ξ) ≫ (derivedPullback (Spec.map
                (CommRingCat.ofHom φ))).map eM.hom ≫ ρ.hom.app (relativeDualizingModuleFirstPullback
                R A M) ∧
            (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map eD.hom ≫ ρ.hom.app
              (relativeDualizingModuleDiagonal R A) ≫
                (relativeDualizingAffineTilde C).map
                  (relativeDualizingLocalizedClassMap R A C φ τ
                    (relativeDualizingModuleFirstPullback R A M) ξU) =
              (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map ((derivedPullback
                (relativeDualizingProductChart f R A jA jR h)).map (relativeDualizingClassMap f K
                ξ)) ≫
                (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map eH.hom ≫ ρ.hom.app
                  (relativeDualizingModuleHom R A M) ≫
                  (relativeDualizingAffineTilde C).map
                    (relativeDualizingHomLocalization φ τ (relativeDualizingModuleDiagonal R A)
                      (relativeDualizingModuleFirstPullback R A M)) := by
  sorry

end AlgebraicGeometry
