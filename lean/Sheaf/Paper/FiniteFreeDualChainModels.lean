/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.ScalarPerfectDualRealization
public import Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Sites.LocalSite
/-! # Concrete scalar chain models in native internal modules

(blueprint: def-sfb-finite-free-dual-chain-models).

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ;
main-20261015, det-lem-int-tensor-product.proof.md, first paragraph
(blueprint: lem-sfb-finite-free-dual-chain-comparison).

Scalar extension is the existing ordinary constant-sheaf scalar extension, expressed
in internal modules through the section-action equivalence. This fixes its action,
its differential and its tensor, without imposing scalar flatness. The native derived
transpose below uses the actual closed adjunction, including its counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteFreeDualComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
  (A : Type (u + 1)) [CommRing A]
  (α : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of A) ⟶ ring Λ X)

/-- Ordinary relative scalar extension, in the internal module category. The inverse
section equivalence reconstructs the original action, not a chosen tensor structure.
The ring map is written on section-ring sheaves, the equivalent presentation of A_X → R_X.
Source: Stacks 03EK, 08JJ (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def realization : ModuleCat.{u + 1} A ⥤ Internal Λ X :=
  SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α ⋙
    (equivalence Λ X).inverse

/-- The existing scalar functor is additive and reconstruction is an additive equivalence.
Source: Stacks 03EK (blueprint: lem-sfb-finite-free-dual-chain-comparison).
Proof: ordinary scalar extension is additive on balanced generators; the section
 equivalence is additive since it fixes addition on every section and morphism. -/
@[instance] theorem realization_additive : (realization Λ X A α).Additive := by
  have : (SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α).Additive :=
    SheafOfModules.scalarPerfectFunctor_additive (Scheme.ProEt.topology X) A α
  have : (equivalence Λ X).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold realization
  infer_instance

/-- The native scalar chart with its termwise scalar differential.
Source: Stacks 08JJ (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def chart (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    CochainComplex (Internal Λ X) ℤ :=
  ((realization Λ X A α).mapHomologicalComplex (.up ℤ)).obj P

/-- The scalar dual is the recorded Hom complex into A[0]. Its coordinate identification
is ScalarPerfectDual.coordinates; dual_coordinates gives dφ = (-1)^(b+1) φ d_P.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def scalarDual (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  CategoryTheory.ScalarPerfectDual.dual A P

/-- Reconstruction's counit identifies the section chart with ordinary scalar extension.
Source: Stacks 03EK (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def sectionChartIso : realization Λ X A α ⋙ (equivalence Λ X).functor ≅
    SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α :=
  Functor.associator (SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α)
      (equivalence Λ X).inverse (equivalence Λ X).functor ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α)
      (equivalence Λ X).counitIso ≪≫
    Functor.rightUnitor (SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α)

/-- The balanced local generator r tensor v, with the actual reconstructed action.
Source: Stacks 03CY, 03EK (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def scalarSection (V : ModuleCat.{u + 1} A) (U : X.ProEtᵒᵖ)
    (r : (ring Λ X).obj.obj U) (v : V) :
    ((equivalence Λ X).functor.obj ((realization Λ X A α).obj V)).val.obj U :=
  ((sectionChartIso Λ X A α).inv.app V).val.app U
    (SheafOfModules.scalarExtensionSection α
      ((SheafOfModules.scalarPerfectConstantFunctor (Scheme.ProEt.topology X) A).obj V)
      U r (SheafOfModules.scalarPerfectConstantSection (Scheme.ProEt.topology X) A V U v))

/-- The ordinary scalar image in the reconstructed coefficient sheaf.
Source: Stacks 03CY (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def scalar (U : X.ProEtᵒᵖ) (a : A) : (ring Λ X).obj.obj U :=
  α.hom.app U ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a)


/-- The existing Grothendieck localization for the section-module category.
This explicit instance fixes the same small-Hom localization used by the comparison API.
Source: Stacks 079V (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
instance sectionDerivedCategory : HasDerivedCategory.{u + 1} (Modules Λ X) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (Modules Λ X)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unit of the actual native derived tensor structure.
Source: Stacks 08JJ (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def nativeUnit : DerivedCategory.{u + 1} (Internal Λ X) :=
  𝟙_ (DerivedCategory.{u + 1} (Internal Λ X))

/-- The native evaluation transpose F tensor RHom(T,1) → RHom(T,F). The two braidings
only convert the specified left-tensor adjunction to right-tensor evaluation.
Source: Stacks 08JJ, equation-eval
(blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def evaluationTranspose (T F : DerivedCategory.{u + 1} (Internal Λ X)) :
    ((CondensedRing.derivedTensor Λ X).obj F).obj
      (((CondensedRing.derivedHom Λ X).obj (op T)).obj (𝟙_ (DerivedCategory.{u + 1} (Internal Λ
        X)))) ⟶
    ((CondensedRing.derivedHom Λ X).obj (op T)).obj F :=
  (CondensedRing.derivedTensorHomAdjunction Λ T).homEquiv _ _
    ((β_ T (F ⊗ (((CondensedRing.derivedHom Λ X).obj (op T)).obj
        (𝟙_ (DerivedCategory.{u + 1} (Internal Λ X)))))).hom ≫
      (α_ F (((CondensedRing.derivedHom Λ X).obj (op T)).obj
        (𝟙_ (DerivedCategory.{u + 1} (Internal Λ X)))) T).hom ≫
      F ◁ ((β_ (((CondensedRing.derivedHom Λ X).obj (op T)).obj
          (𝟙_ (DerivedCategory.{u + 1} (Internal Λ X)))) T).hom ≫
        (CondensedRing.derivedTensorHomAdjunction Λ T).counit.app
          (𝟙_ (DerivedCategory.{u + 1} (Internal Λ X)))) ≫ (ρ_ F).hom)



/-- The natural derived Hom comparison, conjugated by the complex localization
comparison. Its argument is required to preserve the native evaluation counit below.
Source: Stacks 08JA (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def sectionDerivedHomMap
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    (T F : CochainComplex (Internal Λ X) ℤ) :
    (forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj
      (op (DerivedCategory.Q.{u + 1}.obj T))).obj (DerivedCategory.Q.{u + 1}.obj F)) ⟶
      (hom Λ X).obj (op (DerivedCategory.Q.{u + 1}.obj ((complexForward Λ X).obj T)),
        DerivedCategory.Q.{u + 1}.obj ((complexForward Λ X).obj F)) :=
  θ.hom.app (op (DerivedCategory.Q.{u + 1}.obj T), DerivedCategory.Q.{u + 1}.obj F) ≫
    (hom Λ X).map ((localizationIso Λ X).inv.app T |>.op,
      (localizationIso Λ X).hom.app F)


/-- Tensoring in the target-complex variable with the native scalar dual.
Source: Stacks 08JJ (blueprint: lem-sfb-finite-free-dual-chain-comparison). -/
def tensorTargetMap (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    {F G : CochainComplex (Internal Λ X) ℤ} (f : F ⟶ G) :
    internalTotalTensor Λ X F (chart Λ X A α (scalarDual A P)) ⟶
      internalTotalTensor Λ X G (chart Λ X A α (scalarDual A P)) :=
  (@tensorRight _ _ (internalComplexMonoidal Λ X)
    (chart Λ X A α (scalarDual A P))).map f


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.ProEtale.FiniteFreeDualComparison
