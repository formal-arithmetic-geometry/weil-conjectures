/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.SheafTensorStructure
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
/-! # Internal and sectionwise tensor products

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW;
(blueprint: lem-pe-internal-section-tensor-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace CategoryTheory.InternalAbelianSheafModule
/-- The site is essentially small in the coefficient universe.
Source: the size hypothesis of the node (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: shrink its object and arrow types into the coefficient universe using UnivLE;
the resulting small category is equivalent to the original category. -/
@[instance] theorem comparison_essentiallySmall
    {D : Type v} [Category.{w} D] [UnivLE.{max v w, u}] :
    EssentiallySmall.{u} D := by
  have : UnivLE.{v, u} := UnivLE.trans.{v, max v w, u}
  have : UnivLE.{w, u} := UnivLE.trans.{w, max v w, u}
  exact essentiallySmall_of_small_of_locallySmall D

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

/-- Left tensor on abelian sheaves preserves the colimits used in relative tensor.
Source: Stacks 03EK (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: use closedness in sk-def-sfb-sheaf-tensor; left tensor is a left adjoint. -/
@[instance] theorem comparison_sheafTensorLeft (M : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  let _ : HasWeakSheafify J AddCommGrpCat.{u} := HasSheafify.isRightAdjoint
  exact (sfbSheafTensor_properties (A := AddCommGrpCat.{u}) J).2.2 M |>.1

/-- Right tensor on abelian sheaves preserves the colimits used in relative tensor.
Source: Stacks 03EK (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: conjugate left tensor by the symmetry of det-def-sfb-sheaf-tensor-structure. -/
@[instance] theorem comparison_sheafTensorRight (M : Sheaf J AddCommGrpCat.{u}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

variable (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]

/-- Module objects have the coproducts used in direct-sum totalization.
Source: Stacks 03DA--03DB (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: section module sheaves have small colimits by
lem-weil-pbc-module-sheaves-colimits-forgetful. Transfer their universal property
through sectionModuleEquivalence: applying its inverse to a coproduct gives a
coproduct of the original internal modules by the equivalence's Hom bijections. -/
@[instance] theorem comparison_internalColimits :
    HasColimitsOfSize.{0, 0} (Mod (Sheaf J AddCommGrpCat.{u}) R) := by
  exact Adjunction.has_colimits_of_equivalence (sectionModuleEquivalence J R).functor

/-- The fixed sectionwise equivalence is additive on morphisms.
Source: Stacks 00YV (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: its map is the original map on underlying abelian sheaves; addition of module
maps is computed on those underlying maps (lem-sfb-modobj-abelian). -/
@[instance] theorem comparison_additive : (sectionModuleEquivalence J R).functor.Additive := by
  have : HasBinaryProducts (Mod (Sheaf J AddCommGrpCat.{u}) R) :=
    Adjunction.hasLimitsOfShape_of_equivalence (sectionModuleEquivalence J R).functor
  exact Functor.additive_of_preserves_binary_products _

/-- Every pair of internal complexes admits its direct-sum total tensor.
Source: Stacks 012Z (blueprint: lem-pe-internal-section-tensor-comparison).
Proof: comparison_internalColimits supplies every coproduct indexed by p+q=n,
which is the defining HasMapBifunctor condition. -/
@[instance] theorem comparison_internalTotalExists
    (K L : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ) :
    K.HasMapBifunctor L (curriedTensor _) := by
  intro n
  exact (comparison_internalColimits J R).has_colimits_of_shape _ |>.has_colimit _

/-- The pure tensor in the coequalizer relative tensor, formed using the lax tensor
comparison of the inclusion of sheaves into presheaves, then the coequalizer projection.
Source: Stacks 03EK (blueprint: lem-pe-internal-section-tensor-comparison). -/
noncomputable def comparison_internalTmul
    (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) : (M ⊗ N).X.obj.obj U :=
  ((Mod.tensorObjπ M N).hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) M.X N.X).app U)
      (x ⊗ₜ[ℤ] y))

/-- The pure tensor in the sectionwise sheaf tensor: apply the module-sheafification
unit to the balanced section tensor and the inverse canonical tensor comparison.
Source: Stacks 03EK and 0GMW (blueprint: lem-pe-internal-section-tensor-comparison). -/
noncomputable def comparison_sectionTmul
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U)
    ((((PresheafOfModules.sheafificationAdjunction (𝟙
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R)).obj)).unit.app (M.val ⊗ N.val)).app U)
      (x ⊗ₜ[(sectionRingSheaf J R).obj.obj U] y))

/-- The fixed internal-to-sectionwise equivalence is exact, symmetric monoidal with
its tensor comparison pinned on local pure tensors, and identifies the unbounded
sum-total tensors, acyclicity, flatness and K-flatness.

Source: Stacks Project, Modules on Sites, Tags 03EK, 0GMW and 03ER; Cohomology on
Sites, Definition 06YN (blueprint: lem-pe-internal-section-tensor-comparison).

Proof following the eight DAG steps:
1. def-weil-pbc-internal-abelian-sheaf-module-equivalence evaluates multiplication
and action on sections. It leaves the underlying abelian sheaves and maps unchanged;
det-def-sfb-sheaf-tensor-structure identifies local tensors with sheafified tensors.
2. sk-def-sfb-sheaf-tensor supplies additive tensor preserving colimits. Apply
lem-sfb-modobj-abelian and lem-sfb-modobj-forget-left-exact/right-exact. The target
has the same kernels and sheafified cokernels by def-weil-sheaf-of-modules-category
and lem-weil-pbc-module-sheaves-colimits-forgetful. Thus the equivalence is exact.
3. The coequalizer def-sfb-modobj-relative-tensor corepresents the compatible
sectionwise balanced bilinear maps. The tensor in def-pur-sheaf-tensor-product
corepresents the same maps by def-weil-pbc-sheafification and
def-weil-presheaf-modules-sheafification. Their universal maps are inverse and
fix every local pure tensor. This proves the normalized natural tensor comparison.
4. The regular module has the original section-ring action. The associators,
unitors and the symmetry of def-sfb-modobj-symmetric-tensor and
lem-pc-sheaf-modules-tensor-closed agree on pure tensors. The same universal
properties give the three coherence equations and the braiding equation below.
5. Transfer coproducts through the equivalence. In degree n sum the comparisons
for p+q=n; naturality commutes with d tensor 1 + (-1)^p 1 tensor d. This is the
sum-total tensor of def-pc-tensor-complex-sheaves, with the displayed summand formula.
6. Exactness identifies kernels, images and cokernels, hence cohomology as in
def-weil-abstract-derived-category. The equivalence reflects zero objects, so
it preserves and reflects acyclicity.
7. The tensor comparison conjugates the two right tensor functors through an
exact equivalence. Exactness of one is equivalent to exactness of the other,
which is precisely def-pc-flat-sheaf-modules.
8. Use step 5 on every acyclic tensor test in def-pc-kflat-complex and step 6
to preserve and reflect its acyclicity. For every target test complex, apply
the quasi-inverse termwise; the counit identifies its image with that test
complex. This proves both directions without restricting the tests.
-/
theorem internal_section_tensor_comparison :
    exactFunctor _ _ (sectionModuleEquivalence J R).functor ∧
    ∃ e : ∀ M N : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (sectionModuleEquivalence J R).functor.obj (M ⊗ N) ≅
        (sectionModuleEquivalence J R).functor.obj M ⊗
          (sectionModuleEquivalence J R).functor.obj N,
    ∃ e₀ : (sectionModuleEquivalence J R).functor.obj
        (𝟙_ (Mod (Sheaf J AddCommGrpCat.{u}) R)) ≅
      𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R))),
    (∀ (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
        (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      ((e M N).hom.val.app U) (comparison_internalTmul J R M N U x y) =
        comparison_sectionTmul J R
          ((sectionModuleEquivalence J R).functor.obj M)
          ((sectionModuleEquivalence J R).functor.obj N) U x y) ∧
    (∀ (U : Cᵒᵖ) (r : R.obj.obj U), (e₀.hom.val.app U) r = r) ∧
    (∀ (M M' N N' : Mod (Sheaf J AddCommGrpCat.{u}) R) (f : M ⟶ M') (g : N ⟶ N'),
      (sectionModuleEquivalence J R).functor.map (f ⊗ₘ g) ≫ (e M' N').hom =
        (e M N).hom ≫ ((sectionModuleEquivalence J R).functor.map f ⊗ₘ
          (sectionModuleEquivalence J R).functor.map g)) ∧
    (∀ M N P : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e (M ⊗ N) P).hom ≫
          (e M N).hom ▷ (sectionModuleEquivalence J R).functor.obj P ≫
          (α_ _ _ _).hom =
        (sectionModuleEquivalence J R).functor.map (α_ M N P).hom ≫
          (e M (N ⊗ P)).hom ≫
          (sectionModuleEquivalence J R).functor.obj M ◁ (e N P).hom) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e (𝟙_ _) M).hom ≫ e₀.hom ▷
          (sectionModuleEquivalence J R).functor.obj M ≫ (λ_ _).hom =
        (sectionModuleEquivalence J R).functor.map (λ_ M).hom) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e M (𝟙_ _)).hom ≫ (sectionModuleEquivalence J R).functor.obj M ◁
          e₀.hom ≫ (ρ_ _).hom =
        (sectionModuleEquivalence J R).functor.map (ρ_ M).hom) ∧
    (∀ M N : Mod (Sheaf J AddCommGrpCat.{u}) R,
      (e M N).hom ≫ (β_ _ _).hom =
        (sectionModuleEquivalence J R).functor.map (β_ M N).hom ≫ (e N M).hom) ∧
    (∀ K L : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      ∃ t : ((sectionModuleEquivalence J R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (CochainComplex.mapBifunctor K L (curriedTensor _)) ≅
        CochainComplex.mapBifunctor
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) (curriedTensor _),
      ∀ (p q n : ℤ) (h : p + q = n),
        (sectionModuleEquivalence J R).functor.map
            (CochainComplex.ιMapBifunctor K L (curriedTensor _) p q n h) ≫ t.hom.f n =
          (e (K.X p) (L.X q)).hom ≫ CochainComplex.ιMapBifunctor
            (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L) (curriedTensor _) p q n h) ∧
    (∀ K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      K.Acyclic ↔ (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic) ∧
    (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      exactFunctor _ _ (tensorRight M) ↔
        SheafOfModules.IsFlatOnSite ((sectionModuleEquivalence J R).functor.obj M)) ∧
    (∀ K : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
      (∀ A : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ,
        A.Acyclic → (CochainComplex.mapBifunctor A K (curriedTensor _)).Acyclic) ↔
      CochainComplex.IsKFlatIndependentCoefficients
        (((sectionModuleEquivalence J R).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) := by
  sorry

end CategoryTheory.InternalAbelianSheafModule
