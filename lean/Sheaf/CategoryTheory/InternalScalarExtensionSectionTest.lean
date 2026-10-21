/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Internal scalar extension and the sectionwise flatness test

Source: Stacks Project, Modules on Sites, Tags 03CY, 03CZ, 03DB, 03EK, 03EO,
03ER(3), and Categories, Tags 0034, 0038, 0B65.
(blueprint: lem-sfb-internal-scalar-extension-section-test).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [UnivLE.{max uC vC, w}] [HasSheafify J AddCommGrpCat.{w}]
  [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
  [MonoidalClosed (Sheaf J AddCommGrpCat.{w})]

/-- Instantiate Mathlib's small-model construction using the stated universe bound.
Source: the small-site hypothesis, Mathlib `essentiallySmall_of_small_of_locallySmall`
(blueprint: lem-sfb-internal-scalar-extension-section-test). -/
noncomputable instance scalarExtensionSectionEssentiallySmall : EssentiallySmall.{w} C := by
  have : UnivLE.{uC, w} := UnivLE.trans.{uC, max uC vC, w}
  have : UnivLE.{vC, w} := UnivLE.trans.{vC, max uC vC, w}
  exact essentiallySmall_of_small_of_locallySmall C

/-- Transport the existing local-bijectivity criterion from the small model of the site.
Source: Stacks Project, Sites, Section 00ZG, and Mathlib's existing transport theorem
(blueprint: lem-sfb-internal-scalar-extension-section-test). -/
noncomputable instance scalarExtensionSectionLocalEquivalences :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, w, uC, w + 1, w, w, w} J

variable {R S : Sheaf J AddCommGrpCat.{w}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- The reconstructed section module of S, with R acting through φ. Applying the
section-module equivalence to the restricted regular module retains the section groups
and restriction maps and gives exactly this action.
Source: Stacks Project, Tags 00YV and 03CS
(blueprint: lem-sfb-internal-scalar-extension-section-test). -/
noncomputable def scalarExtensionSectionModule :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R)) :=
  (sectionModuleEquivalence J R).functor.obj ((Mod.comap φ).obj (Mod.regular S))

/-- The pure tensor in the localized sectionwise module tensor. The inverse of the
canonical tensor/sheafification comparison sends the image of the balanced tensor
under the sheafification unit into the chosen sheaf tensor.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sfb-internal-scalar-extension-section-test). -/
noncomputable def scalarExtensionSectionTmul
    (M : Mod (Sheaf J AddCommGrpCat.{w}) R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (m : M.X.obj.obj U) :
    ((scalarExtensionSectionModule J φ) ⊗
      (sectionModuleEquivalence J R).functor.obj M).val.obj U :=
  ((SheafOfModules.tensorObjIsoSheafification (scalarExtensionSectionModule J φ)
    ((sectionModuleEquivalence J R).functor.obj M)).inv.val.app U)
      ((((PresheafOfModules.sheafificationAdjunction (𝟙
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (sectionRingSheaf J R)).obj)).unit.app
        ((scalarExtensionSectionModule J φ).val ⊗
          ((sectionModuleEquivalence J R).functor.obj M).val)).app U)
        (s ⊗ₜ[(sectionRingSheaf J R).obj.obj U] m))

/-- Internal extension followed by restriction corresponds naturally to tensoring on
sectionwise modules with the restricted section-ring sheaf S. The isomorphism fixes
local pure tensors and intertwines every module map with `1 ⊗ E_R(u)`. Internal
extension preserves finite limits precisely when that section module is flat.

Source: Stacks Project, Tags 03CY, 03CZ, 03DB, 03EK, 03EO, 03ER(3), and
Categories, Tags 0034, 0038, 0B65
(blueprint: lem-sfb-internal-scalar-extension-section-test).

Proof following the node:
1. The section equivalences preserve underlying sheaves and section maps. Restricted
internal action is φ(r)n, so E_R Res is naturally sectionwise restriction V followed
by E_S, with the identity on sections (def-pc-sheaf-restrict-scalars).
2. Let Q(F) be the sheafification of U ↦ S(U) ⊗_{R(U)} F(U), with S acting on the
first factor. The balanced rule s ⊗ m ↦ s h(m) and evaluation on 1 ⊗ m give inverse
natural Hom bijections Q ⊣ V. Use module sheafification's universal property
(def-weil-presheaf-modules-sheafification); the unit is m ↦ [1 ⊗ m].
3. The closed sheaf tensor preserves colimits. Transport the internal extension/restriction
adjunction (def-sfb-modobj-extend-restrict-adjunction) through E_R,E_S. Unit-compatible
uniqueness of left adjoints (lem-weil-pbc-conjugate-iso-unit-equation) gives a natural
S-linear comparison E_S Ext ≅ Q E_R carrying [1 ⊗ m] to [1 ⊗ m]. S-linearity gives
the formula for [s ⊗ m].
4. Restricted Q and S ⊗_R - sheafify the same tensor presheaf with the same R-action,
so their identity-on-tensors comparison is natural. Compose it with step 3 and the
restriction identification of step 1 to get θ. Tensor generation and the uniqueness
in sheafification give its naturality and the asserted pure-tensor formula.
5. Module-sheaf limits are computed sectionwise (lem-weil-pbc-module-sheaves-colimits-forgetful).
Thus V preserves finite limits, including the empty one. It reflects isomorphisms:
if f is S-linear with R-linear inverse g, then f(g(sn)) = sn = f(sg(n)), hence
g(sn) = sg(n). The conservative left-exact criterion makes V reflect finite limits
(lem-sfb-conservative-left-exact-reflects-finite-limits).
6. Equivalences and natural isomorphisms preserve the finite-limit test
(lem-galois-equivalence-preserves-limits, lem-sfb-finite-exactness-nat-iso).
Hence Ext preserves finite limits iff Q does. Since V preserves and reflects finite
limits, Q does iff VQ does, by lem-sfb-finite-limit-preservation-cancellation.
Step 4 identifies this with finite-limit preservation of S ⊗_R -.
7. The sheaf tensor is a left adjoint (lem-pc-sheaf-modules-tensor-closed), so it
preserves finite colimits (lem-weil-pbc-left-adjoint-preserves-colimits). Its symmetry
identifies left and right tensor with S. Thus exactness in def-pc-flat-sheaf-modules
is equivalent to finite-limit preservation (def-galois-exact-functor), proving the iff.
All section rings and modules lie in w; none of these arguments excludes zero rings
or the empty site. -/
theorem internalScalarExtension_section_test :
    (∃ θ : Mod.extendScalars φ ⋙ Mod.comap φ ⋙
        (sectionModuleEquivalence J R).functor ≅
      (sectionModuleEquivalence J R).functor ⋙
        tensorLeft (scalarExtensionSectionModule J φ),
      (∀ (M : Mod (Sheaf J AddCommGrpCat.{w}) R) (U : Cᵒᵖ)
          (s : S.obj.obj U) (m : M.X.obj.obj U),
        ((θ.hom.app M).val.app U)
            (((Mod.extendπ φ M).hom.app U)
              (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
                S M.X).app U) (s ⊗ₜ[ℤ] m))) =
          scalarExtensionSectionTmul J φ M U s m) ∧
      (∀ {M N : Mod (Sheaf J AddCommGrpCat.{w}) R} (f : M ⟶ N),
        (sectionModuleEquivalence J R).functor.map
            ((Mod.comap φ).map ((Mod.extendScalars φ).map f)) ≫ θ.hom.app N =
          θ.hom.app M ≫ (tensorLeft (scalarExtensionSectionModule J φ)).map
            ((sectionModuleEquivalence J R).functor.map f))) ∧
    (PreservesFiniteLimits (Mod.extendScalars φ) ↔
      SheafOfModules.IsFlatOnSite (scalarExtensionSectionModule J φ)) := by
  sorry

end CategoryTheory.InternalAbelianSheafModule
