/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.SpaceStalkIdealPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction

import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal

/-! # Quasi-coherent modules along a closed immersion of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 03MB and 04CJ
(blueprint: lem-sfb-space-closed-immersion-quasi-coherent-modules).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction of the specified module direct image to the full quasi-coherent
subcategories, using its preservation of quasi-coherence. Its object and map data are
those of moduleDirectImage, with only the quasi-coherence proof attached.
Source: Stacks Project, Morphisms of Spaces, Tag 04CJ
(blueprint: lem-sfb-space-closed-immersion-quasi-coherent-modules). -/
def quasiCoherentDirectImage
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (hqc : ∀ M : Z.Modules, M.IsQuasicoherent →
      ((moduleDirectImage i).obj M).IsQuasicoherent) : QCoh Z ⥤ QCoh X :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).lift
    (ObjectProperty.ι _ ⋙ moduleDirectImage i) (fun M ↦ hqc M.obj M.property)

/-- A closed immersion has quasi-coherent direct image and identifies its quasi-coherent
modules with the modules annihilated by the defining ideal.

Source: Stacks Project, Morphisms of Spaces, Tags 03MB and 04CJ
(blueprint: lem-sfb-space-closed-immersion-quasi-coherent-modules).
Proof:
1. After every affine scheme test Spec R → X the closed source is Spec(R/J).
   This is quasi-compact, and the quotient map is a monomorphism, so the diagonal
   is an isomorphism and hence closed. Thus i is quasi-compact and separated in
   lem-trf-space-qc-separated-etale-local. Apply
   lem-trf-space-qc-separated-quasi-coherent-pushforward to every quasi-coherent G,
   including the one-generator structure module O_Z.
2. By lem-trf-space-etale-module-pushforward-restriction, the structure map on an
   affine étale chart is R → R/J. Affine opens cover every chart, so it is locally
   surjective, not necessarily surjective on nonaffine section rings. Multiplicativity
   makes the kernel an ideal; lem-sfb-space-qcoh-kernels-colimits makes it quasi-coherent.
3. Use the exactness and conservativity of stalks from
   lem-sfb-space-stalk-ideal-pullback on identity thickenings (zero ideals). The natural
   closed stalk comparison lem-sfb-space-closed-pushforward-geometric-stalks identifies
   the direct-image structure stalk at i(z) with B = O_Z,z. The structure stalk map
   A → B is surjective with kernel I_x, so B = A/I_x. Outside Z the target stalk is
   zero and I_x = A. These comparisons are restriction of germs and respect products.
4. The ordinary clause of lem-sfb-space-geometric-stalk-tensor-calculus, using the
   identity square and complexes in degree zero, identifies pullback stalks with
   tensor products. The counit of def-trf-space-etale-module-functors is therefore
   G_z ⊗_A B → G_z, m ⊗ b ↦ bm. Its inverse is m ↦ m ⊗ 1, because A → B is
   surjective. Stalk conservativity makes the counit invertible. On Hom sets the
   inverse to direct image takes alpha to epsilon ∘ i^*(alpha) ∘ epsilon^{-1};
   naturality and the triangle identities prove both inverse equations.
5. The kernel ideal kills every direct image by the prescribed scalar action.
   Conversely, for quasi-coherent F killed by I, the module i^*F is quasi-coherent
   by lem-sfb-space-module-pullback-quasicoherent. The unit has stalk m ↦ m ⊗ 1
   into F_x ⊗_A (A/I_x), with inverse m ⊗ a-bar ↦ am, independent of the lift.
   Outside Z, I_x = A forces F_x = 0 and the direct-image stalk is zero.
   Stalk conservativity proves the unit invertible, giving the essential image.
6. For a short exact sequence on Z, the direct-image stalk sequence is the original
   exact sequence on Z and zero outside Z. Exact and conservative stalk functors
   detect exactness: kernel modulo image has zero stalks and hence is zero. By
   lem-sfb-space-qcoh-kernels-colimits the kernels and cokernels agree with those in
   all modules. Thus the restricted functor is exact, equivalently it preserves
   finite limits and finite colimits in these abelian quasi-coherent categories. -/
theorem closedImmersion_quasiCoherent_modules
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    ∃ (hqc : ∀ M : Z.Modules, M.IsQuasicoherent →
        ((moduleDirectImage i).obj M).IsQuasicoherent)
      (I : QuasiCoherentIdeal X),
      ((moduleDirectImage i).obj (SheafOfModules.unit Z.structureSheaf)).IsQuasicoherent ∧
      Epi (moduleStructureMap i) ∧
      I.val = kernelSubobject (moduleStructureMap i) ∧
      PreservesFiniteLimits (quasiCoherentDirectImage i hqc) ∧
      PreservesFiniteColimits (quasiCoherentDirectImage i hqc) ∧
      (quasiCoherentDirectImage i hqc).Full ∧
      (quasiCoherentDirectImage i hqc).Faithful ∧
      (∀ F : QCoh X,
        (∃ G : QCoh Z, Nonempty (F ≅ (quasiCoherentDirectImage i hqc).obj G)) ↔
          ∀ (V : X.EtaleSite)
            (a : (I.val : X.Modules).val.obj (op V)) (m : F.obj.val.obj (op V)),
            (I.val.arrow.val.app (op V) a) • m = 0) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
