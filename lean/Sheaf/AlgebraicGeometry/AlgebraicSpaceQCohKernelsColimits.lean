module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.SmallEtaleQuasiCoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Kernels and colimits of quasi-coherent modules on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03M1
(`lemma-properties-quasi-coherent`), clauses (1), (2), (3)
(blueprint: lem-sfb-space-qcoh-kernels-colimits).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-coherent modules on the small etale site are closed under ambient kernels,
cokernels, small colimits, direct sums and images. Their full inclusion preserves
kernels, cokernels and small colimits, which also exist in the full subcategory.
Source: Stacks Project, Properties of Spaces, Tag 03M1, clauses (1), (2), (3)
(blueprint: lem-sfb-space-qcoh-kernels-colimits).

Proof:
1. Choose a surjective etale scheme atlas U -> X. By
lem-trf-space-representable-etale-scheme-tests the localized site at a chart V is
V_et, with its regular-functions ring. The exact restriction of
lem-weil-pbc-ringed-sheaf-slice-adjunction is also a left adjoint by
lem-weil-pbc-ringed-topoi-module-adjunction, hence preserves all small colimits by
lem-weil-pbc-left-adjoint-preserves-colimits. Ambient colimits and the abelian
structure are supplied by lem-pur-ringed-site-grothendieck-abelian.
2. The local-presentation predicate def-trf-space-quasi-coherent-module restricts
to slices. Conversely pull the atlas back to every chart V and refine that cover
by the presentation covers on U. Relocalization (def-pur-localized-ringed-site)
identifies those presentations, so quasi-coherence is detected on the atlas.
3. On a scheme T, use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.
Its forward functor is tensor pullback, a left adjoint by
lem-weil-pbc-ringed-topoi-module-adjunction, so it preserves ambient colimits.
4. Zariski colimits are quasi-coherent: restrict to affine opens by
lem-weil-pbc-module-restriction-open-immersion-colimits, write the diagram as tilde
modules by lem-weil-pbc-affine-tilde-gamma-adjunction, form its module colimit by
lem-weil-pbc-ring-modules-grothendieck-abelian, and apply tilde. The adjunction
identifies this with the ambient colimit; lem-weil-pbc-spec-module-tilde-sections
and pqf-def-coherent give quasi-coherence. Transport by step 3 to T_et.
5. Scheme etale kernels are quasi-coherent by
lem-trf-scheme-etale-quasi-coherent-kernel. Lift a map to the Zariski category;
lem-weil-pbc-quasi-coherent-module-cokernel-image gives its quasi-coherent
cokernel, and step 3 identifies its etale pullback with the ambient cokernel.
6. Restrict ambient kernels, cokernels and colimits to U. Step 1 identifies the
restricted constructions, steps 4 and 5 prove their quasi-coherence, and step 2
descends it to X. Neither separation nor Noetherianity is used.
7. Fullness restricts each ambient universal property to quasi-coherent test
objects, giving existence and preservation in QCoh. Direct sums are discrete
colimits. In the ambient abelian category (def-weil-sheaf-of-modules-category),
the image is the kernel of the cokernel map, so it is quasi-coherent as well.
This includes the empty diagram and zero maps. -/
theorem quasiCoherent_kernels_colimits {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (∀ (M N : X.Modules) (f : M ⟶ N), M.IsQuasicoherent → N.IsQuasicoherent →
      (kernel f).IsQuasicoherent ∧ (cokernel f).IsQuasicoherent ∧
        (Abelian.image f).IsQuasicoherent) ∧
    (∀ (J : Type u) [Category.{u} J] (F : J ⥤ X.Modules),
      (∀ j : J, (F.obj j).IsQuasicoherent) → (colimit F).IsQuasicoherent) ∧
    HasKernels X.QCoh ∧ HasCokernels X.QCoh ∧ HasColimitsOfSize.{u, u} X.QCoh ∧
    (∀ (M N : X.QCoh) (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (SheafOfModules.isQuasicoherent X.structureSheaf).ι ∧
      PreservesColimit (parallelPair f 0) (SheafOfModules.isQuasicoherent X.structureSheaf).ι) ∧
    PreservesColimitsOfSize.{u, u} (SheafOfModules.isQuasicoherent X.structureSheaf).ι ∧
    (∀ (I : Type u) (M : I → X.Modules),
      (∀ i : I, (M i).IsQuasicoherent) → (∐ M).IsQuasicoherent) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
