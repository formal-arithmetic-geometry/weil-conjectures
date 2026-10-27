/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Global module sections on an H1-acyclic algebraic space

Source: Stacks Project, Spaces Cohomology, Situation 07UY and Lemma 07UZ
(lemma-vanishing-compute)
(blueprint: lem-sfb-space-acyclic-global-module-sections).

The cone with vertex A identifies A with the ring of all compatible chart functions.
Its normalization says that p induces the identity on those functions. The conclusion
makes the actual composite adjunction unit an isomorphism of natural transformations.
Its components are the canonical maps M -> Gamma(X,p^* tilde(M)_et), with their A-actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The associated small étale module of an arbitrary module on an affine scheme.
This is the existing affine tilde functor followed by the existing represented-scheme
Zariski/étale tensor extension; no second extension construction is introduced.
Source: Stacks, Descent, Tags 03DU and 03FH
(blueprint: lem-sfb-space-acyclic-global-module-sections). -/
def affineEtaleAssociated (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤
      (schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A)))).Modules :=
  tilde.functor A ⋙
    evaluationZariskiExtension (Over.mk (specULiftZIsTerminal.from (Spec A)))

/-- The affine associated-module/global-sections adjunction, with its actual unit.
The right adjoint is the existing represented-scheme restriction to Zariski opens
followed by affine global sections. Its unit is the composite of the existing units.
Source: Stacks, Descent, Tags 03DU and 03FH
(blueprint: lem-sfb-space-acyclic-global-module-sections). -/
def affineEtaleAssociatedAdjunction (A : CommRingCat.{u}) :
    affineEtaleAssociated A ⊣
      evaluationZariskiRestriction (Over.mk (specULiftZIsTerminal.from (Spec A))) ⋙
        moduleSpecΓFunctor :=
  tilde.adjunction.comp
    (evaluationZariskiAdjunction (Over.mk (specULiftZIsTerminal.from (Spec A))))

/-- The canonical global-section units are A-linear isomorphisms, naturally in all modules.
No finite generation, Noetherianity, nonemptiness or flatness condition is imposed.
Source: Stacks Project, Spaces Cohomology, Tags 07UY and 07UZ
(blueprint: lem-sfb-space-acyclic-global-module-sections).

Proof:
1. Present M by free modules F1 -> F0 -> M -> 0, taking bases indexed by the elements
   of M and then the elements of the kernel of F0 -> M. No injectivity of F1 -> F0
   is claimed.
2. T = p^* tilde(-)_et preserves sums and cokernels: use the affine tilde adjunction,
   the Zariski-etale quasi-coherent equivalence, lem-sfb-space-qcoh-kernels-colimits,
   and left-adjoint preservation of colimits. The chart tensor formula of
   lem-trf-space-chart-adjunction-tensor-realization identifies T(A) with O_X.
3. Express an arbitrary sum of copies of O_X as the filtered colimit of its finite
   subsums. The forgetful module-sheaf functor preserves this colimit. Apply
   lem-sfb-space-cohomology-filtered-colimit in degree zero, using qcqs of X.
   Thus Gamma of that sum is the corresponding free A-module. The chart-unit
   formula identifies this comparison with the actual unit on each basis element.
4. Forget a quasi-coherent short exact sequence to additive sheaves. Exactness of
   the forgetful functor and the derived-functor long exact sequence show that
   Gamma is right exact, since H1 of the quasi-coherent kernel vanishes.
5. The image and kernel of T(F1) -> T(F0) are quasi-coherent by
   lem-sfb-space-qcoh-kernels-colimits. Apply step 4 twice to obtain the exact
   Gamma-row ending in Gamma(T(M)). Compare with the free presentation in step 1.
   The first two unit maps are invertible by step 3, hence the induced cokernel
   map is invertible; it is precisely the unit for M.
6. A map v sends the local tensor 1 tensor m to 1 tensor v(m), so the units commute
   with all A-linear maps. This is also the naturality of the displayed composite
   adjunction unit. Zero modules, the zero ring, and the empty space are included. -/
theorem isIso_acyclic_global_module_unit
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u})]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (hH : ∀ (F : X.Modules) (_ : F.IsQuasicoherent),
      Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1))
    (A : CommRingCat.{u})
    (p : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec A))))
    (πA : (Functor.const X.EtaleSiteᵒᵖ).obj A ⟶ X.etaleForget.op ⋙ Scheme.Γ)
    (hA : IsLimit (Cone.mk A πA))
    (hp : ∀ T : X.EtaleSite,
      πA.app (op T) = (Scheme.ΓSpecIso A).inv ≫
        (yoneda.preimage (T.obj.hom ≫ p.hom.hom)).left.appTop) :
    IsIso (((affineEtaleAssociatedAdjunction A).comp (moduleTensorAdjunction p)).unit) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
