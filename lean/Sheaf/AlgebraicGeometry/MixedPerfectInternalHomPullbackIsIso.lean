/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison

/-! # Perfect internal-Hom pullback with no module localization choice
Source: Stacks Project, cohomology.tex, Tags 08I3 and 0FPC.
(blueprint: lem-sc-mixed-perfect-internal-hom-pullback-isIso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The evaluation-mate map on sheaf internal Hom is invertible for perfect M.
It uses no global sections or scalar extension and assumes no flatness or qcqs.
Source: Stacks Project, cohomology.tex, Remark 08I3 and Example 0FPC.
(blueprint: lem-sc-mixed-perfect-internal-hom-pullback-isIso).

Proof: locally resolve M by a bounded complex of finite projective modules. The
canonical tensor-Hom equivalence computes evaluation on this representative.
RHom(M,N) is N tensored with the finite-projective dual of M, even for unbounded
N. Termwise pullback preserves finite-projective duals and their evaluation.
The canonical tensor pullback comparison, normalized to the shared derived
counit, identifies pullback of this tensor with tensor of the pulled-back factors.
Consequently the displayed adjunct is the finite-projective tensor-Hom
isomorphism on every such neighbourhood. Compatibility with restriction and
cohomology shows it is globally invertible. Equivalently, transport the perfect
dual's exact evaluation/coevaluation pairing through strong monoidal pullback;
the triangle identities identify its adjunct with this map. Applying the
injective tensor-Hom equivalence checks the equality: both evaluations are
pullback of evaluation preceded by the inverse canonical tensor comparison.
For M=0 or an empty source the map is the unique isomorphism between zero objects. -/
theorem mixedPerfect_internalHom_pullback_isIso
    {T X : Scheme.{u}} (g : T ⟶ X)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M N : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M) :
    IsIso
      (((schemeDerivedTensorHomEquiv T)
        ((derivedPullback g).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N)))
        ((derivedPullback g).obj M) ((derivedPullback g).obj N)).symm
        ((mixedHomTensorPullbackIso g).inv.app
            ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N), M) ≫
          (derivedPullback g).map
            ((schemeDerivedTensorHomEquiv X)
              ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N))
              M N (𝟙 _)))) := by sorry

end AlgebraicGeometry
