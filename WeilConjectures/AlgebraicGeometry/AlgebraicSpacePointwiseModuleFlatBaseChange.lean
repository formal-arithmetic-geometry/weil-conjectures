/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleFlatAtPoint
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import WeilConjectures.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.PointwiseModuleFlatnessBaseChange

/-! # Pointwise module flatness under base change of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 05VW, clauses (1), (2) and final sentence
(blueprint: lem-sfb-space-pointwise-module-flat-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative module flatness ascends at every point under arbitrary base change and is
reflected when the base map is flat at the image point. Global flatness also ascends.
The cartesian square permits any realization of the specified fibre product.
Source: Stacks Project, Morphisms of Spaces, Tag 05VW
(blueprint: lem-sfb-space-pointwise-module-flat-base-change).

Proof:
1. Choose an etale surjective scheme atlas V of Y, then atlases U of X times_Y V
   and V' of Y' times_Y V. Their composites a:U -> X and c:V' -> Y' are etale
   surjective, by lem-trf-space-fibre-products-etale-covers and
   lem-trf-space-chartwise-etale-permanence. The scheme U'=U times_V V' maps etale
   surjectively to X'. Lift x' to u' and write u, v' for its two images. They map
   to x=q(x') and y'=f'(x'), so the chosen charts are at the specified points.
2. The modules pulled back to these charts are quasi-coherent by
   lem-sfb-space-module-pullback-quasicoherent. The identity q a'=a p and the
   normalized moduleTensorComposition of def-sfb-space-module-tensor-composition
   identify a'^*(q^*M) with p^*(a^*M). The functorial tensor comparison of
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies their Zariski
   restrictions with ordinary scheme tensor pullback, respecting base scalars.
3. If M is flat at x, apply lem-sfb-pointwise-module-flatness-base-change (1)
   to U times_V V' and the restriction of M. Its pullback stalk is flat over
   the local ring of V' at v'. By step 2 this is the chart stalk of q^*M.
   lem-sfb-space-module-flat-arbitrary-charts transfers this one-chart condition
   to every compatible chart at x', giving ModuleIsFlatAt f' (q^*M) x'.
4. For reflection, the every-chart flatness hypothesis on g gives flatness of
   V' -> V at v'. Apply lem-sfb-pointwise-module-flatness-base-change (2) to the
   same scheme square and use step 2. The stalk of M at u is flat over V at v.
   lem-sfb-space-module-flat-arbitrary-charts gives every-chart flatness at x.
   No flatness of g away from y' is used.
5. If M is flat over Y, apply (1) at each point of X'. The quasi-coherent
   affine-local/stalk criterion identifies this with ModuleIsFlatOver f' (q^*M).
   If X' is empty there are no point tests and the same global assertion holds. -/
theorem pointwise_module_flat_base_change {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (q : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback q f' f g)
    (M : X.Modules) [M.IsQuasicoherent] :
    (∀ x' : Point X'.obj.obj,
      (ModuleIsFlatAt f M (mapPoint q.hom.hom x') →
        ModuleIsFlatAt f' ((moduleTensorPullback q).obj M) x') ∧
      ((∀ (U : Y'.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left),
        U.obj.hom ≫ g.hom.hom = yoneda.map h ≫ V.obj.hom →
          ∀ u : U.obj.left.left,
            schemePointMap U.obj.hom u = mapPoint f'.hom.hom x' →
              (h.left.stalkMap u).hom.Flat) →
        ModuleIsFlatAt f' ((moduleTensorPullback q).obj M) x' →
          ModuleIsFlatAt f M (mapPoint q.hom.hom x'))) ∧
    (ModuleIsFlatOver f M → ModuleIsFlatOver f' ((moduleTensorPullback q).obj M)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
