/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity

import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.RelativeAssassin
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport

/-! # Proper support implies universal relative purity

Source: Stacks Project, spaces-flat.tex, Tag 0CVI, lemma-proper-pure (1);
spaces-perfect.tex, Tag 0CZI, lemma-module-support-proper-over-base (3)
(blueprint: lem-sfb-space-proper-support-universal-purity).

The proper-support assumption is exactly the closed-carrier condition used by
`ProperQuotient.properSupport`, without requiring a quotient or finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite type quasi-coherent module with a proper closed carrier is universally
pure relative to its scheme base.
Source: Stacks Project, spaces-flat.tex, Tag 0CVI, lemma-proper-pure (1), with the
carrier formulation of spaces-perfect.tex, Tag 0CZI (3)
(blueprint: lem-sfb-space-proper-support-universal-purity).

Proof:
1. Put T = Supp(M). By lem-sfb-space-finite-type-support-pullback it is closed.
   The isomorphism i_*N ≅ M and lem-sfb-space-closed-pushforward-geometric-stalks
   make its stalks vanish outside A = |i|(|Z|), so T is contained in A.
   By lem-sfb-space-closed-subspace-proper the immersion i is proper; universal
   closedness at the identity base change makes A closed.
2. Apply lem-sfb-space-proper-support-closed-operations to Z, A and T: T is proper
   over Y. By lem-sfb-space-reduced-closed-support its reduced induced closed
   subspace W is proper over Y. No descent of M to the reduced subspace is needed.
3. After any scheme base change B → Y, lem-sfb-space-proper-base-change makes
   W_B → B proper. The reduced-closed-support theorem identifies |W_B| with the
   inverse image of T, even though W_B need not be reduced. By the finite-type
   support-pullback theorem this inverse image is exactly Supp(M_B).
4. For an associated point ξ of M_B over b', choose an etale chart and a fibrewise
   associated point u mapping to ξ, using def-sfb-space-universal-relative-purity.
   By def-trf-relative-assassin the fibre stalk has a nonzero element annihilated
   precisely by its maximal ideal. Thus the original chart stalk is nonzero.
   By lem-sfb-space-etale-chart-support, ξ lies in Supp(M_B) = |W_B|.
5. For any specialization b' ↝ b, the image under the proper map W_B → B of
   the closure of ξ is closed and contains b', hence contains b. Choose θ in
   that closure over b. The closed embedding |W_B| → |X_B| identifies this
   closure with the closure in |X_B|, by the reduced-closed-support theorem.
6. This supplies a specialization over b for every scheme base change and every
   relative associated point. It excludes all impurities and is precisely
   IsUniversallyPureRelativeToScheme, as defined in def-sfb-space-universal-relative-purity. -/
theorem universallyPureRelativeToScheme_of_properSupport
    {X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (hf : MapIsFiniteType f) (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.QCoh) (hM : SheafOfModules.IsFiniteType M.obj)
    (hsupport : ∃ (Z : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ N : Z.QCoh,
        SheafOfModules.IsFiniteType N.obj ∧
          Nonempty ((moduleDirectImage i).obj N.obj ≅ M.obj)) :
    IsUniversallyPureRelativeToScheme Y f hf hqs M hM := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
