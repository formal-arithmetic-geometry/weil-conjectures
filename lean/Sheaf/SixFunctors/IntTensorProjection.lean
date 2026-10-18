/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.ModuleObjects
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.MultivariableDerivedCalculus

/-!
# Projection formula for extension by zero along a locally closed immersion

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/
 det-lem-int-tensor-projection.md` (blueprint: det-lem-int-tensor-projection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Projection formula for a locally closed immersion, with `a_!` represented by `i_* u_!`.
Source: node `det-lem-int-tensor-projection`,
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.md` (blueprint: det-lem-int-tensor-projection).

The proof follows the source proof, step by step.

1. Identify module objects with sheaves of modules using `sk-def-sfb-module-objects`,
   `def-weil-sheaf-of-modules-category`, `sk-def-sfb-sheaf-tensor`, and
   `def-pur-sheaf-tensor-product`; use `lem-sfb-alpha-iso` for coefficient transport and
   `def-sfb-module-upper-star`, `def-sfb-module-lower-star`,
   `def-sfb-module-open-lower-shriek`, and `def-sfb-module-linear-open-lower-shriek` for
   the specified actions.
2. Use `sk-def-sfb-dc-setting`, `lem-weil-pbc-finite-type-over-noetherian`, and
   `lem-weil-pbc-noetherian-open-subscheme-noetherian` to verify that the three standing
   schemes are Noetherian and qcqs and that every open complement used below is
   quasi-compact.
3. Apply `lem-weil-pbc-proetale-ringed-open-closed` and
   `lem-weil-pbc-proetale-immersion-limit-preservation` to obtain the open--closed
   support identities, exactness, localization sequence, and joint detection of
   isomorphisms.
4. Use `lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
   `def-sfb-module-upper-lower-adjunction`, `lem-weil-pbc-left-adjoint-preserves-colimits`,
   and the filtered-colimit clause of `lem-weil-pbc-proetale-ringed-open-closed` to show
   that inverse image, extension by zero, and closed direct image preserve the coproducts
   needed for unbounded totalization.
5. For an open immersion, form the adjoint of the unit map using the tensor comparison
   of `lem-weil-pbc-ringed-topoi-module-pullback-tensor`; its open restriction is the
   identity and its closed restriction is zero, so step 3 makes it an isomorphism.
6. For a closed immersion, form the unit map into the closed direct image and use
   `def-sfb-module-upper-lower-adjunction`, the same tensor comparison, and the invertible
   closed counit from step 3; its two restrictions again prove it an isomorphism.
7. Apply the two sheaf isomorphisms degreewise to unbounded complexes. The direct sums,
   total differential, and signs are handled by `def-pc-tensor-complex-sheaves`; the
   signed symmetry is checked explicitly, so the resulting maps are chain isomorphisms.
8. If the second complex is K-flat, exactness and the comparison of step 7 show that
   inverse image preserves K-flatness and flat terms, using `def-pc-kflat-complex` and
   `def-pc-flat-sheaf-modules`.
9. The same comparison and signed symmetry show that extension by zero and closed direct
   image preserve flat-term K-flat complexes and flat terms, again using those two
   definitions and exactness from step 3.
10. Choose flat-term K-flat representatives with `lem-pc-kflat-resolution`. Use
    `lem-weil-pbc-exact-functor-derived-factorization` to identify the exact termwise
    functors with their derived functors, and use the representative clause of
    `lem-weil-pbc-site-derived-tensor-descent`, `def-sfb-derived-tensor-modules`, and
    `lem-sfb-derived-tensor-modules-derived` to compute both sides on these representatives.
11. The chain isomorphism is natural on the two homotopy categories: additive functors
    preserve homotopies, and the homotopies in either tensor variable use the signed
    formulas for `def-pc-tensor-complex-sheaves`; the cross terms cancel.
12. Apply the product-localization clause of `lem-sfb-multivariable-derived-calculus`
    to the two resolving classes and then the natural-transformation clause of
    `lem-weil-pbc-localization-universal-property`. This descends the representative
    comparison to a natural isomorphism in both derived variables and makes it
    independent of representatives.
13. Apply steps 10--12 first to the closed immersion with input `u_! M`, and then to
    the open immersion with input `M` and `i^* L`. Compose with
    `def-sfb-module-upper-star-comp`, use `ha : a = u ≫ i`, and substitute the definition
    `a_! = i_* u_!`. This gives the displayed bifunctor isomorphism.
-/
theorem locallyClosedImmersionTensorProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {S Sbar X : Scheme.{u}}
    [S.Over (Spec (.of k))] [Sbar.Over (Spec (.of k))]
    [X.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (Sbar ↘ Spec (.of k))]
    [LocallyOfFiniteType (Sbar ↘ Spec (.of k))]
    [QuasiCompact (Sbar ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X)
    (ha : a = u ≫ i) [a.IsOver (Spec (.of k))]
    [u.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion u] [IsClosedImmersion i] :
    Nonempty (
      (((Functor.whiskeringLeft₂ _).obj
          ((openImmersionLowerShriek Λ u).mapDerivedCategory ⋙
            (lowerStar Λ i).rightDerivedFunctor)).obj (𝟭 _)).obj
        (derivedTensor Λ X) ≅
      (Functor.postcompose₂.obj
        ((openImmersionLowerShriek Λ u).mapDerivedCategory ⋙
          (lowerStar Λ i).rightDerivedFunctor)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          ((a)^*⟦Λ⟧.mapDerivedCategory)).obj (derivedTensor Λ S))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
