/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.Over

/-!
# Triangulated compactly supported direct image at a finite coefficient level

Source: Weil conjectures blueprint, `sk-def-sf-operations`, clause (iv), node order 1493
(blueprint: lem-compact-support-direct-image-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- For every compactification, finite-level compactly supported direct image commutes
with integer shifts and sends distinguished triangles to distinguished triangles.
The shift structure is the canonical composite structure on derived extension by zero
followed by the total right derived direct image.

Source: blueprint `lem-compact-support-direct-image-triangulated`, order 1493, in
`sk-def-sf-operations`, clause (iv)
(blueprint: lem-compact-support-direct-image-triangulated).

Proof plan:
1. Fix `c = (j,p)`. By def-weil-compact-support-candidate and
   def-weil-pbc-proetale-site the functor is the composite on the unbounded derived
   categories of constant-coefficient module sheaves on the small pro-etale sites.
2. The ring `A_{E,n}` is finite by def-weil-l-adic-coefficient-extension. Extension
   by zero is exact by lem-weil-extension-by-zero-exact. Its termwise derived functor
   is triangulated by lem-sf-exact-functor-derived-triangulated.
3. By prop-pur-kinjective-resolutions-exist these module-sheaf categories have
   unbounded K-injective resolutions. Pushforward is additive and left exact by
   lem-weil-proetale-module-direct-image-left-exact. The invertibility of `l` in `K0`
   implies its invertibility on the schemes over `K0`, including the ambient scheme
   via `p`. The finite-level functor of def-weil-derived-direct-image is therefore
   triangulated by lem-pc-right-derived-functor-triangulated, without a boundedness
   or etale-origin restriction.
4. Apply lem-weil-pbc-triangulated-functor-composite. If the shift isomorphisms of
   `J = Dj_!` and `P = Rp_*` are `phi` and `psi`, that of `J ⋙ P` is
   `P(phi_K)` followed by `psi_{JK}`. The last arrow of its image triangle is
   `P(J(w))` followed by these two maps: functoriality rewrites the iterated image
   as this composite. It is distinguished since both factors are triangulated.
   This is precisely the functor of def-compact-support-direct-image-detailed,
   and the chosen compactification was arbitrary. -/
theorem compactSupportDirectImage_isTriangulated
    (K0 : Type u) [Field K0] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K0))] [Y.Over (Spec (CommRingCat.of K0))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K0))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K0))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K0))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K0))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of K0))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : K0))
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) (c : Compactification f) :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c :
        ModuleDerivedCategory X (Padic.coefficientExtensionRing l E n) ⥤
        ModuleDerivedCategory Y
          (Padic.coefficientExtensionRing l E n)).IsTriangulated := by
  -- The candidate is Dj_! followed by Rp_*, with their canonical composite shift.
  infer_instance

end AlgebraicGeometry.ProEtale
