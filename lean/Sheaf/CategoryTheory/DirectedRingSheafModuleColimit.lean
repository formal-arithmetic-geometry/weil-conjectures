/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Directed ring-sheaf colimits as module-sheaf colimits

Source: agent assembly from Stacks Project, Modules on Sites, Tags 03DB
(lemma-limits-colimits) and 03EP (lemma-tensor-commute-colimits), item (2).
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit).

The conclusion is the explicit existence-and-uniqueness universal property. Compatibility
and factorization are equalities on sections, so no separate choice of linear transition
maps or cocone legs is involved.

## Main definitions

* `siteRingSheafModule`: the existing regular module restricted along the scalar map.

## Main statements

* `directedRingSheaf_module_colimit`: the explicit module-colimit universal property.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The module underlying a ring sheaf with its specified scalar map: restrict the regular
module along that map. Thus on each object its scalar action is `r • x = s(r) * x`.
This is only an abbreviation for Mathlib's restriction of scalars and regular module.
Source: Stacks Project, Modules on Sites, module structures used in Tags 03DB and 03EP.
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit). -/
noncomputable abbrev siteRingSheafModule {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R A : Sheaf J CommRingCat.{w}} (s : R ⟶ A) :
    ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map s)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A))

/-- The ring-colimit cocone has the module-colimit universal property with exactly the
same maps on sections and the scalar actions induced by the specified structure maps.
Source: agent assembly from Stacks Project, Modules on Sites, Tags 03DB and 03EP(2).
(blueprint: lem-sfb-directed-ring-sheaf-module-colimit).

Proof:
1. Scalar compatibility makes the transition maps and the given cocone maps linear.
   By lem-weil-pbc-module-sheaves-colimits-forgetful form the module colimit L, with
   legs b_i, and its induced linear map u to A. Essential smallness allows sheafification
   in the coefficient universe by passage to a small site skeleton.
2. For i,j choose a common upper bound k. The balanced formula
   x tensor y maps to b_k(a_ik(x) * a_jk(y)) defines A_i tensor A_j to L, using
   def-pur-sheaf-tensor-product and def-weil-presheaf-modules-sheafification. A common
   upper bound of two choices proves independence and compatibility in both variables.
3. Apply lem-weil-pbc-independent-sheaf-tensor-colimits twice, using the tensor swap
   for preservation in the other variable, to obtain multiplication on L. Equality of
   maps from L tensor L can be checked after all pairs of colimit legs.
4. Choose i_0 and take e = b_i_0(1). Common upper bounds show b_i(1) = e for all i.
   Check commutativity and the unit laws on colimit legs, and associativity on triples
   of legs using tensor-colimit preservation three times. In a common stage these are
   the ring laws. Bilinearity gives distributivity, making L a commutative ring sheaf
   and the b_i unital ring maps.
5. Define the scalar map s_L(r) = r e = b_i(s_i(r)). It is a unital ring map, and
   multiplication through it agrees with L's original module action. Checking on pairs
   of legs shows u is multiplicative; also u(e) = 1. Hence u is a unital ring map.
6. The given ring-colimit property supplies v : A to L with v q_i = b_i. Since
   v s = s_L, it is linear. Module-colimit uniqueness gives v u = 1 and ring-colimit
   uniqueness gives u v = 1. Thus u is a module isomorphism respecting the legs.
7. A compatible family f_i factors uniquely as g through L. Then g v is the required
   map from A, and precomposition with u proves uniqueness. -/
theorem directedRingSheaf_module_colimit
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (I : Type w) [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (A : I ⥤ Sheaf J CommRingCat.{w})
    (sᵢ : (Functor.const I).obj R ⟶ A)
    (q : Cocone A) (_hq : IsColimit q) (s : R ⟶ q.pt)
    (_hs : ∀ i : I, sᵢ.app i ≫ q.ι.app i = s)
    (M : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (fᵢ : ∀ i : I, siteRingSheafModule (sᵢ.app i) ⟶ M)
    (_hf : ∀ (i j : I) (h : i ≤ j) (U : Cᵒᵖ) (x : (A.obj i).obj.obj U),
      (fᵢ j).val.app U ((A.map (homOfLE h)).hom.app U x) = (fᵢ i).val.app U x) :
    ∃! f : siteRingSheafModule s ⟶ M,
      ∀ (i : I) (U : Cᵒᵖ) (x : (A.obj i).obj.obj U),
        f.val.app U ((q.ι.app i).hom.app U x) = (fᵢ i).val.app U x := by
  sorry

end CategoryTheory
