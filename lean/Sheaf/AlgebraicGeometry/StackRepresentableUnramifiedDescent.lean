/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent

/-! # Unramifiedness descends along a flat algebraic-space cover

Source: Stacks Project, stacks-properties.tex, Tag 04XD (lemma-check-property-covering),
with the unramified property from Section 04XB
(blueprint: lem-sfb-stack-representable-unramified-descent).

The cover's surjectivity is tested on the actual algebraic-space projections after
all scheme base changes. The conclusion uses the existing chartwise property test
and the actual first projection from the existing 2-fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A representable stack morphism is unramified exactly when its pullback to a
surjective flat locally finitely presented algebraic-space cover is unramified.
Source: Stacks Project, stacks-properties.tex, Tag 04XD and Section 04XB
(blueprint: lem-sfb-stack-representable-unramified-descent).

Proof:
1. The representable diagonal of B makes q representable by algebraic spaces
   [lem-sfb-stack-diagonal-space-source-representability]. For a scheme T -> B put
   X_T = T x_B A and W_T = T x_B W. For a scheme E -> W_T, its comparison eta gives
   the equivalence X_T x_T E = (W x_B A) x_W E over E: send alpha to alpha eta^{-1}
   and send beta back to beta eta. These formulas preserve arrows and pullbacks
   [def-sfb-stable-pointed-moduli-groupoids].
2. If f is unramified, apply its scheme tests to every etale scheme chart E -> W,
   then to every etale scheme chart of E x_B A. This is precisely the chart test
   for W x_B A -> W [def-trf-algebraic-space].
3. Conversely, for T -> B choose a surjective etale scheme atlas E -> W_T.
   The composite p : E -> T is flat and locally of finite presentation by base
   change, etale-implies-smooth, smooth-implies-flat-and-lfp, and composition
   [lem-sfb-stack-chartwise-smooth-etale-calculus]. Surjectivity on the actual
   scheme base change, as in the hypothesis, makes p surjective.
4. The singleton family p is fpqc [def-weil-pbc-fpqc-covering]. Indeed p is open
   [lem-weil-pbc-flat-lfp-open]. Cover the inverse image of an affine open T_0
   by affine opens of E. Their open images cover T_0, and quasi-compactness
   [lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact] selects finitely many.
   These affine opens all map inside T_0, so the union of their images equals T_0.
   For empty T_0 use the empty finite family; no quasi-compactness of p is needed.
5. For any etale scheme chart U -> X_T, form U_E = U x_T E
   [def-pc-fibre-product]. The comparison in step 1 identifies its map to
   V_E = (W x_B A) x_W E, and its composite to E is the second projection
   [lem-trf-space-fibre-products-etale-covers]. The chart map is etale by base
   change [lem-trf-space-chartwise-etale-permanence]. Unramified base change,
   etale-implies-unramified and composition make U_E -> E unramified
   [lem-sfb-space-unramified-permanence].
6. Scheme fpqc descent [lem-galois-fpqc-descend-unramified] applied to U -> T
   and the singleton cover E -> T makes U -> T unramified. Since U and T were
   arbitrary, the chart tests give unramifiedness of f. -/
theorem stack_representable_unramified_descent {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (f : BasedFunctor A B) (hf : IsRepresentableByAlgebraicSpaces f)
    (W : AlgebraicSpace S) (q : BasedFunctor (discreteModuli W.obj.obj) B)
    (hs : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) B),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange q T t Z p ∧ SpaceMapIsSurjective Z T p)
    (hflat : ModuliSpaceTest @Flat q)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q) :
    ModuliSpaceTest @IsUnramified f ↔
      ModuliSpaceTest @IsUnramified (moduliTwoFiberFst q f) := by
  sorry

end CategoryTheory
