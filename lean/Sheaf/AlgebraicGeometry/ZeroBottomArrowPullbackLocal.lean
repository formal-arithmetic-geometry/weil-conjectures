/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! # Local pullback of a bottom truncation arrow
Source: Stacks Project, Tag 0BDL, zero-matrix chart argument.
(blueprint: lem-sc-zero-bottom-arrow-pullback-local). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- On one zero-bottom model chart, pullback preserves the bottom homology
isomorphism of a specified arrow from a single sheaf.
Source: Stacks Project, Tags 0BDL, 06YD, 06YJ, 0D5S and 08CR, second proof.
(blueprint: lem-sc-zero-bottom-arrow-pullback-local).

Proof: Restrict f to U. Exact restriction and the given isomorphism e identify
its bottom homology with a map M|U -> K.X a; the map is invertible by hf.
Refine U by affine opens, trivializing M|U by this identification with the
finite free K.X a. On an affine refinement, represent the restricted derived
arrow by a chain map from the single finite-free complex to the restricted K
using the affine perfect-map representative theorem. Both complexes have zero
incoming and outgoing differentials at a. Their homology map therefore is the
a-th component of the chain map, which is invertible. Both complexes are
bounded above and flat. The natural flat-complex counit represents pullback
of the specified arrow by its termwise pullback. The a-th component remains
invertible, and the zero bottom differentials persist. Exact open restriction
and derived composition identify this computation with the restriction of
H^a(Lg*f). Take the inverse image of the affine refinement containing g(y).
This gives V containing y and the asserted invertibility on V. No gluing of
chosen local object isomorphisms is needed: the arrow f is fixed globally.
Zero ranks, negative a, empty opens, and an empty source cause no exception. -/
theorem zeroBottomArrow_pullback_local
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (f : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M ⟶ D)
    (hf : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).map f))
    (U : T.Opens)
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
    (hbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i))
    (hnegative : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hzero : K.d a (a + 1) = 0)
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (e : (derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K)
    (T' : Scheme.{u}) (g : T' ⟶ T) (y : T') (hy : g.base y ∈ U) :
    ∃ V : T'.Opens, y ∈ V ∧
      IsIso (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
          ((derivedPullback g).map f)).over V) := by sorry

end AlgebraicGeometry.Scheme
