/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! # An affine chain representative of a bottom arrow

Source: Stacks Project, Tags 0BDL and 08CR, second proof.
(blueprint: lem-sc-zero-bottom-arrow-affine-chain-model). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A specified bottom arrow has a finite-free chain representative on an affine
refinement of a given zero-bottom chart. Its homology map in the bottom degree
is invertible; invertibility of its component is not part of this assertion.

Source: Stacks Project, Tag 0BDL, zero-matrix chart; Tag 08CR, second proof,
and Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-sc-zero-bottom-arrow-affine-chain-model).

Proof: Choose an affine neighbourhood W of x inside U. Restrict K termwise to W,
obtaining B; exact restriction preserves its zero terms and zero differential,
and preserves finite free terms and the upper bound. Derived composition and
the exact restriction comparison give eB. Exact open pullback commutes naturally
with homology and with single complexes. The hypothesis hf therefore makes the
restricted arrow invertible on H^a. Since both bottom differentials of B vanish,
H^a(B) is B.X a. Identify the restriction of M with B.X a using this isomorphism,
and let A be the single complex on this finite free sheaf in degree a. It is
bounded above by a, finite free in all degrees (rank zero off a), and has all
other terms zero. The single-functor restriction comparison and this sheaf
isomorphism give eA. Transport A and B to the localized site over W via
Scheme.Modules.overEquiv W. Both are strictly perfect there. Apply the affine
perfect-map representative theorem to eA.inv followed by the restricted f
and eB.hom, and transport the resulting chain map back to W.toScheme.
Naturality of localization gives the displayed square. Apply H^a to that square;
the endpoint comparisons are isomorphisms and the restricted H^a(f) is invertible.
The homology factorization of Q then makes H^a(alpha) invertible. Rank zero,
a negative degree and an empty scheme do not alter the construction. -/
theorem zeroBottomArrow_affine_chain_model
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
    (x : T) (hx : x ∈ U) :
    ∃ W : T.Opens, x ∈ W ∧ W ≤ U ∧ IsAffineOpen W ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i)) ∧
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i)) ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
          (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
          (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        (∀ i : ℤ, i ≠ a → IsZero (A.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (B.X i)) ∧ B.d a (a + 1) = 0 ∧
        ∃ α : A ⟶ B, IsIso (HomologicalComplex.homologyMap α a) ∧
          ∃ (eA : (derivedPullback W.ι).obj ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M) ≅
                DerivedCategory.Q.obj A)
            (eB : (derivedPullback W.ι).obj D ≅ DerivedCategory.Q.obj B),
            (derivedPullback W.ι).map f ≫ eB.hom =
              eA.hom ≫ DerivedCategory.Q.map α := by sorry

end AlgebraicGeometry.Scheme
