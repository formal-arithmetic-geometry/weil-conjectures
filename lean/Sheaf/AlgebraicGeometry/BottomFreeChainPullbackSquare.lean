/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison

/-! # Pullback of a specified finite-free bottom chain square

Source: Stacks Project, Tags 06YD, 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-bottom-free-chain-pullback-square). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A specified chain square on a scheme chart pulls back to a bottom homology
square on the localized open site. This only transports a chain representative;
it neither constructs one nor asserts invertibility of the resulting homology map.

Source: Stacks Project, Tags 06YD and 06YJ (flat termwise computation),
0D5S (composition) and 08DW (open restriction).
(blueprint: lem-sc-bottom-free-chain-pullback-square).

Proof: Set V to the inverse image of W under g and use hy to see y in V. Let
h : V.toScheme -> W.toScheme be the restricted morphism. Finite free terms of
A and B are flat, and both complexes are bounded above. Use the single natural
left-derived counit for tensor pullback along h. Its components at A and B are
invertible by flatComplexDerivedPullback. Its naturality at alpha computes the
pullback of the given square by the termwise chain map beta. Tensor pullback
is additive and preserves zero objects and isomorphisms, so the terms in degree
a - 1 and the outgoing degree-a differentials of the two pulled-back complexes
are zero, and beta.f a is invertible. Transport both complexes and beta through
the inverse of Scheme.Modules.overEquiv V to obtain P and Q on the localized
site. This equivalence preserves homology, zero objects, zero maps and isomorphisms.
Derived composition and the natural comparison with exact open restriction
identify the pulled-back given square with the restriction of Lg*f. Apply H^a
and the homology factorization of Q, obtaining eP, eQ and the displayed equation.
All comparisons are natural for the given arrow. No choices of unrelated endpoint
isomorphisms replace this square. The calculation also holds on empty opens and
for zero ranks, and does not require a to be nonnegative. -/
theorem bottomFreeChain_pullback_square
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (X Z : schemeDerivedCategory T) (f : X ⟶ Z) (a : ℤ)
    (W : T.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ)
    (hAbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i))
    (hBbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i))
    (hAfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hBfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hAprev : IsZero (A.X (a - 1))) (hBprev : IsZero (B.X (a - 1)))
    (hAzero : A.d a (a + 1) = 0) (hBzero : B.d a (a + 1) = 0)
    (α : A ⟶ B) (hα : IsIso (α.f a))
    (eA : (derivedPullback W.ι).obj X ≅ DerivedCategory.Q.obj A)
    (eB : (derivedPullback W.ι).obj Z ≅ DerivedCategory.Q.obj B)
    (hsquare : (derivedPullback W.ι).map f ≫ eB.hom =
      eA.hom ≫ DerivedCategory.Q.map α)
    (T' : Scheme.{u}) (g : T' ⟶ T) (y : T') (hy : g.base y ∈ W) :
    ∃ V : T'.Opens, y ∈ V ∧
      ∃ P Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V)) ℤ,
        IsZero (P.X (a - 1)) ∧ IsZero (Q.X (a - 1)) ∧
        P.d a (a + 1) = 0 ∧ Q.d a (a + 1) = 0 ∧
        ∃ β : P ⟶ Q, IsIso (β.f a) ∧
          ∃ (eP : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
              ((derivedPullback g).obj X)).over V ≅ P.homology a)
            (eQ : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
              ((derivedPullback g).obj Z)).over V ≅ Q.homology a),
            (((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
                ((derivedPullback g).map f)).over V) ≫ eQ.hom =
                  eP.hom ≫ HomologicalComplex.homologyMap β a := by
  let V := g ⁻¹ᵁ W
  let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
    (Modules.overEquiv V).inverse
  obtain ⟨hF, eP, eQ, he⟩ := bottomFreeChain_pullback_comparison
    T X Z f a W A B hAbounded hBbounded hAfree hBfree α eA eB hsquare T' g
  let := hF
  let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A
  let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
  let β := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α
  refine ⟨V, hy, P, Q, ?_, ?_, ?_, ?_, β, ?_, eP, eQ, he⟩
  · exact Functor.map_isZero F hAprev
  · exact Functor.map_isZero F hBprev
  · change F.map (A.d a (a + 1)) = 0
    rw [hAzero, F.map_zero]
  · change F.map (B.d a (a + 1)) = 0
    rw [hBzero, F.map_zero]
  · change IsIso (F.map (α.f a))
    have := hα
    infer_instance


end AlgebraicGeometry.Scheme
