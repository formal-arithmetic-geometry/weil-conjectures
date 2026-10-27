/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-! # The binary shuffle calculation on canonical subset singles -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Profinite.DiscreteLattice.OrderedKoszul

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

local notation "S" => (fun q : ℕ ↦
  Functor.obj (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) (q : ℤ)) (𝟙_ (Modules R)))

/-- The cup matrix on canonical single-term subset inclusions has the inversion sign.

Source: step 4 of `lem-sfb-lattice-ordered-koszul-products`, the coordinate
formula of the given triangulated cup comparison, and the finite-free coordinate
calculus (no assertion about sections of tensor sheaves is used).
(blueprint: lem-sfb-koszul-subset-shuffle-binary).

Proof: the tensor of the two single complexes is concentrated in degree |A|+|C|.
Test the composite against every target subset projection in that degree and
precompose with the inclusion of its unique input tensor summand. Substitute
the prescribed inclusion coordinates and the cup comparison's matrix formula.
The only possible summand has inputs exactly A and C. If these intersect, the
cup coordinate condition is false for every output, hence the morphism is zero.
Otherwise its sole output is A union C, with coefficient (-1)^inv(A,C).
The specified unsigned tensor coordinate identifies its regular multiplication
with mul, and the target degree equality is exactly card_union_of_disjoint.
The resulting componentwise equations imply equality by biproduct and complex
extensionality. Empty subsets give inv=0 and the same regular multiplication;
in the zero ring both sides vanish, and in characteristic two the sign is one. -/
theorem subset_shuffle_binary (r : ℕ) (K : KoszulModel R r)
    (c : Comparison R r K)
    (cup : TriangulatedCup.CupComparison R r K c (Mon.trivial (Equivariant R r)))
    (incl : ∀ I : Finset (Fin r), S I.card ⟶ K.functor.obj (𝟙_ (Equivariant R r)))
    (mul : ∀ p q : ℕ, S p ⊗ S q ≅ S (p + q))
    (hi : ∀ (I : Finset (Fin r)) (J : Subsets r (I.card : ℤ)),
    (HomologicalComplex.singleObjXSelf (.up ℤ) (I.card : ℤ) (𝟙_ (Modules R))).inv ≫
      (incl I).f (I.card : ℤ) ≫ (K.coordinates (𝟙_ (Equivariant R r)) I.card).hom ≫
      biproduct.π _ J = if I = J.val then 𝟙 _ else 0)
    (hm : ∀ p q : ℕ,
    ((HomologicalComplex.singleObjXSelf (.up ℤ) (p : ℤ) (𝟙_ (Modules R))).inv ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (𝟙_ (Modules R))).inv) ≫
      HomologicalComplex.ιTensorObj (S p) (S q) (p : ℤ) (q : ℤ)
        ((p + q : ℕ) : ℤ) (Nat.cast_add p q).symm ≫
      (mul p q).hom.f ((p + q : ℕ) : ℤ) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) ((p + q : ℕ) : ℤ)
        (𝟙_ (Modules R))).hom = (λ_ (𝟙_ (Modules R))).hom) :
    ∀ A C : Finset (Fin r), (incl A ⊗ₘ incl C) ≫ cup.star =
    if h : Disjoint A C then
      ((-1 : ℤ) ^ ((A.product C).filter (fun ac ↦ ac.2 < ac.1)).card) •
        ((mul A.card C.card).hom ≫
          eqToHom (congrArg (S) (Finset.card_union_of_disjoint h).symm) ≫ incl (A ∪ C))
    else 0 := by sorry

end Profinite.DiscreteLattice.OrderedKoszul
