/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-! # The canonical subset decomposition of the trivial Koszul complex -/

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

local instance : HasFiniteBiproducts (CochainComplex (Modules R) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A zero-differential trivial Koszul model is the sum of its canonical subset singles.
The empty summand is the prescribed cup unit, and the rank-zero inverse has the
specified unique coordinate.

Source: step 1 of `lem-sfb-lattice-ordered-koszul-products`, using the Koszul
coordinate and cup-unit formulas.
(blueprint: lem-sfb-koszul-trivial-subset-decomposition).

Proof: for each I construct the map from S_|I| whose only component is the I-th
biproduct inclusion followed by K.coordinates.inv. It is a chain map because all
differentials vanish. The sum of these maps is an isomorphism: in degree a,
only subsets of cardinality a contribute, and the coordinate projections give
an inverse. Both composites are identity by the biproduct matrix identities.
At degree zero every subset is empty; the cup unit's prescribed coordinate is
the identity of the regular module, so it equals the empty inclusion by single
complex extensionality. If r=0, every nonempty-degree term is zero and the sole
remaining coordinate is the empty subset. Projecting to that coordinate gives
the rank-zero inverse, and its composite with the empty inclusion is identity.
This construction works also for r=0 and for the zero ring. -/
theorem trivial_subset_decomposition (r : ℕ) (K : KoszulModel R r)
    (c : Comparison R r K)
    (cup : TriangulatedCup.CupComparison R r K c (Mon.trivial (Equivariant R r)))
    (hd : ∀ a b : ℤ, (K.functor.obj (𝟙_ (Equivariant R r))).d a b = 0) :
    ∃ (incl : ∀ I : Finset (Fin r), S I.card ⟶ K.functor.obj (𝟙_ (Equivariant R r)))
      (decomposition :
        (⨁ fun I : Finset (Fin r) ↦ S I.card) ≅ K.functor.obj (𝟙_ (Equivariant R r)))
      (rank_zero_iso : r = 0 → (K.functor.obj (𝟙_ (Equivariant R r)) ≅ S 0)),
      (∀ (I : Finset (Fin r)) (J : Subsets r (I.card : ℤ)),
    (HomologicalComplex.singleObjXSelf (.up ℤ) (I.card : ℤ) (𝟙_ (Modules R))).inv ≫
      (incl I).f (I.card : ℤ) ≫ (K.coordinates (𝟙_ (Equivariant R r)) I.card).hom ≫
      biproduct.π _ J = if I = J.val then 𝟙 _ else 0) ∧
      (∀ I : Finset (Fin r),
    biproduct.ι (fun I : Finset (Fin r) ↦ S I.card) I ≫ decomposition.hom = incl I) ∧
      (incl ∅ = cup.unit) ∧
      (∀ h : r = 0,
    (rank_zero_iso h).hom.f 0 = (K.coordinates (𝟙_ (Equivariant R r)) 0).hom ≫
      biproduct.π _ ⟨∅, rfl⟩ ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).inv) ∧
      (∀ h : r = 0, incl ∅ ≫ (rank_zero_iso h).hom = 𝟙 (S 0)) := by sorry

end Profinite.DiscreteLattice.OrderedKoszul
