/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalMultiplicationData

/-! # Cubical roof denominators and tensor representatives

Source: direct-images paragraph (3), lattice expansion, steps 4--5
(blueprint: lem-sfb-lattice-cubical-tensor-representatives).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice.CubicalMultiplication

variable (R : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ)
    (J : CubicalEvaluation.DiscreteComparison R r)
    (C : CubicalEvaluation.CubicalModel R r)
    (K : KoszulModel R.toMon r) (B : DerivedCup.Algebra R.toMon r)

/-- The counit yields a common denominator, and contraction gives the quasi-isomorphisms
and the ordinary K-flat tensor representatives. Localization cancellation is separate.
Source: cubical roof proof steps 4--5
(blueprint: lem-sfb-lattice-cubical-tensor-representatives).

Proof: the double counit, naturality of the middle interchange and the unitors give
comparison followed by b equals a. Forget action. The recorded cubical contraction
satisfies dh+hd=1-e, where e=s epsilon and epsilon s=1. On L tensor L use
H(l tensor l')=h(l) tensor l'+(-1)^|l| e(l) tensor h(l'). Expanding gives
dH+Hd=1-e tensor e. On X tensor (L tensor L) use (-1)^|x| x tensor H. Conjugate
by the middle interchange to obtain a homotopy inverse for b. The single-factor
contraction gives the homotopy inverse of a. The forgetful functor is exact and
conservative, so these are equivariant quasi-isomorphisms; s and h need no equivariance.
The flat twisted pairing theorem makes the trivial Koszul complex K-flat with flat
terms. The cubical model is a bounded complex of free internal modules, hence K-flat;
its underlying contraction gives the same acyclic-tensor test. Composing tensor
functors proves K-flatness of every displayed tensor word. The canonical localization
tensor comparison on two K-flat representatives is invertible, as in the ordinary
K-flat tensor comparison used by the flat pairing theorem. This proves both predicates
without assuming multiplication compatibility or localization of the evaluation roofs.
The argument uses no nonzero coefficient or positive rank assumption. -/
theorem normalized_roof_tensor_representatives [IsCommMonObj B.X]
    (hflat : exactFunctor (Modules R.toMon) (Modules R.toMon) (tensorLeft B.X.V))
    (F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B))
    (hF : Normalized R r J C K B F) :
    F.comparison ≫ F.b = F.a ∧ QuasiIso F.a ∧ QuasiIso F.b ∧
      TensorRepresentatives R r J C K B := by sorry

end Profinite.DiscreteLattice.CubicalMultiplication
