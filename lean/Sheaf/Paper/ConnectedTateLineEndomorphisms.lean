/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Scalar endomorphisms of a shifted Tate line

Source: blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-dualizing, affine-space Tate rank-one reduction; extracted scalar argument
(blueprint: lem-coef-connected-tate-line-endomorphisms).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The tensor-power finite Tate sheaf, placed in degree zero and shifted by `d`.
Source: blueprint, lem-coef-finite-dualizing, affine-space Tate rank-one reduction
(blueprint: lem-coef-connected-tate-line-endomorphisms).
The existing `finiteEtaleTateSheaf` restricts on nonnegative integers to the tensor powers;
no new Tate-twist construction is introduced here. -/
def shiftedFiniteEtaleTateLine (B : Type (u + 1)) [CommRing B] (N : ℕ)
    (Y : Scheme.{u}) (hB : (N : B) = 0) (r : ℕ) (d : ℤ) :
    Etale.DerivedCategoryModule B Y :=
  (shiftFunctor (Etale.DerivedCategoryModule B Y) d).obj
    ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf B N Y hB (r : ℤ)))

/-- Scalars give every endomorphism of the shifted Tate line, uniquely. A `B`-linear
functor carrying this line to the constant coefficient complex detects its invertible
endomorphisms.

Source: blueprint, lem-coef-finite-dualizing, affine-space Tate rank-one reduction,
extracted agent-written scalar argument; Stacks, Tags 06XS and 03P5
(blueprint: lem-coef-connected-tate-line-endomorphisms).

Proof:
1. By lem-asd-etale-finite-twist-pullback the Tate sheaf is locally free of rank one.
Cancel the shifts using def-weil-abstract-derived-category; shift linearity is supplied by
lem-weil-linear-abelian-derived-category. By lem-weil-pbc-derived-single-fully-faithful its
unshifted derived endomorphisms are precisely module-sheaf endomorphisms. In local bases
write f(e_i) = a_i e_i. On overlaps e_j = u_ij e_i with u_ij a unit, so linearity and
commutativity give a_j u_ij = u_ij a_i and hence a_j = a_i. Glue by the sheaf axiom. This
identifies endomorphisms with sections of B_Y, respecting addition, multiplication and one.
2. Apply lem-weil-pbc-constant-sheaf-sections-connected to the additive group of B: because
Y is nonempty and connected, its constant sections are exactly B, via the constant-section
map. The local calculation identifies that map with b mapping to b times the identity.
3. Write v = b times the identity. By def-weil-linear-category and the linearity of G,
G(v) is the same scalar on G(L). Transport along the given isomorphism to the coefficient
complex on Spec k. Apply the first two steps to Spec k. An inverse to this scalar map
corresponds to c in B, with bc = cb = 1, so b is a unit.
4. The endomorphism c times the identity on L is a two-sided inverse to v. Thus G detects
invertibility on these endomorphisms. The argument also applies to B = 0 and r = 0. -/
theorem connected_tate_line_endomorphisms
    (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : 0 < N) (hInvertible : IsUnit (N : k))
    (B : Type (u + 1)) [CommRing B] (hB : (N : B) = 0)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] [ConnectedSpace Y] (r : ℕ) (d : ℤ) :
    Function.Bijective
      (fun b : B => b • 𝟙 (shiftedFiniteEtaleTateLine B N Y hB r d)) ∧
    (∀ (G : Etale.DerivedCategoryModule B Y ⥤
        Etale.DerivedCategoryModule B (Spec (.of k))) [G.Linear B],
      Nonempty (G.obj (shiftedFiniteEtaleTateLine B N Y hB r d) ≅
        Etale.constantComplex B (Spec (.of k))) →
      ∀ v : shiftedFiniteEtaleTateLine B N Y hB r d ⟶
          shiftedFiniteEtaleTateLine B N Y hB r d,
        IsIso (G.map v) → IsIso v) := by
  sorry

end AlgebraicGeometry.Scheme
