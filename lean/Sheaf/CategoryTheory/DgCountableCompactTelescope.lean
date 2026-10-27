/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import WeilConjectures.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.Data.Countable.Defs
import Sheaf.CategoryTheory.DgCountableSubalgebra
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit

/-!
# Countable cohomology DG modules are telescopes of compact objects

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, implication (2) to (1);
derived.tex, Tags 090Z and 0CRH, for the compatible telescope legs
(blueprint: lem-sfb-dg-countable-compact-telescope).

The localization has the same objects as the category of DG modules. The inverse
of `Localization.Construction.objEquiv` retrieves that actual underlying object,
so the countability hypothesis uses its ordinary cohomology groups. This imposes
no choice of a resolution and no boundedness or countability of the module itself.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- Countable cohomology over a DG algebra with countable cohomology gives a
sequential compact telescope with its specified compatible maps to the object.
The two `Sigma.desc` maps have components respectively the transition followed
by the next coprojection, and the specified map to `M`. Thus the triangle has
exactly the `1-s` and `b` legs of the sequential homotopy-colimit convention.

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, implication (2) to (1);
derived.tex, Tags 090Z and 0CRH
(blueprint: lem-sfb-dg-countable-compact-telescope).

Proof:
1. By lem-sfb-dg-countable-subalgebra choose a countable DG subalgebra A_0
quasi-isomorphic to A. Lem-sfb-dg-qis-restriction-equivalence gives the exact
restriction equivalence R with exact left-adjoint quasi-inverse L and counit epsilon.
2. Restriction leaves the underlying complex and its countable cohomology unchanged.
Apply lem-sfb-dg-countable-semi-free-resolution to a representative N of R(M),
obtaining a quasi-isomorphism P to N and a countable homogeneous basis with
natural-number heights and differentials supported at smaller heights.
3. Exhaust the basis by increasing finite sets and close each under differential
supports. The closure is finite by induction on the maximum height. The spans C_m
are nested DG submodules with union P, since Leibniz keeps their spans stable.
Their height filtrations have finite sums of shifts of A_0 as successive quotients.
This also handles a finite or empty basis.
4. Lem-sfb-dg-finite-cell-compact makes the images E_m of C_m compact.
Lem-sfb-dg-sequential-colimit-triangle supplies their telescope with third object P
and the actual inclusion legs. Compose with P to N to R(M) in the derived category.
The resulting compatible legs c_m give the triangle with third object R(M).
5. Both directions of the equivalence preserve small coproducts by their Hom
bijections and the coproduct universal property. The same bijections and
compactness of E_m show that Q_m = L(E_m) is compact, using def-pc-compact-object.
6. Apply lem-kun-functor-preserves-hocolim to L and the triangle in step 4.
Set u_m = L(v_m) and b_m = L(c_m) followed by epsilon_M. Naturality and compatibility
of c_m give u_m followed by b_(m+1) equal to b_m. The coproduct comparison identifies
the first arrow with 1-s by checking coprojections. Identify L(R(M)) with M by
epsilon_M; the second arrow has components b_m. This is precisely the required
triangle and the convention of def-kun-truncations. -/
theorem exists_compact_telescope_of_countable_cohomology
    (A : Algebra.{u}) [DerivedStructure A]
    (hA : ∀ i : ℤ, Countable (A.X.homology i))
    (M : Derived A)
    (hM : ∀ i : ℤ, Countable
      (((underlying A).obj
        ((Localization.Construction.objEquiv (quasiIsomorphisms A)).symm M)).homology i)) :
    ∃ (Qm : ℕ → Derived A) (um : ∀ m : ℕ, Qm m ⟶ Qm (m + 1))
      (bm : ∀ m : ℕ, Qm m ⟶ M),
      (∀ m : ℕ, IsCompactObject.{u} (Qm m)) ∧
      (∀ m : ℕ, um m ≫ bm (m + 1) = bm m) ∧
      ∃ δ : M ⟶ (∐ Qm)⟦(1 : ℤ)⟧,
        Triangle.mk
          (𝟙 (∐ Qm) - Sigma.desc (fun m : ℕ ↦ um m ≫ Sigma.ι Qm (m + 1)))
          (Sigma.desc bm) δ ∈ distTriang (Derived A) := by
  sorry

end CategoryTheory.DgAlgebra
