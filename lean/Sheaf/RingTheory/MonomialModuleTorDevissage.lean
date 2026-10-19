/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.RingTheory.MonomialSubsetSpan
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.TorDimensionShiftNatural
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry

/-!
# Monomial ideal tests and higher Tor vanishing

Source: the algebraic monomial filtration used in ILO, Travaux de Gabber,
Exposé X 1.3(vii), printed p.140, and Lemma 1.5, printed p.142;
Stacks Project, Tags 00LY, 00M0, 00M3, 0BNF
(blueprint: lem-per-monomial-module-tor-devissage).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AddMonoidAlgebra

/-- Monomial ideal Tor-one tests imply every positive-degree Tor vanishing for
quotients of stable monomial subsets. The quotient uses the inverse image of the
smaller span under the larger span's inclusion, so it is literally `Z[T]/Z[U]`
when `U ⊆ T`. The `ULift`s place both arguments in one module category without
identifying the monoid, group, and module universes. Scalars are transported
along the canonical ring equivalence from the lifted ring to `Z[Q]`.
Source: ILO Exposé X 1.3(vii), p.140, and Lemma 1.5, p.142; agent algebra lemma
using Stacks Tags 00LY, 00M0, 00M3, 0BNF
(blueprint: lem-per-monomial-module-tor-devissage).

Proof (the eight steps of the node):
1. For every module N satisfying the monomial ideal tests, fix a projective
resolution P of N. Write C(W) for P tensor W in cochain degrees -j. Its H^-1 is
Tor_1(N,W), by def-weil-pbc-tor-modules.
2. Projective terms are flat (lem-weil-pbc-projective-module-flat).
Lem-weil-pbc-flat-tensor-exact makes C send short exact sequences to degreewise
short exact sequences. The full homology sequence
(lem-weil-pbc-complex-ses-homology-long-exact) makes Tor_1 vanishing extension closed.
3. Lem-weil-pbc-tensor-commutes-with-colimits identifies C of a directed colimit
with its termwise colimit. Filtered module colimits are computed on abelian groups,
with action d[w] = [dw]. Applying
lem-weil-pbc-filtered-colimit-abelian-groups-exact to the kernel, image and
image-to-kernel quotient sequences identifies H^-1 with the colimit of H^-1.
Thus directed colimits preserve the degree-one vanishing.
4. For a finite E in T minus U, enumerate E as t_1,...,t_r and set
T_0 = U, T_j = T_(j-1) union (t_j + h(Q)). The successive quotients in
Z[T_j]/Z[U] are D/Z[I_j], where I_j = {q | t_j + h(q) belongs to T_(j-1)}.
Stability makes I_j a monoid ideal. The map z^q to [t_j + h(q)] is onto;
injectivity of h and cancellation make its surviving basis values distinct,
so its kernel is exactly Z[I_j], also for the empty and full ideals.
5. Induct along this finite filtration using steps 2 and 4. The finite E form a
nonempty directed set under union, and their modules exhaust V because every
element has finite support. Step 3 gives Tor_1(N,V) = 0 for every tested N.
6. Apply step 5 to T = h(I), U empty to obtain Tor_1(N,Z[I]) = 0. The sequence
0 -> Z[I] -> D -> D/Z[I] -> 0, tor symmetry (lem-weil-pbc-tor-symmetry), and
lem-sc-p1-tor-dimension-shift-natural at degree 1 give Tor_2(N,D/Z[I]) = 0.
7. For a free presentation 0 -> K -> F -> N -> 0, dimension shifting now shows
that K also satisfies the ideal tests. Iterate the explicit presentations whose
free basis is indexed by all elements of the preceding kernel, starting at M.
8. Repeated dimension shifts identify Tor_i(M,V) with Tor_1(K_(i-1),V).
Step 7 supplies the tests for that syzygy, so step 5 makes this zero. For i = 1
no shift is needed. Empty U, empty T and U = T are included throughout.
-/
theorem monomialModule_tor_vanishes
    {Q : Type u} [AddCommMonoid Q] {G : Type v} [AddCommGroup G]
    (h : Q →+ G) (_hh : Function.Injective h)
    (M : Type w) [AddCommGroup M] [Module (AddMonoidAlgebra ℤ Q) M]
    (_hM : ∀ (I : Set Q), (∀ q ∈ I, ∀ q' : Q, q + q' ∈ I) →
      IsZero (((Tor' (ModuleCat.{max u v w}
        (ULift.{max u v w} (AddMonoidAlgebra ℤ Q))) 1).obj
          (ModuleCat.of (ULift.{max u v w} (AddMonoidAlgebra ℤ Q)) (ULift.{max u v w} M))).obj
        (ModuleCat.of (ULift.{max u v w} (AddMonoidAlgebra ℤ Q))
          (ULift.{max u v w} (AddMonoidAlgebra ℤ Q ⧸
            Ideal.span ((fun q : Q ↦ single q (1 : ℤ)) '' I))))))
    (U T : Set G) (_hUT : U ⊆ T)
    (_hT : ∀ t ∈ T, ∀ q : Q, t + h q ∈ T)
    (_hU : ∀ t ∈ U, ∀ q : Q, t + h q ∈ U)
    (i : ℕ) (_hi : 0 < i) :
    IsZero (((Tor' (ModuleCat.{max u v w}
      (ULift.{max u v w} (AddMonoidAlgebra ℤ Q))) i).obj
        (ModuleCat.of (ULift.{max u v w} (AddMonoidAlgebra ℤ Q)) (ULift.{max u v w} M))).obj
      (ModuleCat.of (ULift.{max u v w} (AddMonoidAlgebra ℤ Q))
        (ULift.{max u v w} ((monomialSubsetSpan h T) ⧸
          (monomialSubsetSpan h U).comap (monomialSubsetSpan h T).subtype)))) := by
  sorry

end AddMonoidAlgebra
