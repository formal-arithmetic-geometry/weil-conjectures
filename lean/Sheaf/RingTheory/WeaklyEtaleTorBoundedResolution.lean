module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.FlatTorIdealCriterion

/-! # Bounded flat resolutions from uniform Tor vanishing

Source: Stacks Project, More on Algebra, Tag 066F, and Algebra, Tag 00M5.
(blueprint: lem-weil-pbc-weak-etale-tor-bounded-resolution).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat.WeaklyEtaleTorAux
noncomputable section

/-- Uniform Tor vanishing gives a flat resolution truncated at the bound.
Source: Stacks Project, More on Algebra, Tag 066F (the converse Tor-dimension
criterion), with the flatness criterion in Algebra, Tag 00M5.
(blueprint: lem-weil-pbc-weak-etale-tor-bounded-resolution).

Proof: Fix M and construct a free resolution P of M as follows. Take P_0 free on
its underlying set and send [m] to m. Take P_(n+1) free on the underlying set of
the kernel of the preceding surjection, mapping [x] to x; compose with the kernel
inclusion to define the differential. Each differential has image the next kernel,
so this augmented complex is exact. Put K_0 = M and, for d > 0, put K_d equal to
the kernel of P_(d-1) -> P_(d-2), where P_(-1) = M and the map at zero is the
augmentation. The tail with degree-zero term P_d is a free resolution of K_d.
For every ideal I, the three terms and two differentials that compute degree-one
homology of this tail tensored with R/I are exactly those computing degree d+1
homology of P tensored with R/I. Hence Tor_1(K_d,R/I) is isomorphic to
Tor_(d+1)(M,R/I), which vanishes by hTor. The flat Tor ideal criterion makes K_d
flat. For d > 0, set F_d = K_d, F_j = P_j for j < d, and F_j = 0 for j > d;
use the kernel inclusion for the differential out of F_d and the differentials of
P below it. The kernel-image equalities give exactness in positive degrees and
cokernel M at zero, so the inherited augmentation to M[0] is a quasi-isomorphism.
Every lower P_j is free and therefore flat, K_d is flat, and zero terms are flat.
For d = 0, the same Tor criterion makes M flat; take F = M[0] and the identity
augmentation. The zero ring and the zero module satisfy these constructions too;
no finiteness or Noetherian hypothesis is used. -/
theorem flatResolution_of_tor_vanishing
    (R : Type u) [CommRing R] (d : ℕ)
    (hTor : ∀ M N : ModuleCat.{u} R, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} R) j).obj M).obj N)) :
    ∀ M : ModuleCat.{u} R,
      ∃ (F : ChainComplex (ModuleCat.{u} R) ℕ)
        (ε : F ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M),
        QuasiIso ε ∧ (∀ j : ℕ, Module.Flat R (F.X j)) ∧
          (∀ j : ℕ, d < j → IsZero (F.X j)) := by
  sorry

end
end ModuleCat.WeaklyEtaleTorAux
