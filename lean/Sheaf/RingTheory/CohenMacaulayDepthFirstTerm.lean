module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.RingTheory.DepthInSES

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- The nonzero finite left term of the prescribed free sequence has depth at least `d`.
Source: Stacks Project, Algebra, Tags 00NG, 00NE and 00LX, part (3).
(blueprint: lem-weil-pbc-cm-local-free-resolution-mcm-depth).

Proof: Put `n = d-e`. Read the sequence right to left as short exact sequences
`0 → N_{j+1} → F_j → N_j → 0`, with `N_0` identified with `M` and `N_n` with
`S.obj' 1`. All syzygies are finite: each is a submodule of a finite free module
and the ring is Noetherian. A nonzero finite free module has depth at least `d`:
a regular sequence on `R` acts regularly componentwise on a finite power of `R`;
a finite basis transports this fact, so taking suprema gives depth at least
`depth R`. Linear equivalences preserve depth because they preserve regularity
and the quotient by the maximal ideal.

Induct on `j` to show that any nonzero `N_j` has depth at least `min(d,e+j)`.
The initial bound is `he`. If the three terms are nonzero, part (3) of the depth
lemma gives `depth N_{j+1} ≥ min(depth F_j, depth N_j + 1)`, hence the next bound.
If `N_j` is zero, exactness identifies `N_{j+1}` with `F_j`, giving the bound by
freeness. If `F_j` is zero, injectivity makes `N_{j+1}` zero, so there is no bound
to prove at that step. If `N_{j+1}` is zero the induction assertion is vacuous;
the next step is covered by the zero-quotient case. Thus zero intermediate terms
do not interrupt induction. At `j=n`, `e≤d` gives `min(d,e+n)=d`; the assumed
nontriviality of the left term gives the desired bound. When `n=0`, endpoint
exactness identifies the left term with `M` and `he`, with `e=d`, proves it. -/
theorem first_term_depth_ge
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d e : ℕ)
    (hcm : (d : ℕ∞) ≤ depth (R := R) R)
    (he : depth (R := R) M = (e : ℕ∞)) (hed : e ≤ d)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3))
    (hS : S.Exact) (hzero0 : IsZero (S.obj' 0))
    (hzero1 : IsZero (S.obj' (d - e + 3)))
    (hM : Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M))
    (hfree : ∀ i : Fin (d - e),
      Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
      Module.Finite R (S.obj' (i.val + 2) (by omega)))
    [Module.Finite R (S.obj' 1)] [Nontrivial (S.obj' 1)] :
    (d : ℕ∞) ≤ depth (R := R) (S.obj' 1) := by
  sorry

end IsLocalRing
