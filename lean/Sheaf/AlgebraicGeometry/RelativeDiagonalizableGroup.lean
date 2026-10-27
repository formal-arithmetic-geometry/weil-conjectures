module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Diagonalizable groups over arbitrary schemes

Source: Conrad, Reductive group schemes, Appendix B.1, printed p.280
(blueprint: def-sfb-relative-diagonalizable-group).

The integral Hopf-spectrum model is pulled back along the unique map to Spec Z.
On an affine open Spec A this is Spec A[M], with its canonical Hopf operations:
A ⊗[Z] Z[M] ≃ A[M], by a ⊗ e_m ↦ a e_m. These formulas agree on overlaps,
so this construction is the diagonalizable group obtained by affine gluing.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The group D_S(M), constructed by base change of Spec Z[M] to S.
The integral model uses a universe lift of Z, which is still the initial ring.
This gives on every affine open Spec A the Hopf spectrum of A[M], hence precisely
its gluing over S, without a finite-generation or nonemptiness assumption.
Source: Conrad, Reductive group schemes, Appendix B.1, printed p.280
(blueprint: def-sfb-relative-diagonalizable-group). -/
noncomputable def relativeDiagonalizableGroup (S : Scheme.{u})
    (M : Type u) [AddCommGroup M] : Grp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.obj
    (ringDiagonalizableGroup (ULift.{u} ℤ) M)

end AlgebraicGeometry
