module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.Finiteness
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Monomorphisms from groups of multiplicative type into affine groups

Source: Conrad, Reductive group schemes, Appendix B, Definition B.1.1 and Lemma B.1.3,
printed pp.280--282 (blueprint: lem-sfb-affine-multiplicative-type-monomorphism-closed).

The fppf splitting cover is refined by affine opens so that the existing ring-diagonalizable
construction supplies the split models. All identifications preserve the group operations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pointwise monic homomorphism from a finitely presented group of multiplicative type
into an affine finitely presented group is a closed immersion.

Source: Conrad, Reductive group schemes, Appendix B, Definition B.1.1 and Lemma B.1.3,
printed pp.280--282 (blueprint: lem-sfb-affine-multiplicative-type-monomorphism-closed).

Proof: refine the splitting fppf cover by affine opens. The covering calculus and
lem-trf-fppf-covering-base-change give a covering of G; it is fpqc by
lem-trf-fppf-covering-is-fpqc. By lem-pc-fpqc-descend-closed-immersion it suffices to work
with H = Spec R[M] and G = Spec A. Right translation by H gives a coaction on A, hence
an M-grading by lem-sfb-group-algebra-coaction-grading. If c : A → R is the identity
section, the coordinate map sends homogeneous a of degree m to c(a)e_m.
In A[M] put I = (a(t^m - 1) : a homogeneous of degree m) and J = (t^m - 1 : m in M).
In C = A[M]/I the universal point h of H fixes the universal point x of G under right
translation. Cancellation gives j(h) = 1, and injectivity on Spec C points gives h = 1.
Thus J is contained in I; the reverse inclusion is immediate. Apply
lem-sfb-graded-stabilizer-strong-products: for each m, finitely many a_i of degree m and
b_i of degree -m satisfy sum a_i*b_i = 1. Evaluation at the identity shows that
sum c(b_i)*a_i maps to e_m. Consequently A → R[M] is surjective, including when R is the
zero ring. The affine criterion for closed immersions and fpqc descent prove the result.
No step requires M to be torsion-free or H to be smooth. -/
theorem affine_multiplicativeType_monomorphism_closed
    {S : Scheme.{u}} (H G : Grp (Over S)) [IsCommMonObj H.X]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom] [QuasiSeparated H.X.hom]
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (hH : ∃ (I : Type u) (R : I → CommRingCat.{u})
      (p : ∀ i : I, Spec (R i) ⟶ S) (M : I → AddCommGrpCat.{u}),
      (∀ i : I, AddGroup.FG (M i)) ∧
      Presieve.ofArrows (fun i : I ↦ Spec (R i)) p ∈ Scheme.fppfPrecoverage S ∧
      ∀ i : I, Nonempty (((Over.pullback (p i)).mapGrp.obj H) ≅
        ringDiagonalizableGroup (R i) (M i)))
    (j : H ⟶ G)
    (hj : ∀ T : Over S, Function.Injective (fun x : T ⟶ H.X ↦ x ≫ j.hom.hom)) :
    IsClosedImmersion j.hom.hom.left := by
  sorry

end AlgebraicGeometry
