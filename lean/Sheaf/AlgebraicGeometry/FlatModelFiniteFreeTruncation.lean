module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero cokernel of the canonical quotient truncation is finite free near t.
Source: Stacks Project, Tags 0653 and 00NX.
Proof: choose an affine neighbourhood of t inside U. The cokernel of Q.d (-1) 0
is quasi-coherent and finitely presented, because both terms are finite free.
At every stalk, the bounded flat complex C has Tor amplitude [0,d]. The bounded-above
free complex Q is K-flat, so its quasi-isomorphism to C gives it the same Tor amplitude.
Tag 0653 makes the degree-zero cokernel flat at each stalk. Over the chosen affine,
the corresponding finitely presented flat module is finite projective. Tag 00NX gives
an open neighbourhood of t on which it is finite free. Restriction is exact, so this
restricted cokernel is the cokernel of the restricted differential. The degree-zero
term of Mathlib's truncGE 0 is canonically isomorphic to that cokernel; transport the
finite-free isomorphism along it. Only the open neighbourhood and rank are existential;
the complex itself is the explicit canonical truncation, not an arbitrary witness.
(blueprint: lem-pc-flat-model-finite-free-truncation-zero). -/
theorem exists_local_finiteFree_truncation_zero {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U), t ∈ V ∧ ∃ r : ℕ,
      Nonempty ((CochainComplex.truncGE
        (((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj Q) 0).X 0 ≅
          SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
