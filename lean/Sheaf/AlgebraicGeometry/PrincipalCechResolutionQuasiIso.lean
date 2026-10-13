module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
import Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections

/-! # Principal Čech totalization of a quasi-coherent resolution

Source: Stacks, Tags 08D2 and 08C2
(blueprint: lem-sc-principal-cech-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a finite principal-open cover, totalization takes a K-injective resolution
of a termwise quasi-coherent complex to a quasi-isomorphism. The resolution's
terms need not be quasi-coherent.
Source: Stacks, Tags 08D2 and 08C2
(blueprint: lem-sc-principal-cech-resolution-quasi-iso).

Proof:
1. Restrict F and its resolution i to each nonempty principal intersection D(g_J).
Restriction preserves quasi-isomorphisms and K-injectivity. The terms, cokernels
of differentials, and cohomology sheaves of F restricted to this affine open are
quasi-coherent, so their higher cohomology vanishes. The unbounded affine acyclic
section comparison therefore says that Γ(D(g_J), i) is a quasi-isomorphism.
This is the intersectionwise comparison used in the proof of
lem-sc-qcoh-complex-alternating-cech-derived-sections (Tags 08D2 and 08C2).
2. Filter the two principal Čech totals by subset cardinality, equivalently by
Čech degree. The map induced by i respects the filtration; its graded map in
row p is the finite product over |J|=p+1 of those section quasi-isomorphisms,
shifted by p. Finite products and shifts preserve quasi-isomorphisms.
3. There are only rows 0 through r-1. Induction on this finite filtration, using
the long exact cohomology sequences, proves that the total map is a
quasi-isomorphism. This argument makes no boundedness assumption in the vertical
direction. For r=0 both totals are zero. For r=1 it is the affine section
comparison alone. The zero complex case is included by the same argument. -/
theorem principalCech_resolution_quasiIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso ((principalCechFunctor r f).map i) := by
  sorry

end AlgebraicGeometry
