module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A strictly perfect neighbourhood has finite residue-field fibre cohomology in every degree.
Source: Stacks Project, More on Algebra, Tag 0BCD, first paragraph of the proof;
Cohomology of Sheaves, Tag 08C4 (strictly perfect complexes).
(blueprint: new-perfect-finite-residue-cohomology-finite).

Proof: Choose V, P and the given derived isomorphism from hlocal. The residue-point
morphism factors through V, so restriction followed by derived pullback identifies the
fibre of E with the derived pullback of Q(P). Each term of P is a finite-free retract,
hence flat; its boundedness makes P K-flat. Consequently ordinary termwise pullback
computes this derived pullback. The inverse image of V is the whole one-point spectrum
of the residue field. Pullback carries the finite-free retract maps to splitting maps
of the same rank. Evaluation on the whole spectrum is exact: sheaves of modules there
are modules over its global ring. Transport along GammaSpecIso is also exact. Thus
derivedFiberCohomology is isomorphic to homology of the resulting complex of
residue-field vector spaces.
Every term is a retract of a finite-dimensional vector space, so is finite-dimensional.
The cycles in degree i form a subspace of that term and the boundaries form a subspace
of the cycles. The quotient of cycles by boundaries is finite-dimensional; transfer
this property across the cohomology isomorphism. This works in every degree, including
rank-zero terms and the zero complex. -/
theorem finiteFiberCohomology
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P)) :
    ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x) := by
  sorry

end
end AlgebraicGeometry.Scheme
