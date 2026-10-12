module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A strictly perfect neighbourhood of a point gives finite-dimensional derived fibre
cohomology, supported in a bounded interval.
Source: Stacks Project, More on Algebra, Tag 0BCD, first paragraph of the proof;
Cohomology of Sheaves, Tag 08C4 (strictly perfect complexes).
(blueprint: lem-sc-perfect-finite-free-residue-model-data).

Proof: Unpack the given neighbourhood and its strictly perfect representative P. Its terms
are direct summands of finite free sheaves, hence flat. Since P is bounded, it is K-flat,
so termwise pullback to Spec kappa(x) computes the derived fibre of E. Pullback preserves
zero terms and the splitting maps exhibiting each term as a direct summand of a finite
free sheaf. On the one-point spectrum of a field, evaluation on the whole space identifies
these sheaves with finite-dimensional vector spaces; it is exact. Transport scalars through
GammaSpecIso, as in derivedFiberCohomology. Thus that vector space is the degree-i homology
of a bounded complex of finite-dimensional kappa(x)-vector spaces. Cycles are subspaces of
finite-dimensional terms, and homology is a quotient of cycles, so each homology is finite.
Outside the bounds of P the term is zero, so its homology is zero and its finrank is zero.
The same bounds therefore establish the support assertion for derivedFiberBetti. -/
theorem finiteFiberData
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
    (∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) ∧
      ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0 := by
  sorry

end
end AlgebraicGeometry.Scheme
