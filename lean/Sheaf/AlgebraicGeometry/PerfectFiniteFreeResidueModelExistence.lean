module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.Algebra.Homology.AffinePerfectColimitDescent
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.RingTheory.MinimalFreeModel

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Spread a minimal finite free model from the local ring of a strictly perfect
neighbourhood, using the already known finite residue cohomology and its bounded support.
Source: Stacks Project, More on Algebra, Tags 0BCD, 0BCC, 0BC7; Derived Categories of
Schemes, Tags 08EB and 09RE.
(blueprint: lem-sc-perfect-finite-free-residue-model-existence).

Proof: Unpack the strictly perfect neighbourhood V and restrict it to an affine open
W = Spec A containing x. The bounded strictly perfect complex has quasi-coherent terms
(each is a summand of a finite free sheaf). The affine correspondence identifies it with
a bounded complex C of finite projective A-modules. Let p be the prime corresponding to x.
Localize C at p. Its terms are finite projective over the local ring A_p, hence finite
free. It is consequently pseudo-coherent. Termwise scalar extension computes its derived
residue fibre, since C is bounded and flat, and its homology identifies with
derivedFiberCohomology X E i x. Use hfin and the definition of derivedFiberBetti to supply
the finite residue cohomology and rank hypotheses of exists_unique_minimalFreeModel
(Tag 0BCC). The upper bound in hbound supplies its remaining hypothesis. This gives a
bounded above finite free complex F representing C_p with terms of ranks d_i. The lower
bound in hbound makes the remaining terms zero too, so F is bounded.

Present A_p as the filtered colimit of principal localizations A_f for f outside p
(Tag 00CM). Descend F as a bounded finite projective complex Q at one such stage by
exists_finite_projective_model_of_directed_colimit (Tag 0BC7). Its derived isomorphism
with C_p and the inverse descend by affine_perfect_hom_colimit (Tag 09RE), applied in
both orders. Apply the injectivity clause of that same theorem to descend both inverse
identities after further localization. Thus Q and C become isomorphic in the derived
category on a principal neighbourhood of p. For each of the finitely many possibly
nonzero terms of Q, exists_standardFreeCover_of_finite_projective gives a principal free cover.
Select one member containing p and intersect these finitely many principal opens. On
this affine neighbourhood all terms are free. Their ranks equal d_i by localization at
p and invariant basis number over the nonzero ring A_p. Outside the bounds use the zero
module, which is free of rank zero. Sheafify Q and the descended isomorphism and transport
along the affine-open identification. This produces U, its bounded complex K with terms
isomorphic to the displayed free sheaves, and the required derived isomorphism. -/
theorem finiteFreeModel_of_fiberData
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
          DerivedCategory.Q.obj P))
    (hfin : ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x))
    (hbound : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin (derivedFiberBetti X E i x))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj K) := by
  sorry

end
end AlgebraicGeometry.Scheme
