module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Finite-diagonal Hom totalization of exact columns is acyclic

Source: Stacks Project, Tag 0GM8 via Tag 0GM7; the explicit proof is the
agent-written calculation described below (blueprint: lem-sc-bounded-hom-exact-columns). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Exact internal-Hom columns imply exactness of the total Hom when its diagonals
are finite. The hypothesis concerns only the differentials of the second complex;
no freeness or acyclicity hypothesis is imposed on either input.
Source: Stacks Project, cohomology.tex, Tag 0GM8, case (2), descending Hom calculation.
(blueprint: lem-sc-bounded-hom-exact-columns)

Proof: fix a degree n and bounds N for E and M for A. A total cocycle has components
only for M-n ≤ p ≤ N. Set the degree n-1 primitive to zero above N and descend in p.
If the equation at p+1 has been solved, subtract the signed precomposition of that
primitive with d_E from the p-th cocycle component. The cocycle equation, the equation
at p+1 and d_E squared equal to zero show that this obstruction lies in the kernel
of postcomposition with d_A. Exactness of the internal-Hom column at q=p+n gives a
local lift along d_A from degree q-1. Perform only the finitely many lifts with
M-n+1 ≤ p ≤ N, taking a common refinement of their coverings. At p=M-n the
column's incoming object is zero, so exactness forces the remaining obstruction to
be zero. Below that degree both cocycle and primitive components vanish. Thus on
the resulting covering the total differential of the primitive is the given cocycle.
The local exactness criterion for module sheaves gives exactness in degree n; n was
arbitrary. This uses the product and signed differential characterization of
homComplex_exists, and is valid even if the interval of possible components is empty. -/
theorem acyclic_homComplex_of_bounded_exact_columns
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (N M : ℤ)
    (hE : ∀ p : ℤ, N < p → IsZero (E.X p))
    (hA : ∀ q : ℤ, q < M → IsZero (A.X q))
    (hcolumns : ∀ p q : ℤ,
      ∃ hz : SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).f ≫
          SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).f)
          (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).g) hz).Exact) :
    (CategoryTheory.homComplex E A).Acyclic := by
  sorry

end CochainComplex
