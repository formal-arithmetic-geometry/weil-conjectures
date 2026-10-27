module

public import Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction

/-! # A uniform bound for the algebraic-space derived quasi-coherator

Source: Stacks Project, Derived Categories of Spaces, Tag 0CSS,
lemma-boundedness-better-coherator (blueprint: lem-sfb-space-derived-coherator-bound).

Affine hypercohomology is written as the homology of termwise sections of any
K-injective representative, forgetting the section-ring action. The small model
contains representatives of every affine etale chart. The conclusion is vanishing
of cohomology sheaves, in the existing full subcategory D_QCoh.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The derived quasi-coherator has one nonnegative bound for all affine-etale
hypercohomology intervals and all unbounded input objects. The representative I and
its identification with E merely spell out the computation of H^i(U,E) required by
the node, and impose no boundedness or quasi-coherence on E.
Source: Stacks Project, Derived Categories of Spaces, Tag 0CSS
(blueprint: lem-sfb-space-derived-coherator-bound).

Proof:
1. Apply lem-sfb-space-qcqs-distinguished-square-induction to the property that one
nonnegative constant works for all intervals and all complexes. This property is
invariant under isomorphism; all smaller vertices are qcqs and admit the adjunction
of lem-sfb-space-derived-coherator-adjunction.
2. On an affine space, the identity chart is among the tests. The formula of
lem-sfb-space-affine-coherator-formula and the cohomology comparison of
lem-sfb-affine-etale-derived-module-realization show that N = 0 works, including
for the empty affine scheme.
3. In a distinguished square U,V over W, put T = U times_W V. By
lem-sfb-space-derived-etale-chart-calculus restriction is exact slice restriction.
It preserves K-injectives: use the exact left adjoint of
lem-weil-pbc-ringed-sheaf-slice-adjunction and def-pur-kinjective-complex to make
maps from acyclic complexes null-homotopic. Sections on a chart B over a vertex
are sections on its composite chart over W. Thus the same affine test interval
holds on U,V,T.
4. The inductive constants N_A bound Q_A = DQ_A(E restricted to A). By
lem-sfb-space-qcqs-permanence the three maps j_A are qcqs. Apply
lem-sfb-space-derived-pushforward-upper-bound to obtain c_A >= 1 with Rj_A Q_A
zero in degrees at least b+N_A+c_A. Exact restriction and the derived adjunction,
using lem-pur-exact-derived-adjunction-bounds (1), give vanishing below a.
5. The triangle of lem-sfb-space-coherator-distinguished-square-triangle and
lem-sf-derived-homology-long-exact give the segment H^(i-1)(Rj_T Q_T) to
H^i(DQ_W E) to H^i(Rj_U Q_U) direct-sum H^i(Rj_V Q_V). Put
M = max_A (N_A+c_A-1), which is nonnegative. Both ends vanish for i < a or
i > b+M+1, so N_W = M+1 works independently of a,b,E.
6. The induction proves the assertion on X. K-injective representatives exist in
SmallModules; termwise evaluation on its affine skeleton computes exactly the
stated affine hypercohomology. Every representative is allowed, and its derived
identification with E transports this computation without any boundedness assumption. -/
theorem derivedCoherator_affineHypercohomology_bound
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : ∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj),
      IsAffine U.left → IsAffine V.left → IsEtale a → IsEtale b →
        ∃ W : Over S, Nonempty (yoneda.obj W ≅ Limits.pullback a b) ∧
          CompactSpace W.left)
    (DQ : X.DerivedModules ⥤ X.DerivedQCoh)
    (adj : X.derivedQCohProperty.ι ⊣ DQ) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ (a b : ℤ), a ≤ b →
      ∀ (E : X.DerivedModules) (I : CochainComplex X.SmallModules ℤ),
        I.IsKInjective → Nonempty (DerivedCategory.Q.obj I ≅ E) →
        (∀ (U : X.SmallEtaleModel) (i : ℤ), (i < a ∨ b < i) →
          IsZero ((((SheafOfModules.toSheaf X.smallStructureRings ⋙
            sheafToPresheaf X.smallEtaleModelTopology AddCommGrpCat.{u} ⋙
            (evaluation X.SmallEtaleModelᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I).homology i)) →
        ∀ i : ℤ, (i < a ∨ b + N < i) →
          IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj
            (DQ.obj E).obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
