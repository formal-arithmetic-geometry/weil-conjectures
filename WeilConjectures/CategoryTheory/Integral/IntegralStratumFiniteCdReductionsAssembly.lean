/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension

/-!
# Hom bound for a bounded classical torsion complex on an integral stratum

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the dual-tensor and bounded-heart steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- A finite local integral model has bounded Hom into any bounded complex with
classical locally ell-power torsion cohomology. This assertion does not involve
an ambient scheme, a closed support, a reduction functor, or a constructible target.

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
dual-tensor and bounded-heart steps; Stacks Tag 08JJ.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions-assembly).

Proof: transport the continuous integral coefficient to integralCoefficientRing.
Since cd_ell(S) <= s, choose its finite natural value s0 <= s. The finite local
model makes L[0] perfect, including its torsion summands, by the length-one DVR
resolutions. Put D=RHom(L[0],A[0]). The integral dual-torsion heart-sections theorem
places RΓ(D tensor F[0]) in [0,s0+1] for every classical local torsion module F;
use the equivalence of local torsion with the filtered prime-power-kernel union.
A K-flat representative of D makes tensoring triangulated, and derived sections
are triangulated. Bounded-heart devissage along the truncation triangles of K
therefore puts RΓ(D tensor K) in [a,b+s0+1]. The perfect-dual tensor adjunction
and the derived internal-Hom sections comparison identify Hom(L[0],K[r]) with
its r-th cohomology. This is zero when r>b+s+1, hence that Hom type is a
subsingleton. The zero module, zero complex and empty scheme satisfy the same
argument; no uniform prime-power annihilator is required. -/
theorem integralStratumFiniteCdReductions_assembly
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (r : ℤ) (hr : b + (s : ℤ) + 1 < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶ K⟦r⟧) := by sorry

end CategoryTheory
