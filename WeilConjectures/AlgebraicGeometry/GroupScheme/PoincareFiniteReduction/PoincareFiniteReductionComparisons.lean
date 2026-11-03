/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.PoincareFiniteReduction.PoincareFiniteReductionData

/-! # Finite Poincare coefficient comparisons

Source: latest blueprint sec-six-functors/sk-thm-sf-package/
thm-pod-finite-reduction.proof.md (blueprint: lem-pod-finite-reduction-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.PoincareFiniteReduction

/-- The geometric part of finite coefficient reduction, in generic coordinates. -/
def CompactDualReduction {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] [IsAlgClosed k]
    (φ : condensedScalarRing A.X →+* condensedScalarRing B.X)
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (cf : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules A.X X)) : Prop :=
  ∃ σ : RestrictionSquare a k φ,
    (∀ (M : ModuleRingedComparison.internalModules B.X (Spec (.of k)))
      (x : (CohomologyTransport.sections B.X (Spec (.of k))).obj M),
      (σ.hom.app M).hom x = x) ∧
    ∃ hu : IsIso (compactComparison a k φ σ cf K),
      letI := hu
      IsIso (unitDualComparison (ModuleCat.ordinaryDerivedExtendScalars φ)
        (inv (compactComparison a k φ σ cf K))
        (Functor.OplaxMonoidal.η (ModuleCat.ordinaryDerivedExtendScalars φ)))


set_option maxHeartbeats 2000000 in
-- Matching the finite coefficient presentation needs extra elaboration work.
/-- The finite scalar comparisons and their normalized coordinates exist, and the
compact-support comparison and its canonical dual comparison are invertible.

Source: thm-pod-finite-reduction.proof.md, paragraphs 1--2 and point-perfectness
(blueprint: lem-pod-finite-reduction-comparisons).

Proof in words. The exact point restriction square is
the identity on the underlying sections with the restricted scalar action.
Localizing it and taking the scalar-adjunction mate gives pointComparison, whose
invertibility on the bounded compact-support object is finite point reduction.
Compose with sections of the native compact-support scalar comparison to obtain u.
Point perfectness makes Cn perfect over its scalar ring. Its scalar-dual comparison
is therefore invertible, as is precomposition by the inverse of u; their composite
is the displayed unitDualComparison. This uses no flatness of the quotient ring.
-/
theorem finiteReduction_comparisons
    (P : CondensedPoincareDualityConventions.{u})
    (n m : ℕ) (h : m ≤ n)
    (K : ConstantModelConstructibleFiniteTor ((coefficient P n).obj P.ell) P.X)
    (hK : IsPerfectOnCoefficientSite ((coefficient P n).obj P.ell) P.X K.obj) :
    letI : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
    CompactDualReduction (change P h) P.datum.k (scalarMap P h)
      P.compactification K.obj := by
  sorry

end WeilConjectures.PoincareFiniteReduction
