/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.PointScalarSectionsExact
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# The complexes whose traces occur

Source: blueprint latest (slopmaster2-20261031),
part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-lem-finite/
sk-lem-tf-compact-trace/_section.md, node sk-lem-tf-compact-trace
(blueprint: sk-lem-tf-compact-trace).

This is the condensed-coefficient form of the compact-trace finiteness statement, for a
finite commutative `ℓ`-primary coefficient ring `A`, realized as the discrete condensed ring
`Λ ≅ C(-, A)`.  Compact support is the recorded compactification lower-shriek followed by
terminal point scalar sections, and a geometric stalk is the derived pro-étale pullback to
the geometric point followed by those same exact point sections.  The perfectness predicate
is `IsPerfectRingComplex` over the scalar ring `Γ Λ`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `X` be separated of finite type over `k = F̄_q`, let `A` be a finite commutative
`ℓ`-primary ring with `ℓ ≠ char k` and `K ∈ D_ctf(X, A)`.  Then `RΓ_c(X_proét, K)` and every
geometric stalk `K_x̄` are perfect `A`-complexes, so the traces of their endomorphisms are
defined.  The compact-support complex is formed for every compactification (the chosen
compactification of the source), and the stalk clause ranges over all algebraically closed
geometric points, using the derived pro-étale pullback before exact point scalar sections.

Source: blueprint latest, sk-lem-tf-compact-trace/_section.md, node sk-lem-tf-compact-trace
(blueprint: sk-lem-tf-compact-trace).

Proof (the three steps of the node):
1. Put `s = Spec k` and let `a_X : X → s` be the structure morphism.  Since `k` is
   algebraically closed, det-compact-trace-point-objects applies: `Ra_{X!}K ∈ D_ctf(s, A)`,
   and each `K_x̄` is bounded with finitely generated cohomology and finite Tor amplitude.
   Compact cohomology is read through scalar sections: `RΓ_c(X, K) = RΓ(s, Ra_{X!}K)`.
2. Apply det-compact-trace-perfect-at-point in this setting: by the finite-ring perfectness
   criterion (Stacks 0658; `A` is Noetherian, no regularity or field hypothesis on `A`),
   both `RΓ_c(X, K)` and every `K_x̄` are perfect `A`-complexes.
3. For either perfect complex `P` and an endomorphism `v`, the perfect-complex case of
   sk-d-trace gives `tr(v | P)` as the composite of coevaluation, `v ⊗ 1`, the symmetry and
   evaluation, an element of `End_{D(A)}(A) = A`. -/
theorem compactTrace_perfect
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)))
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    ∀ (c : Compactification X.hom),
      DerivedCategory.IsPerfectRingComplex
        ((condensedRingCompactCoefficientComplex Λ c).obj K.obj) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X.left),
        DerivedCategory.IsPerfectRingComplex
          ((CohomologyTransport.sections Λ (Spec (.of Ω))).mapDerivedCategory.obj
            ((upperStar Λ x).mapDerivedCategory.obj K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
