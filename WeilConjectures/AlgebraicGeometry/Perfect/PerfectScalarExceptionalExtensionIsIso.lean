/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectCoefficientShriekMate
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings

/-! Objectwise invertibility for the perfect scalar exceptional transpose.
Source: Stacks 0ATI, 0944 and 07A6; Steps 1-8 of the parent node
(blueprint: lem-sf-perfect-scalar-exceptional-extension-isIso).

The proof must identify the restriction of the exceptional transpose with the
perfect projection mate, then use conservativity of restriction of scalars.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The perfect scalar exceptional transpose is invertible at every input.
Source: Stacks 0ATI (thick closure of the unit), 0944 (perfect projection formula) and 07A6
(coefficient adjunction); Steps 1-8 of lem-sf-perfect-scalar-exceptional-extension
(blueprint: lem-sf-perfect-scalar-exceptional-extension-isIso).

Proof. Write E for scalar extension, U for restriction, L for compact support, ε for counits.
1. E ⊣ U (lem-pur-sheaf-ring-derived-coefficient-adjunction); U E K = K ⊗^L B_T on K-flat
   models, and U is conservative (it keeps the underlying complex).
2. For perfect P, P_T is perfect (lem-weil-pbc-finite-type-constant-exact) and the
   proper/open projection map π : L M ⊗ P_Y → L(M ⊗ P_X) is invertible
   (lem-sbc-ringed-site-perfect-projection-formula, lem-pur-etale-open-derived-tensor).
3. L_R is triangulated (lem-route-perfect-coefficient-shriek-mate); F_R gets the
   adjunction-compatible shifts and is triangulated; F_R N ⊗ P_X and F_R(N ⊗ P_Y) are exact
   in P.
4. λ(P,N), the transpose of (ε ⊗ 1) ∘ π⁻¹, is a shift-compatible transformation
   (lem-weil-pbc-ringed-projection-mate-exact).
5. λ(R,N) is the identity; its isomorphism locus is thick, hence all of Perf(R) (Stacks 0ATI),
   so λ(B,N) is invertible.
6. The restriction comparison d of lem-sf-etale-compact-scalar-restriction satisfies
   U(c) = d π for the specified comparison c.
7. The inverse ρ of the exceptional mate satisfies ε_R L(ρ) = U(ε_B) d.
8. The transpose of ρ ∘ U(σ_N) is (ε ⊗ 1) ∘ π⁻¹, so ρ ∘ U(σ_N) = λ(B,N) is invertible;
   hence U(σ_N), and by conservativity σ_N, is invertible. -/
theorem perfectScalarExceptionalExtensionMap_isIso
    {R B : Type (u + 1)} [CommRing R] [CommRing B]
    (φ : R →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    {FR : DerivedCategoryModule R Y ⥤ DerivedCategoryModule R X}
    {FB : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X}
    (aR : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ⊣ FR)
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB) :
    ∀ N : DerivedCategoryModule R Y,
      IsIso (aB.homEquiv _ _
      ((perfectCoefficientCompactSupportIso φ f c hB).inv.app (FR.obj N) ≫
        (scalarExtension φ Y).map (aR.counit.app N))) := by
  sorry

end AlgebraicGeometry.Etale
