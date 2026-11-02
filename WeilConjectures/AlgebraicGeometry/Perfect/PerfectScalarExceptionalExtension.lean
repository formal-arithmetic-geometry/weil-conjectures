/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectCoefficientShriekMate
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarExceptionalExtensionIsIso
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarExceptionalExtensionNatural

/-! # Perfect scalar extension and the exceptional right adjoint

Source: Stacks Project, Tag 0ATI, lemma-perfect-ring-classical-generator, and the
counit calculation in the node; latest blueprint, prop-coef-integral-dualizing.proof.md,
paragraph 1 (blueprint: lem-sf-perfect-scalar-exceptional-extension).

The comparison is the actual adjunction transpose of inverse compact-support coefficient
change followed by scalar extension of the exceptional counit. All categories are ordinary
unbounded small-etale module derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The specified scalar/exceptional arrow at N, with its counit-transpose normalization.
Source: Stacks 07A6 and the counit calculation of the node, using the canonical comparison
of lem-route-perfect-coefficient-shriek-mate
(blueprint: lem-sf-perfect-scalar-exceptional-extension). -/
def perfectScalarExceptionalExtensionMap
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
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB)
    (N : DerivedCategoryModule R Y) :
    (scalarExtension φ X).obj (FR.obj N) ⟶ FB.obj ((scalarExtension φ Y).obj N) :=
  aB.homEquiv _ _
    ((perfectCoefficientCompactSupportIso φ f c hB).inv.app (FR.obj N) ≫
      (scalarExtension φ Y).map (aR.counit.app N))

/-- Perfect coefficient extension commutes with any chosen exceptional right adjoints,
naturally on every unbounded input, and in particular at the constant coefficient unit.
Source: Stacks 0ATI and the adjunction-transpose argument in the node; latest blueprint,
prop-coef-integral-dualizing.proof.md, paragraph 1
(blueprint: lem-sf-perfect-scalar-exceptional-extension).

Proof, following the nine steps of the node:
1. The scalar adjunction of lem-pur-sheaf-ring-derived-coefficient-adjunction identifies
   restricted extension with tensor by B_T on K-flat models. Exact restriction of scalars
   is conservative: it leaves the underlying abelian complex unchanged.
2. For a perfect R-complex P, termwise constant sheafification is exact by
   lem-weil-pbc-finite-type-constant-exact. It sends finite-projective splittings to
   splittings of finite-free sheaves. The specified compact-support projection map pi
   for P_T is invertible: use lem-sbc-ringed-site-perfect-projection-formula for the proper
   factor and lem-pur-etale-open-derived-tensor for the open factor, with the pullback
   tensor identification of lem-kun-inverse-image-monoidal.
3. By lem-route-perfect-coefficient-shriek-mate, compact support is triangulated with
   integer shifts. Give its right adjoint the unique adjunction-compatible shifts by
   lem-weil-pbc-adjunction-shift-compatibility-unique; lem-sf-triangulated-right-adjoint
   makes it exact. Tensor is exact by lem-kun-derived-tensor-triangulated. Thus both
   P maps to FR(N) tensor P_X and P maps to FR(N tensor P_Y) are exact in P.
4. Define lambda(P,N) by transposing inverse pi followed by counit tensor identity.
   Naturality follows from the adjunction bijections. Its shift compatibility, including
   connecting arrows, follows from lem-weil-pbc-ringed-projection-mate-exact for the proper
   factor, the degreewise signed-total identity for the open factor, and the compatible
   adjunction shifts. Hence lambda is a transformation of the exact functors in step 3.
5. Unit normalization makes lambda(R,N) the identity. Apply
   lem-sf-generating-class-determination and lem-sf-perfect-ring-classical-generator
   (Stacks 0ATI): the isomorphism locus is thick, so lambda(B,N) is invertible.
6. The proper/open restriction comparison d of lem-sf-etale-compact-scalar-restriction
   satisfies U(c)u = d L(u) and U(c) = d pi. These are equalities of the specified maps:
   transpose the proper counit; the open scalar balancing sends x tensor b to x tensor b.
   Use def-weil-pbc-adjunction-conjugate and the scalar unit normalization here.
7. The inverse rho of perfectCoefficientExceptionalIso has counit equation
   epsilon_R L(rho) = U(epsilon_B) d. Verify it by the defining conjugate Hom chain,
   the scalar unit equation in step 6, and naturality of d.
8. Transpose rho U(sigma). The equation in step 7, naturality of d, and the definition
   of sigma identify its transpose with counit tensor identity after inverse pi.
   Thus rho U(sigma) = lambda(B,N). Both rho and lambda(B,N) are invertible, so U(sigma)
   is invertible; conservativity of U proves sigma is invertible.
9. The defining Hom bijections are natural (def-weil-pbc-adjunction-mate), giving a
   natural isomorphism with these components. At R_Y[0], extension gives B_Y[0] via the
   rank-one balancing map. Evaluation and that identification give the unit specialization.
No bounds, constructibility, completeness, flatness, or finiteness of coefficients enter.
In Lean, Steps 1-8 are `perfectScalarExceptionalExtensionMap_isIso`
(lem-sf-perfect-scalar-exceptional-extension-isIso) and Step 9 is
`perfectScalarExceptionalExtension_natural`
(lem-sf-perfect-scalar-exceptional-extension-natural). -/
theorem perfectScalarExceptionalExtension
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
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB)
    : (∀ N : DerivedCategoryModule R Y,
        IsIso (perfectScalarExceptionalExtensionMap φ f c hB aR aB N)) ∧
      (∃ e : FR ⋙ scalarExtension φ X ≅ scalarExtension φ Y ⋙ FB,
        ∀ N : DerivedCategoryModule R Y,
          e.hom.app N = perfectScalarExceptionalExtensionMap φ f c hB aR aB N) ∧
      Nonempty ((scalarExtension φ X).obj (FR.obj (constantComplex R Y)) ≅
        FB.obj (constantComplex B Y)) := by
  exact ⟨perfectScalarExceptionalExtensionMap_isIso φ f c hB aR aB,
    perfectScalarExceptionalExtension_natural φ f c hB aR aB⟩

end AlgebraicGeometry.Etale
