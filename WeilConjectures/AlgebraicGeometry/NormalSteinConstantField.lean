/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.AlgebraicClosure
public import WeilConjectures.TraceFormula.LocalDimensionFormula
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteType

/-!
# Normal Stein factor and its algebraic constant field

Source: Stacks Project, Tag 03H0, properties (1)--(5), and Tag 0358;
de Jong, Families of curves and alterations, Lemma 5.2 proof, printed p. 613
(blueprint: lem-sfb-normal-stein-constant-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical Stein factor of a proper dominant map from a normal integral scheme
has normal integral finite-type base; its function field is the relative algebraic closure.
Source: Stacks Project, Tags 03H0, 035L and 0358; de Jong, Lemma 5.2 proof, p. 613
(blueprint: lem-sfb-normal-stein-constant-field).

The section isomorphisms `g.app (q ⁻¹ᵁ V)` specify the relative spectrum construction:
q is affine, so its inverse image of affine V is the spectrum of its sections. The
isomorphism identifies these sections with those on `g ⁻¹ᵁ (q ⁻¹ᵁ V) = f ⁻¹ᵁ V`.
Under this identification the restriction of g is the evaluation map, by the
Spec/global-sections adjunction. Thus this clause includes the prescribed charts and
maps, even for the empty affine open. The three function-field algebra structures are
the canonical generic-stalk maps, supplied by `dominantFunctionFieldAlgebra`.
Dominance of g follows from its geometrically connected fibres and is included to type
its function-field inclusion. `RingHom.Finite` expresses finiteness of k(B0)/k(B).
The last equality says that k(B0) is algebraically closed in k(T).

Proof plan, following the seven steps of the node:
1. Finite type over Spec k makes T and B Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). On a nonempty affine V = Spec A,
   proper restriction (lem-weil-pbc-proper-fp-permanence) has nonempty source U.
   Its sections R and A inject into E = k(T), with Frac A = k(B)
   (lem-sc-integral-function-field-affine-fraction and the sheaf axiom).
2. Form the relative normalization (lem-weil-pbc-relative-normalization).
   The sections R are integral over A (lem-weil-pbc-stein-integral-global-sections),
   so its affine integral-closure charts are exactly Spec R, with evaluation maps.
   Its base is integral, and normal by lem-sbc-relative-normalization-normal-stalks.
3. The structure sheaf is coherent: on a Noetherian affine, kernels of maps O^n to O
   are finite submodules, and localization is exact
   (lem-weil-pbc-localization-module-exact, pqf-def-coherent). Proper coherent
   pushforward in degree zero (lem-pc-coherent-hi) makes R finite over A.
   Thus q is finite, its base is finite type over k, and q is dominant since f is.
4. Affine Stein factorization (lem-weil-pbc-stein-factorization-affine) makes g
   proper with geometrically connected fibres on these charts. Properness is local
   on the target (lemma-nagata-projective-target-local); geometric fibres are local too.
5. By lem-sc-integral-function-field-affine-fraction, k(B0) = Frac R inside E.
   Localize R by A minus zero. This is an integral domain integral over F = Frac A,
   hence a field (a monic equation of least degree expresses each nonzero inverse).
   It is therefore Frac R, and the finite A-generators of R span it over F.
6. If a in E is algebraic over F, clear a common nonzero denominator d in A in a
   monic equation: d*a is integral over A and hence over every local ring of U.
   These local rings have fraction field E and are integrally closed, so d*a lies
   in each. By lem-sc-function-field-sections-glue it lies in R. Hence a lies in Frac R.
7. This proves the displayed relative algebraic closure equality
   (def-weil-relative-algebraic-closure) and finiteness. If an element of E is
   algebraic over this finite extension of F, transitivity of algebraicity places
   it in the same field. No separability or normality of B is used. -/
theorem exists_normal_stein_constant_field
    (k : Type u) [Field k] {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (t : T ⟶ Spec (CommRingCat.of k)) (b : B ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] [QuasiCompact t] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : T ⟶ B) [IsProper f] [IsDominant f] (hf : f ≫ b = t)
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.presheaf.stalk x)) :
    ∃ (B₀ : Scheme.{u}) (q : B₀ ⟶ B) (g : T ⟶ B₀),
      ∃ (_ : IsIntegral B₀) (_ : IsDominant q) (_ : IsDominant g),
        g ≫ q = f ∧ IsFinite q ∧
        LocallyOfFiniteType (q ≫ b) ∧ QuasiCompact (q ≫ b) ∧
        (∀ x : B₀, IsDomain (B₀.presheaf.stalk x) ∧
          IsIntegrallyClosed (B₀.presheaf.stalk x)) ∧
        IsProper g ∧ GeometricallyConnected g ∧
        (∀ V : B.Opens, IsAffineOpen V → IsIso (g.app (q ⁻¹ᵁ V))) ∧
        Set.range (@algebraMap B₀.functionField T.functionField _ _
          (g.dominantFunctionFieldAlgebra)) =
          (↑(@algebraicClosure B.functionField T.functionField _ _
            (f.dominantFunctionFieldAlgebra)) : Set T.functionField) ∧
        (@algebraMap B.functionField B₀.functionField _ _
          (q.dominantFunctionFieldAlgebra)).Finite ∧
        @algebraicClosure B₀.functionField T.functionField _ _
          (g.dominantFunctionFieldAlgebra) = ⊥ := by
  sorry

end AlgebraicGeometry
