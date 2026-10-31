/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.Compactification.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientSetup
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.FiniteTorStability
import WeilConjectures.AlgebraicGeometry.CondensedFunctorPackage
import WeilConjectures.AlgebraicGeometry.GeometricOperations
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Topological invariance for the trace-formula coefficient categories

Source: Weil conjectures blueprint, `sec-trace-formula/sk-i-topology/i-topology.md`
(blueprint: i-topology).

The equivalence records the finite-Tor constructible pullback, its direct-image
quasi-inverse, and the same inverse realised by compact support.  The theorem is
statement-only at this stage; its proof follows the pro-etale topological-invariance
argument, exact descent to complexes, finite-Tor stability, and the proper comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-! The categories and functors occurring in the topological-invariance statement. -/

/--
The finite-Tor constructible pullback along `r` has an equivalence whose inverse is
the direct image, and whose compact-support realisation agrees with that inverse.
The natural isomorphisms after the full inclusions specify the operations on objects
and morphisms. The equivalence supplies its invertible unit and counit.
Source: Weil conjectures blueprint, `sec-trace-formula/sk-i-topology/i-topology.md`
(blueprint: i-topology).
-/
def TraceFormulaTopologicalEquivalence
    (T : TraceFormulaCoefficientConventions.{u})
    {X Y : Scheme.{u}} (r : X ⟶ Y)
    (c : Compactification r) : Prop :=
  ∃ e : finiteTorConstructibleCategory T.coefficients.l T.coefficientField T.level
      T.level_pos Y ≌
      finiteTorConstructibleCategory T.coefficients.l T.coefficientField T.level
        T.level_pos X,
    Nonempty (e.functor ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ⋙
        T.derivedPullback r) ∧
    Nonempty (e.inverse ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ⋙
        proEtaleConstantDerivedDirectImage r T.coefficientRing) ∧
    Nonempty (e.inverse ⋙
        (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y).ι ≅
      (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos X).ι ⋙
        @sfIntrinsicCompactSupport X Y r c T.coefficientRing inferInstance
          (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
            T.level T.level_pos))

/--
For a finite universal homeomorphism, pullback is an equivalence on the bounded
constructible finite-Tor categories, with inverse `Rr_* = Rr_!`; the unit and
counit are invertible.  The second conjunct applies this to the reduction.

Source: Weil conjectures blueprint, `sec-trace-formula/sk-i-topology/i-topology.md`,
and Stacks Project, Tags 09AB and 04DF (blueprint: i-topology).

Proof: (1) `lem-trf-proetale-topological-invariance` gives the equivalence of set
sheaves on the small pro-etale sites in the geometric setting of `sk-d-setup`.
(2) Transport the module action through the constant-ring identification of
`prop-weil-pbc-proetale-constant-ring-map`; the unit and counit are linear by
naturality. The pullback is the exact functor of
`prop-weil-pbc-proetale-constant-exact`; its inverse is exact because it is an equivalence.
(3) Apply these exact functors to complexes. They commute with cohomology and preserve
quasi-isomorphisms, so the unit, counit and triangle identities descend through the
localization `def-weil-abstract-derived-category`. The finite pullback of
`def-weil-derived-pullback-tensor-hom` is this termwise functor. A K-injective
resolution and exactness identify the inverse with `def-weil-derived-direct-image`.
(4) A finite morphism is proper by `lem-weil-pbc-finite-proper`, hence separated and
finite type by `def-weil-proper-morphism`. Apply clauses (i) and (iii) of
`thm-sf-ctf-stability` to restrict both functors and their invertible unit and counit
to the full finite-Tor constructible subcategories.
(5) Clause (3) of `prop-functor-package`, in the notation of `sk-d-six`, identifies
the proper compact-support direct image with the ordinary direct image. Transport
the unit and counit along this comparison; naturality preserves both triangle identities.
(6) `lem-weil-pbc-reduction-universal-homeomorphism` and
`lem-weil-pbc-closed-immersion-finite` apply to the reduction immersion. Its source
is finite type over the base since on each affine it is a quotient algebra
(`def-weil-finite-type-morphism`, `def-weil-closed-immersion`). Its diagonal is closed
by `lem-weil-pbc-closed-immersion-base-change`, giving separation. Apply (1)--(5)
to the canonical morphism from the reduction to the original scheme.
-/
theorem finiteUniversalHomeomorphism_traceFormula
    (T : TraceFormulaCoefficientConventions.{u}) :
    (∀ (X Y : Over (Spec (CommRingCat.of T.datum.k)))
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (r : X ⟶ Y) [IsFinite r.left],
      (topologically IsHomeomorph).universally r.left →
        ∀ c : Compactification r.left, TraceFormulaTopologicalEquivalence T r.left c) ∧
      (∀ (Y : Over (Spec (CommRingCat.of T.datum.k)))
        [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
        (c : Compactification Y.left.nilradical.subschemeι),
        TraceFormulaTopologicalEquivalence T Y.left.nilradical.subschemeι c) := by
  sorry

end WeilConjectures
