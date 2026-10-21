/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability

/-! # Affine ind-etale test objects and their finite-coefficient restriction

Source: Weil conjectures blueprint, main-20261015, sec-smooth-purity,
`sk-prop-sf-kunneth-ordinary/pur7710-def-ind-etale-tests.md`, order 1983
(blueprint: pur7710-def-ind-etale-tests).

The presentation predicate uses the existing `proAffineEtale`: its stages are absolutely
affine and etale, and its small cofiltered index is nonempty. Over the affine open they
are of finite presentation, and every transition between affine schemes is affine.
The derived restriction is ordinary and uncompleted, using the canonical constant-section
coefficient identification already fixed by the pro-etale operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A test morphism factors through an affine open by a pro-affine-etale morphism.
Here `proAffineEtale` uses small nonempty cofiltered presentations by affine etale schemes.
Their maps to the affine open are of finite presentation and their transitions are affine.
The compatible limiting cone is equivalently the limit in schemes over this open.
Source: blueprint main-20261015, order 1983, first sentence
(blueprint: pur7710-def-ind-etale-tests). -/
def IsIndEtaleTest {B W : Scheme.{u}} (f : B ⟶ W) : Prop :=
  ∃ (V : W.Opens), IsAffineOpen V ∧
    ∃ (g : B ⟶ V.toScheme), proAffineEtale g ∧ g ≫ V.ι = f

/-- Every test morphism is weakly etale, hence defines an object of the small site.
Source: blueprint main-20261015, order 1983, second sentence
(blueprint: pur7710-def-ind-etale-tests).

Proof: unpack the affine-open factorization. The pro-affine-etale factor is weakly etale
by `proAffineEtale_le_weaklyEtale`, or by the affine ind-etale comparison of
`det-pe-morphisms-etale-comparison` and the spectrum-colimit/limit identification.
The open immersion is etale (`lem-weil-pbc-open-immersion-etale`), hence weakly etale
by clause 1 of `det-pe-morphisms-etale-comparison`. Composition is weakly etale by
`sk-lem-pe-weakly-etale-stability`. Rewrite by the factorization equality. -/
theorem IsIndEtaleTest.weaklyEtale {B W : Scheme.{u}} {f : B ⟶ W}
    (hf : IsIndEtaleTest f) : WeaklyEtale f := by
  sorry

/-- The test morphism as an object of the recorded small pro-etale site.
Only its membership proof is supplied by the preceding named theorem; its underlying
scheme and structure morphism are the original `B` and `f`.
Source: blueprint main-20261015, order 1983, second sentence
(blueprint: pur7710-def-ind-etale-tests). -/
def IsIndEtaleTest.toProEt {B W : Scheme.{u}} {f : B ⟶ W}
    (hf : IsIndEtaleTest f) : W.ProEt :=
  @ProEt.mk W B f hf.weaklyEtale

/-- Restriction to a test is the ordinary unbounded derived module inverse image.
The coefficient ring is the recorded quotient by the power of the chosen uniformizer.
The pullback uses the canonical constant-preserving coefficient identification, not a
choice of a ring-sheaf isomorphism; no completion or invertibility of the prime is imposed.
Source: blueprint main-20261015, order 1983, third sentence
(blueprint: pur7710-def-ind-etale-tests). -/
noncomputable def indEtaleTestRestriction {B W : Scheme.{u}} (f : B ⟶ W)
    (_hf : IsIndEtaleTest f) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (K : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E n)) :
    proEtaleDerivedCategory B (Padic.coefficientExtensionRing l E n) :=
  (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) f).obj K

end AlgebraicGeometry.Scheme
