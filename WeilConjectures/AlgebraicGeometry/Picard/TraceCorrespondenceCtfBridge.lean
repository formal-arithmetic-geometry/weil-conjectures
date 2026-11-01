/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeometricOperationPackage.Comparisons.GeometricOperations
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Finite-Tor bridge for trace correspondences

Source: Weil blueprint, sec-trace-formula/sk-d-operator (blueprint: sk-d-operator).
This module records the bounded constructible finite-Tor endocorrespondences used by the
global operator of `sk-d-operator`: a geometric support, two legs, and a coefficient map
from the ordinary pullback along leg 2 to the exceptional pullback along leg 1.  The
compactification of leg 1 and its exceptional adjunction are not data: they are those of
the coefficient setup `G` and the given `ExceptionalAdjunctions` `A`.  The associated
`sk-d-corr` correspondence `TraceCorrespondence` is constructed from these data, not
supplied separately, and no comparison isomorphism is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures
open GeometricOperationPackage

/-- A bounded constructible finite-Tor endocorrespondence of `(X,K)` on the geometric
operation package: support `C`, legs `c₁,c₂ : C ⟶ X`, and `u : c₂^*K ⟶ c₁^!K`, where
`c₁^!` is the exceptional functor of `A c₁`.
Source: Weil blueprint, sec-trace-formula/sk-d-operator and sk-d-corr, first paragraph
(blueprint: def-trf-ctf-correspondence-bridge). -/
structure TraceCorrespondenceCtfBridge
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    (A : ExceptionalAdjunctions F l hl E n G)
    (X : TraceFormulaGeometricSpace F) (K : Ctf F l E n X) where
  /-- The geometric support. -/
  C : TraceFormulaGeometricSpace F
  /-- The exceptional leg. -/
  c₁ : C ⟶ X
  /-- The ordinary-pullback leg. -/
  c₂ : C ⟶ X
  /-- The coefficient map `c₂^*K ⟶ c₁^!K` on `D^b_ctf`. -/
  u : (pullCtf F l hl E n G c₂).obj K ⟶ (exceptionalCtf F l hl E n G c₁).obj K

namespace TraceCorrespondenceCtfBridge

variable {F : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime] {hl : l ≠ F.p}
  {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {n : ℕ}
  {G : TraceFormulaCoefficientSetup F l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))}
  {A : ExceptionalAdjunctions F l hl E n G}
  {X : TraceFormulaGeometricSpace F} {K : Ctf F l E n X}

end TraceCorrespondenceCtfBridge

end WeilConjectures
