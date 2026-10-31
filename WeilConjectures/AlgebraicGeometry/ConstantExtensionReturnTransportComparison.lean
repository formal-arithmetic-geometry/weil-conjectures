/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnData

/-! # Sheet return and its local weight filtrations

Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, and (1.2.6), p. 154
(blueprint: lem-zl-constant-extension-return-local-operators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Finite, whole-tower and rational ordered-block transport comparison, before
any assertion about weights or subobjects. Source: Deligne, Weil II
(1.1.7)--(1.1.10), pp. 150--152, with the integral enhancement of the cited laws.
(blueprint: lem-zl-sheet-return-transport-comparison).

Proof: expand the m-fold return Weil map and then its r-fold iterate. Induction
concatenates the m-factor blocks in their original order. The finite point
transport composition law identifies each block with the corresponding power
transport, on every successive pullback. Perform the same induction on whole
coefficient systems using the tower power law and its naturality. Apply the
specified zeta/nu realization equation to the resulting whole-system equality;
no inference from separate reductions is made. The stalk comparison is the
already specified composite of the point-fibre equality and pullback
compositors. Inserting its formula into the local operator identifies the
transport, square and Weil-map factors, hence their composites. Naturality
follows from naturality of these factors. Raw scalar localization extends the
identity to rational arrows by tensor generators. The iterated-return scalar
calculus identifies the two scalar comparison composites, giving exactly the
stated coefficient-extension square. No integral Weil lattice, lissity or finite
Tor-amplitude is required. -/
theorem sheetReturnTransportComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    SheetReturn.TransportLaws D l E hl m ∧
      SheetReturnRationalOperators D m hm X₀ l hl E ∧
      SheetReturnStalkNaturality D m hm X₀ l hl E ∧
      SheetReturnScalarCompatibility D m hm X₀ l hl E := by sorry

end WeilConjectures
