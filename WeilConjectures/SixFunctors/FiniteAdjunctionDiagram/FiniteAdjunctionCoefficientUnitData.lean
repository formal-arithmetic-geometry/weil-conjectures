/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionSystemData

/-! The concrete coefficient unit used by the finite adjunction realization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

/-- The actual regular module over the sequence ring.
Source: node proof step 9 (blueprint: def-sf-finite-adjunction-coefficient-unit). -/
def ordinaryCoefficientUnit (W : Scheme.{u}) : coefficientSequenceModules l E W :=
  SheafOfModules.unit ((sheafCompose
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (coefficientSequenceCommRingSheaf l E W))

/-- The coefficient-unit system is the actual sequence ring as a module in degree zero.
Source: node proof step 9 (blueprint: def-sf-finite-adjunction-coefficient-unit). -/
def coefficientUnit (W : Scheme.{u}) : coefficientSequenceDerived l E W :=
  (DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
    (ordinaryCoefficientUnit W)

end WeilConjectures.FiniteAdjunctionDiagram
