/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel

/-!
# T-admissibility and its scalar local models

Source: Hemo--Richarz--Scholbach, Definition 6.1 and Theorem 6.2(2)
(blueprint: def-zl-t-admissible-coefficient-models).

## Main definitions

- `IsTAdmissible`: regular coherent scalar coefficients and flat profinite evaluations.
- `HasScalarLocalModels`: the existing finite constant local models on some pro-etale cover.
- `dualizableProperty`, `HasRestrictedStandardTStructure`: the inherited derived notions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The actual section-ring sheaf of the condensed coefficient ring.
Source: HRS Section 3 (blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev scalarRingSheaf : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  sectionRingSheaf (coherentTopology Profinite.{u}) Λ.X

/-- The ring R = Γ(*, Λ), evaluated at the terminal profinite set.
Source: HRS Definition 6.1 (blueprint: def-zl-t-admissible-coefficient-models). -/
abbrev scalarRing : CommRingCat.{u + 1} :=
  (scalarRingSheaf Λ).obj.obj (op (⊤_ Profinite.{u}))

/-- The scalar map to sections on S is restriction along its unique map to the point.
Source: HRS Definition 6.1 (blueprint: def-zl-t-admissible-coefficient-models). -/
def scalarSectionMap (S : Profinite.{u}) :
    scalarRing Λ →+* (scalarRingSheaf Λ).obj.obj (op S) :=
  ((scalarRingSheaf Λ).obj.map (terminal.from S).op).hom

end AlgebraicGeometry.ProEtale.CondensedRing
