/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.OrdinaryCompactWeilCohomology
public import Sheaf.Paper.WeilCompactSupportCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Compact cohomology retaining the common-stage Weil structure

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-sf-admissible,
def-weil-ordinary-compact-cohomology, final Weil clause
(blueprint: def-weil-ordinary-compact-cohomology).

The ordinary, compact, finite, integral, rational and Qbar coefficient constructions
remain publicly available from the original module. The definition below retains
H_cⁿ as the canonical higher image on Spec(k₀) in the actual common-stage Weil
heart. Evaluating its geometric fibre gives the coefficient cohomology with its
induced Frobenius. The canonical compact-support image and its comparison with
sfQbarCompactSupportValue are those already constructed in the imported module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Spec(k₀) with its identity structure map, the base of geometric cohomology.
Source: blueprint ordinary/compact coefficient base convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev sfWeilCohomologyPoint (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) where
  left := Spec (.of D.k₀)
  right := default
  hom := 𝟙 _

/-- The identity structure map has its inherited finite-morphism structure.
Source: blueprint coefficient base convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
instance sfWeilCohomologyPoint_isFinite (D : FiniteFieldDatum.{u}) :
    IsFinite (sfWeilCohomologyPoint D).hom :=
  inferInstanceAs (IsFinite (𝟙 (Spec (.of D.k₀))))

/-- H_cⁿ as a Weil sheaf on Spec(k₀), using the existing canonical compact-support
higher image, including its Weil action. Its geometric coefficient fibre is
H_cⁿ of the recorded common-stage For object. No arbitrary linear operator is
chosen: Frobenius is retained as part of the higher image's fixed-pair structure.
Source: blueprint ordinary/compact cohomology, final Weil clause
(blueprint: def-weil-ordinary-compact-cohomology). -/
def commonStageCompactWeilCohomology
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : Compactification Y₀.hom) (G : sfCommonStageWeilSheaf D l hl Y₀ Qbar) (n : ℕ) :
    sfCommonStageWeilSheaf D l hl (sfWeilCohomologyPoint D) Qbar :=
  zlWeilHigherShriek D l hl Qbar
    (Over.homMk Y₀.hom : Y₀ ⟶ sfWeilCohomologyPoint D) c n G

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Ordinary coefficient cohomology, formed at the recorded finite stage and then
extended to the specified algebraic closure. This is exactly the stagewise target
in the node, with no equality of site and coefficient universes.
Source: blueprint order 1510 (blueprint: def-weil-ordinary-compact-cohomology). -/
def adicOrdinaryCohomology (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (i : ℤ) : ModuleCat.{max u v} Ω :=
  (ModuleCat.extendScalars (K.stage.val.subtype.comp
    (Shrink.algEquiv ℚ_[l] K.stage.val).toRingHom)).obj
      (rationalOrdinaryCohomology D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) Y K.obj i)

/-- Compactly supported coefficient cohomology with the same final scalar extension.
The compactification is a choice of presentation of the recorded RΓ_c, not a
properness assumption on Y.
Source: blueprint order 1510 (blueprint: def-weil-ordinary-compact-cohomology). -/
def adicCompactCohomology (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (i : ℤ) : ModuleCat.{max u v} Ω :=
  (ModuleCat.extendScalars (K.stage.val.subtype.comp
    (Shrink.algEquiv ℚ_[l] K.stage.val).toRingHom)).obj
      (rationalCompactCohomology D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) Y c K.obj i)

end WeilConjectures
