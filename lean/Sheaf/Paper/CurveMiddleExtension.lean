/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PbcCommonStageCones

/-!
# Ordinary middle extension on a smooth curve

Source: blueprint, sec-purity-real-sheaves, sk-i-real-boundary,
`def-wf-middle-extension`; Weil II (1.1.1) b)--d).
(blueprint: def-wf-middle-extension)

Finite-level ordinary direct images are transported to the pro-etale site and
completed coefficients. Their inverse limit is an ordinary module sheaf, placed
in degree zero and rationalized at its original coefficient stage. In particular,
no right-derived direct image is used in this construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The geometric hypotheses of the middle-extension definition, bundled without
any extra connectedness, nonemptiness, or geometric irreducibility requirement.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
structure MiddleExtensionCurve (D : WeilConjectures.FiniteFieldDatum.{u}) where
  U : Over (Spec (CommRingCat.of D.k₀))
  C : Over (Spec (CommRingCat.of D.k₀))
  j : U ⟶ C
  [finiteU : LocallyOfFiniteType U.hom]
  [quasiCompactU : QuasiCompact U.hom]
  [finiteC : LocallyOfFiniteType C.hom]
  [quasiCompactC : QuasiCompact C.hom]
  [separatedU : IsSeparated U.hom]
  [separatedC : IsSeparated C.hom]
  [openImmersion : IsOpenImmersion j.left]
  dense : DenseRange j.left.base
  [smooth : Smooth C.hom]
  pureDimension : C.left.IsPureDimension 1

attribute [instance] MiddleExtensionCurve.finiteU MiddleExtensionCurve.finiteC
  MiddleExtensionCurve.quasiCompactU MiddleExtensionCurve.quasiCompactC
  MiddleExtensionCurve.separatedU MiddleExtensionCurve.separatedC
  MiddleExtensionCurve.openImmersion MiddleExtensionCurve.smooth

/-- The category-domain properties follow from the geometric hypotheses.
Source: blueprint def-wf-middle-extension, standing finite-field convention
(blueprint: def-wf-middle-extension).
Proof: finite-type schemes over a field are noetherian and finite-dimensional.
A separated morphism to the affine separated base has separated source. Apply
these facts to U and C. This includes the empty scheme and disconnected curves. -/
theorem MiddleExtensionCurve.baseProperties {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) :
    IsNoetherian c.U.left ∧ IsNoetherian c.C.left ∧
      c.U.left.IsSeparated ∧ c.C.left.IsSeparated ∧
        ∃ n : ℕ, topologicalKrullDim c.C.left ≤ (n : WithBot ℕ∞) := by
  sorry

/-- The source of the dense open is noetherian; this is a consequence, not new data.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
instance MiddleExtensionCurve.noetherianU {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : IsNoetherian c.U.left := c.baseProperties.1

/-- The curve is noetherian, including when empty.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
instance MiddleExtensionCurve.noetherianC {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : IsNoetherian c.C.left := c.baseProperties.2.1

/-- Absolute separatedness needed by the recorded lisse category.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
instance MiddleExtensionCurve.absoluteSeparatedU {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) : c.U.left.IsSeparated := c.baseProperties.2.2.1

/-- The coefficient prime is a unit on every stalk and residue field.
Source: blueprint def-wf-middle-extension, global finite-field convention
(blueprint: def-wf-middle-extension).
Proof: the cardinality p^a of the base field forces its characteristic to be p.
The image of a distinct prime l is nonzero, hence a unit in that field. The
structure homomorphisms carry its inverse to every local ring and residue field. -/
theorem MiddleExtensionCurve.coefficientUnits {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p) :
    (∀ x : c.U.left, IsUnit (l : c.U.left.residueField x)) ∧
      ∀ x : c.C.left, IsUnit (l : c.C.left.presheaf.stalk x) := by
  sorry

/-- The recorded lisse algebraic-coefficient category with its derived unit instances.
Source: blueprint def-wf-middle-extension; Weil II (1.1.1) d)
(blueprint: def-wf-middle-extension). -/
abbrev MiddleExtensionCurve.LisseSheaf {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra ℚ_[l] Qbar]
    [IsAlgClosure ℚ_[l] Qbar] :=
  letI := fun x : c.U.left => ((c.coefficientUnits l hl).1 x).invertible
  LisseAlgebraicSheaf l c.U.left Qbar

/-- The target is exactly the recorded pair category, with no envelope.
Source: blueprint def-wf-middle-extension and def-weil-pbc-qbar-category
(blueprint: def-wf-middle-extension). -/
abbrev MiddleExtensionCurve.CoefficientCategory {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra ℚ_[l] Qbar]
    [IsAlgClosure ℚ_[l] Qbar] :=
  letI := Fact.mk c.baseProperties.2.2.2.2
  letI := Fact.mk (c.coefficientUnits l hl).2
  pbcQbarCategory l Qbar c.C.left

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]

/-- Shrinking a finite field preserves its integral elements.
Source: blueprint def-wf-middle-extension, coefficient-stage interpretation
(blueprint: def-wf-middle-extension).
Proof: the Shrink algebra equivalence fixes Q_l. Uniqueness of the extended
absolute value makes it isometric. Thus it sends the closed unit ball, namely
its valuation ring, into the valuation ring of E. The recorded fraction-field
identification agrees with this equivalence on all integral elements. -/
theorem middleExtensionIntegerMap_mem (E : Padic.FiniteCoefficientFields l Qbar)
    (a : PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)) :
    qbarStageFieldEquiv.{u + 1, u} l Qbar E
      (algebraMap _ (Localization.Away (pbcStageUniformizer.{u} l Qbar E)) a) ∈
        Padic.coefficientExtensionIntegers l E.val := by
  sorry

/-- The coefficient map is the integral-normalized field identification.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
def middleExtensionIntegerMap (E : Padic.FiniteCoefficientFields l Qbar) :
    PbcIntegralRing l (pbcFiniteField.{u} l Qbar E) →+*
      Padic.coefficientExtensionIntegers l E.val :=
  ((qbarStageFieldEquiv.{u + 1, u} l Qbar E).toRingHom.comp
    (algebraMap _ (Localization.Away (pbcStageUniformizer.{u} l Qbar E)))).codRestrict
      (Padic.coefficientExtensionIntegers l E.val) (middleExtensionIntegerMap_mem l Qbar E)

/-- At a fixed stage this is ordinary direct image: sections at V, restriction
maps and morphism components are evaluated at V times_C U. The subsequent functors
only change the site and scalar presentation, retaining the coefficient action.
Source: blueprint def-wf-middle-extension, ordinary module direct-image paragraph
(blueprint: def-wf-middle-extension). -/
def middleExtensionLevelFunctor (E : Padic.FiniteCoefficientFields l Qbar)
    {U C : Scheme.{u}} (j : U ⟶ C) :
    Sheaf U.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) ⥤
        pbcModules C (pbcAdicCompletion C (pbcStageDatum.{u} l Qbar E)) :=
  Etale.lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) j ⋙
    ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) C ⋙
    Sheaf.restrictScalars (ProEt.topology C) (middleExtensionIntegerMap l Qbar E) ⋙
    pbcAssociatedModule C (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))
      (adicLisseRing C (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)))
      (adicLisseConstantUnit C (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))) ⋙
    pbcExtend (pbcCompletedScalar C (pbcStageDatum.{u} l Qbar E))

/-- The ordinary inverse limit of the actual finite-level direct images. It is
not asserted that their transition tower is adic after applying j_*.
Source: blueprint def-wf-middle-extension; Weil II (1.1.1) b)
(blueprint: def-wf-middle-extension). -/
def middleExtensionIntegralSheaf (E : Padic.FiniteCoefficientFields l Qbar)
    {U C : Scheme.{u}} (j : U ⟶ C) (F : AdicIntegralDiagram l E.val U) :=
  limit (F ⋙ middleExtensionLevelFunctor l Qbar E j)

/-- Place the ordinary sheaf direct image in degree zero, before any shift.
Source: blueprint def-wf-middle-extension, final paragraph
(blueprint: def-wf-middle-extension). -/
def middleExtensionIntegralComplex (E : Padic.FiniteCoefficientFields l Qbar)
    {U C : Scheme.{u}} (j : U ⟶ C) (F : AdicIntegralDiagram l E.val U) :
    pbcAmbientStage l Qbar C E :=
  (DerivedCategory.singleFunctor _ 0).obj (middleExtensionIntegralSheaf l Qbar E j F)

/-- The explicitly constructed integral complex belongs to the recorded stage.
Source: blueprint def-wf-middle-extension, interpretation in the coefficient category
(blueprint: def-wf-middle-extension).
Proof: inverse image to the pro-etale site identifies each torsion level with its
constant-coefficient module realization. Integral coefficient transport is an
isometry and hence preserves the uniformizer-adic topology. Tensor extension to
completed scalars leaves these torsion levels unchanged. A quasi-compact open
immersion of noetherian curves has finite constructible direct images at every
finite level. At each of the finitely many boundary points their inverse limit
is the inertia-invariant submodule of a finite integral stalk; it is finite over
the DVR. These modules, and the lisse module on U, give a finite stratification
and uniform bounded finite presentations. On the pro-etale site inverse limits
of the original surjective finite systems compute their completed module sheaf.
Ordinary direct image preserves limits, so the displayed limit is j_* of that
module sheaf. Its finite stratified modules are adically complete, and their
derived reductions have uniform amplitude [-1,0] over the DVR. The quotient
maps give compatible etale origins and the canonical reduction normalizations.
These are precisely the three conditions of PbcIsBoundedConstructibleComplete. -/
theorem middleExtensionIntegralComplex_mem {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (E : Padic.FiniteCoefficientFields l Qbar)
    [∀ x : c.U.left, Invertible (l : c.U.left.residueField x)]
    (F : LisseIntegralSheaf l E.val c.U.left) :
    PbcIsBoundedConstructibleComplete c.C.left (pbcStageDatum.{u} l Qbar E)
      (middleExtensionIntegralComplex l Qbar E c.j.left F.obj) := by
  sorry

/-- Sheaf-theoretic middle extension j_*F, as an object of the actual Qbar pair
category. Its integral representative is the explicit ordinary sheaf above,
placed in degree zero; no right-derived pushforward occurs.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
def curveMiddleExtension {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : c.LisseSheaf l hl Qbar) : c.CoefficientCategory l hl Qbar :=
  letI := fun x : c.U.left => ((c.coefficientUnits l hl).1 x).invertible
  letI := Fact.mk c.baseProperties.2.2.2.2
  letI := Fact.mk (c.coefficientUnits l hl).2
  let P := lisseAlgebraicPair l c.U.left Qbar F
  let M := (lisseCoefficientPairModel l c.U.left Qbar P).integral
  { stage := P.base
    obj := (pbcStageLocalization l Qbar c.C.left P.base).obj
      ⟨middleExtensionIntegralComplex l Qbar P.base c.j.left M.obj,
        middleExtensionIntegralComplex_mem l Qbar c P.base M⟩ }

/-- The notation (j_*F)[1] first forms ordinary sheaf middle extension and then
applies the recorded pair-category cohomological shift. Rj_* is a separate
right-derived functor and its higher cohomology is not discarded by this definition.
Source: blueprint def-wf-middle-extension, final paragraph
(blueprint: def-wf-middle-extension). -/
def shiftedCurveMiddleExtension {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : MiddleExtensionCurve D) (hl : l ≠ D.p)
    (F : c.LisseSheaf l hl Qbar) : c.CoefficientCategory l hl Qbar :=
  letI := Fact.mk c.baseProperties.2.2.2.2
  letI := Fact.mk (c.coefficientUnits l hl).2
  (curveMiddleExtension l Qbar c hl F)⟦(1 : ℤ)⟧

end AlgebraicGeometry.Scheme
