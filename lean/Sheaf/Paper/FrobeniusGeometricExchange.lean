/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.FrobeniusSquareExchange

/-! # Geometric Frobenius exchange at all coefficient stages

Source: slopmaster2 blueprint, `def:weil-direct-image-object` and
`def:weil-compact-support-object`; Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: def-weil-frobenius-square-exchange).

The geometric wrappers use the actual base-changed square and keep the chosen
compactification over the finite field throughout integral realization,
scalar localization and descent to common coefficient stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

section GeometricCompactification
variable (D : FiniteFieldDatum.{u}) {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

-- Keep the existing finite-type parameters in the public signature.
set_option linter.unusedSectionVars false in
/-- Geometric base change preserves the chosen open/proper factorization.
Source: blueprint `def:weil-compact-support-object`; Stacks 01W6
(blueprint: def-weil-frobenius-square-exchange).
Proof: Over.pullback.map is the actual base-changed map. Its two squares are
Cartesian. Open immersions and proper morphisms are stable under base change.
Functoriality of Over.pullback carries c₀.comm to the last equality. -/
theorem geometricCompactification_properties :
    IsOpenImmersion (fiberMap D (zlCompactificationOpen D f₀ c₀)) ∧
      IsProper (fiberMap D (zlCompactificationProper D f₀ c₀)) ∧
      fiberMap D f₀ = fiberMap D (zlCompactificationOpen D f₀ c₀) ≫
        fiberMap D (zlCompactificationProper D f₀ c₀) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.overPullbackMap
      (P := @IsOpenImmersion) _ (zlCompactificationOpen D f₀ c₀) c₀.isOpenImmersion
  · exact MorphismProperty.overPullbackMap
      (P := @IsProper) _ (zlCompactificationProper D f₀ c₀) c₀.isProper
  · have h : f₀ = zlCompactificationOpen D f₀ c₀ ≫
        zlCompactificationProper D f₀ c₀ := by
      apply Over.OverMorphism.ext
      exact c₀.comm
    exact congrArg (fun g ↦
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map g).left) h
      |>.trans (congrArg Over.Hom.left (Functor.map_comp _ _ _))

/-- Base change of this very compactification over k₀; its middle Frobenius is
therefore the coefficient Frobenius of its retained k₀-model.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def geometricCompactification : Compactification (fiberMap D f₀) where
  Z := (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left
  g := fiberMap D (zlCompactificationProper D f₀ c₀)
  i := fiberMap D (zlCompactificationOpen D f₀ c₀)
  comm := (geometricCompactification_properties D f₀ c₀).2.2
  isProper := (geometricCompactification_properties D f₀ c₀).2.1
  isOpenImmersion := (geometricCompactification_properties D f₀ c₀).1

/-- The finite chosen-compactification Frobenius exchange.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusCompactFinite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) :=
  finiteCompact l E n hn (geometricCompactification D f₀ c₀)
    (galois D X₀) (galois D (zlCompactificationMiddle D f₀ c₀)) (galois D Y₀)
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

end GeometricCompactification

section GeometricIntegral
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [xft : LocallyOfFiniteType X₀.hom] [xqc : QuasiCompact X₀.hom]
  [yft : LocallyOfFiniteType Y₀.hom] [yqc : QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [fs : IsSeparated f₀.left]
  [fft : LocallyOfFiniteType f₀.left] [fqc : QuasiCompact f₀.left]

/-- The geometric fiber inherits exactly the finite-type hypotheses over k.
Source: blueprint geometric-fiber convention; Stacks 01T0
(blueprint: def-weil-frobenius-square-exchange).
Proof: its structure map is pullback.snd of the model structure map along Spec k.
Locally finite type and quasi-compact are stable under this base change. -/
theorem fiber_finiteType (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    LocallyOfFiniteType (D.geometricFiber T₀).hom ∧
      QuasiCompact (D.geometricFiber T₀).hom := by
  constructor
  · exact MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) _ T₀ inferInstance
  · exact MorphismProperty.baseChange_obj (P := @QuasiCompact) _ T₀ inferInstance

-- Keep the existing finite-type parameters in the public signature.
set_option linter.unusedSectionVars false in
include fs fft fqc in
/-- The relative geometric map has the source's separated finite-type properties.
Source: blueprint Frobenius square; Stacks 01T0, 01KH
(blueprint: def-weil-frobenius-square-exchange).
Proof: Over.pullback.map is the actual base-changed relative map. Separatedness,
locally finite type and quasi-compact are preserved by that Cartesian base change. -/
theorem fiberMap_properties :
    IsSeparated (fiberMap D f₀) ∧ LocallyOfFiniteType (fiberMap D f₀) ∧
      QuasiCompact (fiberMap D f₀) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance
  · exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance
  · exact MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance

/-- Install only the inherited proof instances used by the three integral stages.
Source: blueprint geometric-fiber convention
(blueprint: def-weil-frobenius-square-exchange). -/
instance fiberLocallyFiniteType (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    LocallyOfFiniteType (D.geometricFiber T₀).hom := (fiber_finiteType D T₀).1

/-- Quasi-compactness of the same actual geometric fiber.
Source: blueprint geometric-fiber convention
(blueprint: def-weil-frobenius-square-exchange). -/
instance fiberQuasiCompact (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    QuasiCompact (D.geometricFiber T₀).hom := (fiber_finiteType D T₀).2

/-- Direct integral Frobenius exchange with the finite-field and prime hypotheses.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusDirectIntegral :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  directIntegral (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
    (galois D X₀) (galois D Y₀) (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1

/-- Chosen-compactification integral Frobenius exchange with the same c at every level.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusCompactIntegral (c₀ : Compactification f₀.left) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  compactIntegral (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
    (geometricCompactification D f₀ c₀) (galois D X₀)
    (galois D (zlCompactificationMiddle D f₀ c₀)) (galois D Y₀)
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

/-- The direct recipe contains only the actual Frobenius square.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusDirectModel : SupportModel (fiberMap D f₀) (galois D X₀) (galois D Y₀) :=
  .direct (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1

/-- The compact recipe retains the selected model over k₀ and its middle Frobenius.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusCompactModel (c₀ : Compactification f₀.left) :
    SupportModel (fiberMap D f₀) (galois D X₀) (galois D Y₀) :=
  .compact (geometricCompactification D f₀ c₀)
    (galois D (zlCompactificationMiddle D f₀ c₀))
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

/-- Rational Frobenius exchange for either specified recipe: literal scalar
localization of the already constructed integral map on its integral representative.
Source: blueprint rational coefficient paragraphs
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusRational
    (M : SupportModel (fiberMap D f₀) (galois D X₀) (galois D Y₀)) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  modelRationalExchange (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    l D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀) (galois D X₀) (galois D Y₀) M E

/-- Algebraically closed coefficient Frobenius exchange for the direct recipe or
for the retained compactification recipe. Its component at (E,K) is the class of
the literal localized integral exchange at E. For cohomology take the terminal
model Y₀ = Spec k₀ and f₀ its structure map; no new exchange is then selected.
Source: blueprint common-stage and final cohomology paragraphs
(blueprint: def-weil-frobenius-square-exchange). -/
def frobeniusCommonStage
    (M : SupportModel (fiberMap D f₀) (galois D X₀) (galois D Y₀))
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  commonStageExchange (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    l D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀) (galois D X₀) (galois D Y₀) M Ω

end GeometricIntegral

end WeilConjectures.FrobeniusExchange
