/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceFormulaCoefficientSetup
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.Picard.FiniteTorStability
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Geometric comparison data

Source: Weil blueprint, sec-trace-formula/sk-d-six, the five comparison-data bullets
(blueprint: def-trf-geometric-comparison-data).
The functors are the recorded intrinsic finite-coefficient operations. The exceptional
adjunction is supplied only on the full bounded constructible finite-Tor subcategories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The separated geometric part of the existing finite-type over category.
Source: sk-d-setup, geometric schemes (blueprint: def-trf-geometric-comparison-data). -/
abbrev TraceFormulaGeometricSpace (F : FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (fun X : SixFunctorSpace F ↦ IsSeparated X.obj.hom)

namespace TraceFormulaGeometricSpace

variable {F : FiniteFieldDatum.{u}}

/-- The inherited separatedness, not additional geometric data.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
instance separated (X : TraceFormulaGeometricSpace F) : IsSeparated X.obj.obj.hom := X.property

/-- The base, with its identity structure morphism.
Source: def-trf-geometric-comparison-data, normalization clause
(blueprint: def-trf-geometric-comparison-data). -/
def point (F : FiniteFieldDatum.{u}) : TraceFormulaGeometricSpace F :=
  ⟨sixFunctorPoint F, inferInstanceAs (IsSeparated (𝟙 (Spec (.of F.k))))⟩

/-- The original structure map, regarded as a map of geometric schemes.
Source: def-trf-geometric-comparison-data, a_X (blueprint: def-trf-geometric-comparison-data). -/
def structureMap (X : TraceFormulaGeometricSpace F) : X ⟶ point F :=
  ObjectProperty.homMk (sixFunctorStructure X.obj)

/-- Every map has the compactification supplied by the geometric coefficient setup.
No second choice of compactification is made.
Source: sk-d-setup, chosen compactifications (blueprint: def-trf-geometric-comparison-data). -/
def compactification
    {l : ℕ} [Fact l.Prime] {hl : l ≠ F.p}
    {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {n : ℕ} {hn : 1 ≤ n} (G : TraceFormulaCoefficientSetup F l hl E n hn)
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :
    Compactification f.hom.hom.left :=
  letI := HasCompactification.of_over f.hom.hom
  G.val X.obj.obj Y.obj.obj f.hom.hom

end TraceFormulaGeometricSpace

namespace GeometricOperationPackage

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)

/-- The actual ambient uncompleted pro-etale derived category at level n+1.
Source: sk-d-setup, D(X,A) (blueprint: def-trf-geometric-comparison-data). -/
abbrev Ambient (X : TraceFormulaGeometricSpace F) :=
  proEtaleDerivedCategory X.obj.obj.left (Padic.coefficientExtensionRing l E (n + 1))

/-- The recorded coefficient predicate, without another constructibility notion.
Source: sk-d-setup, D^b_ctf (blueprint: def-trf-geometric-comparison-data). -/
abbrev domain (X : TraceFormulaGeometricSpace F) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.obj.obj.left

/-- The actual full coefficient subcategory.
Source: sk-d-setup (blueprint: def-trf-geometric-comparison-data). -/
abbrev Ctf (X : TraceFormulaGeometricSpace F) := (domain F l E n X).FullSubcategory

/-- Ambient pullback is the recorded exact derived inverse image.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev pull {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  finiteDerivedPullback l E n f.hom.hom.left

/-- Restrict the recorded pullback using the geometric coefficient requirement.
Source: sk-d-setup, pullback stability (blueprint: def-trf-geometric-comparison-data). -/
def pullCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) : Ctf F l E n Y ⥤ Ctf F l E n X :=
  (domain F l E n X).lift ((domain F l E n Y).ι ⋙ pull F l E n f)
    (fun K ↦ G.property.2.1 X.obj.obj Y.obj.obj f.hom.hom K.obj K.property)

/-- The chosen compactification's actual ordinary support direct image.
Source: sk-d-setup and sk-def-sf-operations (iv) (blueprint: def-trf-geometric-comparison-data). -/
def support
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  sfIntrinsicCompactSupport (TraceFormulaGeometricSpace.compactification G f)
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The restriction required by the given coefficient setup.
Source: sk-d-setup, support preservation (blueprint: def-trf-geometric-comparison-data). -/
def supportCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) : Ctf F l E n X ⥤ Ctf F l E n Y :=
  letI := HasCompactification.of_over f.hom.hom
  (domain F l E n Y).lift ((domain F l E n X).ι ⋙ support F l hl E n G f)
    (fun K ↦ G.property.2.2 X.obj.obj Y.obj.obj f.hom.hom K.obj K.property)

/-- The actual comparison-defined exceptional functor, restricted to D^b_ctf.
Source: sk-def-sf-operations (vi), thm-sf-ctf-stability (v) (blueprint: def-trf-geometric-compa
rison-data). -/
def exceptionalCtf
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    : Ctf F l E n Y ⥤ Ctf F l E n X :=
  sfStabilityFiniteExceptional F l hl E n X.obj.obj Y.obj.obj f.hom.hom
    (TraceFormulaGeometricSpace.compactification G f)

/-- The actual ambient tensor, restricted to the two finite-Tor inputs.
Source: thm-sf-ctf-stability (ii) (blueprint: def-trf-geometric-comparison-data). -/
def tensorCtf (X : TraceFormulaGeometricSpace F) :
    Ctf F l E n X × Ctf F l E n X ⥤ Ctf F l E n X :=
  (domain F l E n X).lift
    (((domain F l E n X).ι.prod (domain F l E n X).ι) ⋙
      finiteIntrinsicDerivedTensor l E X.obj.obj.left n)
    (fun K ↦ ((finiteTor_stability F l hl E n X.obj.obj X.obj.obj (𝟙 _)).2.1
      K.1.obj K.2.obj K.1.property K.2.property).1)

/-- The fixed ambient monoidal structure used by the recorded tensor and internal Hom.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev closed (X : TraceFormulaGeometricSpace F) :=
  finiteIntrinsicClosed l E X.obj.obj.left n

/-- Tensor objects in the fixed closed structure, with the structure explicit.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev tensorObj (X : TraceFormulaGeometricSpace F) (K L : Ambient F l E n X) :=
  (closed F l E n X).tensor.obj (K, L)

/-- The actual derived coefficient unit, with its monoidal structure explicit.
Source: sk-def-sf-operations (i) (blueprint: def-trf-geometric-comparison-data). -/
abbrev unitObj (X : TraceFormulaGeometricSpace F) : Ambient F l E n X :=
  (closed F l E n X).monoidal.tensorUnit

/-- Strong monoidal data between the two fixed ambient tensor structures.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
abbrev PullMonoidal {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y) :=
  @Functor.CoreMonoidal (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f)

/-- The unit comparison in the specified strong monoidal pullback.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
def pullUnitIso {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (m : PullMonoidal F l E n f) :
    unitObj F l E n X ≅ (pull F l E n f).obj (unitObj F l E n Y) :=
  @Functor.CoreMonoidal.εIso (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f) m

/-- The tensor comparison in the specified strong monoidal pullback.
Source: strong monoidal pullback (blueprint: def-trf-geometric-comparison-data). -/
def pullTensorIso {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (m : PullMonoidal F l E n f) (K L : Ambient F l E n Y) :
    tensorObj F l E n X ((pull F l E n f).obj K) ((pull F l E n f).obj L) ≅
      (pull F l E n f).obj (tensorObj F l E n Y K L) :=
  @Functor.CoreMonoidal.μIso (Ambient F l E n Y) _ (closed F l E n Y).monoidal
    (Ambient F l E n X) _ (closed F l E n X).monoidal (pull F l E n f) m K L

/-- An ordinary Cartesian square of geometric schemes over the fixed base.
The chosen identification is the dependency's ChosenCartesianSquare, rather than
an arbitrary commuting diagram. Source: def-trf-geometric-comparison-data, base change
(blueprint: def-trf-geometric-comparison-data). -/
structure Square where
  X : TraceFormulaGeometricSpace F
  Y : TraceFormulaGeometricSpace F
  X' : TraceFormulaGeometricSpace F
  Y' : TraceFormulaGeometricSpace F
  f : X ⟶ Y
  g : Y' ⟶ Y
  g' : X' ⟶ X
  f' : X' ⟶ Y'
  cartesian : ChosenCartesianSquare g'.hom.hom.left f'.hom.hom.left
    f.hom.hom.left g.hom.hom.left

variable
  (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)))

/-- The exceptional adjunctions are given on the full coefficient subcategories.
Their functors are the recorded ordinary support and transported etale exceptional
operations. Source: def-trf-geometric-comparison-data, initial adjunction convention
(blueprint: def-trf-geometric-comparison-data). -/
abbrev ExceptionalAdjunctions :=
  ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y),
    supportCtf F l hl E n G f ⊣ exceptionalCtf F l hl E n G f

end GeometricOperationPackage
end WeilConjectures
