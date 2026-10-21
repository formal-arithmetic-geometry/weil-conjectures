/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.PbcCommonStageCones
import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated

import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.FiniteStagePairCategory
/-! # Simultaneous lifting of distinguished rows and finite equations

Source: blueprint `main-20261015`, `thm-weil-pbc-verdier-axioms.proof.md`, TR2--TR4
common-stage representation sentences (blueprint: lem-weil-pbc-distinguished-diagram-lifting).

The expression helpers encode only finite terms, with typed endpoints. An occurrence
is an original vertex together with a number of applications of [1]. Raw stage objects
are scalar extensions of these occurrences; their shift comparison is the prescribed sigma.
No triangulation of the pair category is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b e r w u v c

open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.PbcFiniteDiagram

/-- An occurrence of a vertex after finitely many shifts [1]. Source: blueprint TR2--TR4
finite data (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Vertex (A : Type a) where
  index : A
  shifts : ℕ

/-- One more occurrence of [1]. Source: blueprint TR2--TR4 finite data
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Vertex.shift {A : Type a} (x : Vertex A) : Vertex A := ⟨x.index, x.shifts + 1⟩

/-- Iterated [1], retaining parentheses and the zero-iteration identity literally.
Source: blueprint repeated shifts (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def iterShift {D : Type u} [Category.{v} D] [HasShift D ℤ] (K : D) : ℕ → D
  | 0 => K
  | n + 1 => (shiftFunctor D (1 : ℤ)).obj (iterShift K n)

/-- Typed terms in the specified arrows and the permitted operations. Each term is finite.
Source: blueprint TR2--TR4 finite equations
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
inductive Expr {A : Type a} {B : Type b} (s t : B → Vertex A) :
    Vertex A → Vertex A → Type (max a b)
  | arrow (k : B) : Expr s t (s k) (t k)
  | id (x : Vertex A) : Expr s t x x
  | zero (x y : Vertex A) : Expr s t x y
  | comp {x y z : Vertex A} : Expr s t x y → Expr s t y z → Expr s t x z
  | add {x y : Vertex A} : Expr s t x y → Expr s t x y → Expr s t x y
  | neg {x y : Vertex A} : Expr s t x y → Expr s t x y
  | shift {x y : Vertex A} : Expr s t x y → Expr s t x.shift y.shift

/-- Evaluation uses the stated shift identifications: sigma_X, then u[1], then
sigma_Y inverse. Source: blueprint common-stage shift formula
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Expr.eval {A : Type a} {B : Type b} {s t : B → Vertex A}
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    (V : Vertex A → D) (sigma : ∀ x : Vertex A, V x.shift ≅ (V x)⟦(1 : ℤ)⟧)
    (f : ∀ k : B, V (s k) ⟶ V (t k)) :
    {x y : Vertex A} → Expr s t x y → (V x ⟶ V y)
  | _, _, .arrow k => f k
  | _, _, .id x => 𝟙 (V x)
  | _, _, .zero _ _ => 0
  | _, _, .comp p q => p.eval V sigma f ≫ q.eval V sigma f
  | _, _, .add p q => p.eval V sigma f + q.eval V sigma f
  | _, _, .neg p => -p.eval V sigma f
  | _, _, @Expr.shift _ _ _ _ x y p =>
      (sigma x).hom ≫ (shiftFunctor D (1 : ℤ)).map (p.eval V sigma f) ≫ (sigma y).inv

/-- A selected equation consists of parallel finite terms. Source: blueprint finite
asserted equalities (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Equation {A : Type a} {B : Type b} (s t : B → Vertex A) where
  source : Vertex A
  target : Vertex A
  lhs : Expr s t source target
  rhs : Expr s t source target

/-- A selected row uses three occurrences and terms ending in the shifted first occurrence.
Source: blueprint distinguished rows
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Row {A : Type a} {B : Type b} (s t : B → Vertex A) where
  first : Vertex A
  second : Vertex A
  third : Vertex A
  f : Expr s t first second
  i : Expr s t second third
  p : Expr s t third first.shift

/-- The triangle of a row, correcting its last arrow by sigma. Source: blueprint displayed
lifted row (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Row.triangle {A : Type a} {B : Type b} {s t : B → Vertex A}
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    (V : Vertex A → D) (sigma : ∀ x : Vertex A, V x.shift ≅ (V x)⟦(1 : ℤ)⟧)
    (f : ∀ k : B, V (s k) ⟶ V (t k)) (R : Row s t) : Triangle D :=
  Triangle.mk (R.f.eval V sigma f) (R.i.eval V sigma f)
    (R.p.eval V sigma f ≫ (sigma R.first).hom)

end CategoryTheory.PbcFiniteDiagram

namespace AlgebraicGeometry.Scheme

open CategoryTheory.PbcFiniteDiagram CategoryTheory.StageSystem

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The occurrence (E,K[n]) uses the original vertex's field, with no fresh object choice.
Source: blueprint vertex sharing (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertex {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out) (x : Vertex A) :
    PbcFiniteStagePairCategory l Ω T hDim.out hInv.out :=
  ⟨(X x.index).stage, iterShift (X x.index).obj x.shifts⟩

/-- The pair shift is literal on these occurrences. Source: blueprint common-stage shift
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertexShift {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out) (x : Vertex A) :
    pbcDiagramVertex l Ω T X x.shift ≅ (pbcDiagramVertex l Ω T X x)⟦(1 : ℤ)⟧ :=
  Iso.refl _

/-- The raw lift is T_(M/E)(K[n]), shared at every occurrence. Source: blueprint raw
representatives (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
abbrev pbcDiagramStageVertex {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) : pbcStageCategory l Ω T M :=
  (pbcDiagramVertex l Ω T X x).toStage (h x.index)

/-- The actual transition sigma, with its already prescribed normalization and coherence.
Source: blueprint scalar-extension comparisons
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramStageShift {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) :
    pbcDiagramStageVertex l Ω T X M h x.shift ≅
      (pbcDiagramStageVertex l Ω T X M h x)⟦(1 : ℤ)⟧ :=
  ((pbcScalarSystem l Ω T hDim.out hInv.out).T (h x.index)).commShiftIso
    (1 : ℤ) |>.app (iterShift (X x.index).obj x.shifts)

/-- Iterating the same sigma identifies the raw lift with the iterated shift of X_M.
Source: blueprint iterated sigma (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramIteratedSigma {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (j : A) : ∀ n : ℕ,
      pbcDiagramStageVertex l Ω T X M h ⟨j, n⟩ ≅
        iterShift ((X j).toStage (h j)) n
  | 0 => Iso.refl _
  | n + 1 => pbcDiagramStageShift l Ω T X M h ⟨j, n⟩ ≪≫
      (shiftFunctor (pbcStageCategory l Ω T M) (1 : ℤ)).mapIso
        (pbcDiagramIteratedSigma X M h j n)

/-- Canonical vertex recovery, represented by the identity after normalized unit
identifications. Source: blueprint final recovery clause
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertexIso {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) :
    pbcDiagramVertex l Ω T X x ≅
      ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).obj
        (pbcDiagramStageVertex l Ω T X M h x) :=
  (pbcScalarSystem l Ω T hDim.out hInv.out).isoToStage
    (pbcDiagramVertex l Ω T X x) (h x.index)

/-- Every finite configuration, including distinguished rows, descends simultaneously.
Source: blueprint main-20261015, thm-weil-pbc-verdier-axioms proof, TR2--TR4
(blueprint: lem-weil-pbc-distinguished-diagram-lifting).

Proof: (1) For each distinguished row, use common-stage distinguishedness to choose
an image distinguished triangle and a triangle isomorphism. Add its three components,
inverses, six inverse identities and three commuting equations to the finite data.
(2) Choose representatives for all arrows, retaining the chosen witness representatives.
Take a compositum containing their fields, the vertex and witness fields, and M0.
Transport by the associators; repeated vertices use the same scalar extension.
(3) Induct on the finite expressions. Composition, identities, addition, negatives and
zero commute with transport by commonStageCalculus. For shift the representative is
sigma_X followed by u[1] followed by sigma_Y inverse; iterating gives repeated shifts.
Use eventual equality for each true equation, then a compositum of their finitely many
witness fields, to make every equation hold simultaneously.
(4) Exact scalar extension takes each witness triangle to a distinguished triangle.
Associator/shift coherence identifies its last arrow with the transported raw arrow
followed by sigma, so the corrected witness row is distinguished at the final stage.
(5) The transported inverse equations and triangle squares make each witness isomorphism
an isomorphism of stage triangles; finite-stage TR1 gives every selected row.
(6) The canonical isoToStage maps recover every arrow and term. On a vertex their
representatives are identities after the normalized units; the shift formula gives
recovery of the corrected last arrows and all iterated shifted arrows. Empty finite
families only require the prescribed base stage. No Verdier axiom on the pair category
is used. -/
theorem pbcDistinguishedDiagramLifting
    {A : Type a} {B : Type b} {J : Type e} {R : Type r}
    [Finite A] [Finite B] [Finite J] [Finite R]
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (s t : B → Vertex A)
    (f : ∀ k : B, pbcDiagramVertex l Ω T X (s k) ⟶ pbcDiagramVertex l Ω T X (t k))
    (eqs : J → Equation s t) (rows : R → Row s t)
    (heqs : ∀ j : J,
      (eqs j).lhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f =
        (eqs j).rhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f)
    (hrows : ∀ k : R, pbcCommonStageDistinguished l Ω T
      ((rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f))
    (M0 : Padic.FiniteCoefficientFields l Ω) :
    ∃ (M : Padic.FiniteCoefficientFields l Ω) (_ : M0 ≤ M)
      (h : ∀ j : A, (X j).stage ≤ M)
      (u : ∀ k : B, pbcDiagramStageVertex l Ω T X M h (s k) ⟶
        pbcDiagramStageVertex l Ω T X M h (t k)),
      (∀ (x y : Vertex A) (p : Expr s t x y),
        PairCategory.mkHom (X := pbcDiagramVertex l Ω T X x)
          (Y := pbcDiagramVertex l Ω T X y) M (h x.index) (h y.index)
          (p.eval (pbcDiagramStageVertex l Ω T X M h) (pbcDiagramStageShift l Ω T X M h) u) =
        p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f) ∧
      (∀ j : J,
        (eqs j).lhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u =
          (eqs j).rhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u) ∧
      (∀ k : R,
        (rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u ∈ distTriang (pbcStageCategory l Ω T M)) ∧
      (∀ (x y : Vertex A) (p : Expr s t x y),
        (pbcDiagramVertexIso l Ω T X M h x).hom ≫
            ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).map
              (p.eval (pbcDiagramStageVertex l Ω T X M h)
                (pbcDiagramStageShift l Ω T X M h) u) =
          p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≫
            (pbcDiagramVertexIso l Ω T X M h y).hom) ∧
      (∀ k : R, ∃ q :
        (rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≅
          ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).mapTriangle.obj
            ((rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
              (pbcDiagramStageShift l Ω T X M h) u),
        q.hom.hom₁ = (pbcDiagramVertexIso l Ω T X M h (rows k).first).hom ∧
        q.hom.hom₂ = (pbcDiagramVertexIso l Ω T X M h (rows k).second).hom ∧
        q.hom.hom₃ = (pbcDiagramVertexIso l Ω T X M h (rows k).third).hom) := by
  sorry

end AlgebraicGeometry.Scheme
