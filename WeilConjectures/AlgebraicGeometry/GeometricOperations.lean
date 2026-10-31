/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricComparisonData

/-! # Geometric operation packages

Source: Weil blueprint, sec-trace-formula/sk-d-six (blueprint: sk-d-six).
The canonical duality maps and component coherence complete the specified
comparison data on the given finite-coefficient operations.
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
namespace GeometricOperationPackage

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ)
  (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)))

namespace Comparisons

variable {F l hl E n G} {A : ExceptionalAdjunctions F l hl E n G}
  (P : Comparisons F l hl E n G A)

/-- The exceptional identity comparison forced by the support identity and adjunction.
Source: sk-d-six, identity normalization (blueprint: sk-d-six). -/
def exceptionalId (X : TraceFormulaGeometricSpace F) :
    exceptionalCtf F l hl E n G (𝟙 X) ≅ 𝟭 (Ctf F l E n X) :=
  (A (𝟙 X)).rightAdjointUniq (Adjunction.id.ofNatIsoLeft (P.identity X).symm)

/-- The exceptional compositor forced by support composition and the given adjunctions.
Source: sk-d-six, dualizing composition coherence (blueprint: sk-d-six). -/
def exceptionalComp {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exceptionalCtf F l hl E n G (f ≫ g) ≅
      exceptionalCtf F l hl E n G g ⋙ exceptionalCtf F l hl E n G f :=
  (A (f ≫ g)).rightAdjointUniq
    (((A f).comp (A g)).ofNatIsoLeft (P.composition f g).symm)

/-- Verdier duality is the existing internal Hom into the specified dualizing object.
Source: sk-d-six, D_X K (blueprint: sk-d-six). -/
def dual (X : TraceFormulaGeometricSpace F) :
    (Ambient F l E n X)ᵒᵖ ⥤ Ambient F l E n X :=
  Prod.sectL (Ambient F l E n X)ᵒᵖ (P.omega X).obj ⋙
    finiteIntrinsicDerivedInternalHom l E X.obj.obj.left n

/-- Evaluation is the counit of the specified tensor/internal-Hom adjunction.
Source: sk-d-six, evaluation paragraph (blueprint: sk-d-six). -/
def evaluation (X : TraceFormulaGeometricSpace F) (K : Ambient F l E n X) :
    tensorObj F l E n X ((P.dual X).obj (op K)) K ⟶ (P.omega X).obj :=
  (closed F l E n X).evaluation K (P.omega X).obj

/-- The canonical biduality arrow, including the braiding before evaluation.
Source: sk-d-six, canonical biduality paragraph (blueprint: sk-d-six). -/
def biduality (X : TraceFormulaGeometricSpace F) (K : Ambient F l E n X) :
    K ⟶ (P.dual X).obj (op ((P.dual X).obj (op K))) :=
  (closed F l E n X).transpose K ((P.dual X).obj (op K)) (P.omega X).obj
    (((P.symmetric X).braiding K ((P.dual X).obj (op K))).hom ≫ P.evaluation X K)

/-- The actual product square, with the chosen fibre-product identification.
Source: sk-d-six, product square in the trace (blueprint: sk-d-six). -/
def productSquare (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left) : Square F where
  X := Y
  Y := TraceFormulaGeometricSpace.point F
  X' := Z
  Y' := X
  f := TraceFormulaGeometricSpace.structureMap Y
  g := TraceFormulaGeometricSpace.structureMap X
  g' := py
  f' := px
  cartesian := h

/-- The displayed trace: inverse product base change, the dualizing identification,
the given exceptional counit, and inverse monoidal unit, in this order.
Source: sk-d-six, formula for t (blueprint: sk-d-six). -/
def trace (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left) :
    (support F l hl E n G px).obj ((pull F l E n py).obj (P.omega Y).obj) ⟶
      unitObj F l E n X :=
  ((P.baseChange (productSquare X Y Z px py h)).inv.app (P.omega Y)).hom ≫
    (pull F l E n (TraceFormulaGeometricSpace.structureMap X)).map
      ((support F l hl E n G (TraceFormulaGeometricSpace.structureMap Y)).map
        (P.dualizing Y).hom.hom) ≫
    (pull F l E n (TraceFormulaGeometricSpace.structureMap X)).map
      ((A (TraceFormulaGeometricSpace.structureMap Y)).counit.app
        ⟨unitObj F l E n (TraceFormulaGeometricSpace.point F), P.unitDomain⟩).hom ≫
    (pullUnitIso F l E n (TraceFormulaGeometricSpace.structureMap X)
      (P.monoidal (TraceFormulaGeometricSpace.structureMap X))).inv

/-- The auxiliary exceptional adjunct, with finite-Tor membership supplied by the
actual tensor restriction and pullback stability. This is the specified braiding
followed by inverse projection, trace tensor identity, and left unitor.
Source: sk-d-six, formula for alpha_M (blueprint: sk-d-six). -/
def alpha (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left)
    (M : Ctf F l E n X) :
    (tensorCtf F l hl E n Z).obj
      ((pullCtf F l hl E n G px).obj M, (pullCtf F l hl E n G py).obj (P.omega Y)) ⟶
        (exceptionalCtf F l hl E n G px).obj M :=
  (A px).homEquiv _ M (ObjectProperty.homMk
    ((support F l hl E n G px).map
      ((P.symmetric Z).braiding ((pull F l E n px).obj M.obj)
        ((pull F l E n py).obj (P.omega Y).obj)).hom ≫
      (P.projection px ((pullCtf F l hl E n G py).obj (P.omega Y)) M).inv ≫
      (closed F l E n X).tensor.map
        (Prod.mkHom (P.trace X Y Z px py h) (𝟙 M.obj)) ≫
      ((closed F l E n X).monoidal.leftUnitor M.obj).hom))

/-- Compactly supported cohomology is the actual support image of the structure map.
Source: sk-d-six, R Gamma_c (blueprint: sk-d-six). -/
def compactlySupported (X : TraceFormulaGeometricSpace F) :
    Ctf F l E n X ⥤ Ctf F l E n (TraceFormulaGeometricSpace.point F) :=
  supportCtf F l hl E n G (TraceFormulaGeometricSpace.structureMap X)

/-- The specified external tensor product in intrinsic coefficient coordinates.
Source: sk-d-six, M boxtimes N (blueprint: sk-d-six). -/
def external {X Y Z : TraceFormulaGeometricSpace F} (px : Z ⟶ X) (py : Z ⟶ Y)
    (M : Ambient F l E n X) (N : Ambient F l E n Y) : Ambient F l E n Z :=
  tensorObj F l E n Z ((pull F l E n px).obj M) ((pull F l E n py).obj N)

/-- The canonical Kunneth--Verdier arrow, rather than a freely supplied comparison.
It is the tensor-Hom adjunct of reassociation, the pullback tensorator, pulled-back
evaluation, and the specified exceptional adjunct alpha.
Source: sk-d-six, final displayed composite (blueprint: sk-d-six). -/
def kunnethVerdier (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left)
    (M : Ctf F l E n X) (N : Ctf F l E n Y) :
    external px py M.obj ((P.dual Y).obj (op N.obj)) ⟶
      (finiteIntrinsicDerivedInternalHom l E Z.obj.obj.left n).obj
        (op ((pull F l E n py).obj N.obj),
          ((exceptionalCtf F l hl E n G px).obj M).obj) :=
  (closed F l E n Z).transpose _ _ _
    (((closed F l E n Z).monoidal.associator ((pull F l E n px).obj M.obj)
      ((pull F l E n py).obj ((P.dual Y).obj (op N.obj)))
      ((pull F l E n py).obj N.obj)).hom ≫
    (closed F l E n Z).tensor.map
      (Prod.mkHom (𝟙 ((pull F l E n px).obj M.obj))
        (pullTensorIso F l E n py (P.monoidal py) ((P.dual Y).obj (op N.obj)) N.obj).hom) ≫
    (closed F l E n Z).tensor.map
      (Prod.mkHom (𝟙 ((pull F l E n px).obj M.obj))
        ((pull F l E n py).map (P.evaluation Y N.obj))) ≫
    (P.alpha X Y Z px py h M).hom)

/-- Support transport along equality of maps; this is ordinary equality transport.
Source: sk-d-six, canonical identity/composition convention (blueprint: sk-d-six). -/
def supportCongr {X Y : TraceFormulaGeometricSpace F} {f g : X ⟶ Y} (e : f = g) :
    supportCtf F l hl E n G f ≅ supportCtf F l hl E n G g :=
  eqToIso (congrArg (supportCtf F l hl E n G) e)

/-- The package's coherence consists of equations of ordinary component maps.
No higher-categorical equality, pentagon beyond the stated axioms, or unbounded
exceptional adjoint is imposed. Source: sk-d-six, coherence paragraph
(blueprint: sk-d-six). -/
structure Coherence : Prop where
  /-- Right unit of support composition. -/
  rightUnit : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (K : Ctf F l E n X),
    (P.composition f (𝟙 Y)).hom.app K ≫
      (P.identity Y).hom.app ((supportCtf F l hl E n G f).obj K) =
      (supportCongr (G := G) (Category.comp_id f)).hom.app K
  /-- Left unit of support composition. -/
  leftUnit : ∀ {X Y : TraceFormulaGeometricSpace F} (f : X ⟶ Y)
    (K : Ctf F l E n X),
    (P.composition (𝟙 X) f).hom.app K ≫
      (supportCtf F l hl E n G f).map ((P.identity X).hom.app K) =
      (supportCongr (G := G) (Category.id_comp f)).hom.app K
  /-- At the identity the proper comparison uses the canonical direct identity. -/
  properIdentity : ∀ (X : TraceFormulaGeometricSpace F) (K : Ctf F l E n X),
    (P.proper (𝟙 X)).hom.app K =
      (P.identity X).hom.app K ≫ (directId F l hl E n G X).inv.app K
  /-- Normalization is exactly the exceptional identification followed by its mate. -/
  baseNormalization : P.normalization.hom =
    (P.dualizing (TraceFormulaGeometricSpace.point F)).hom ≫
      (P.exceptionalId (TraceFormulaGeometricSpace.point F)).hom.app
        ⟨unitObj F l E n (TraceFormulaGeometricSpace.point F), P.unitDomain⟩
  /-- Dualizing identity is the same adjoint identity comparison. -/
  dualizingIdentity : ∀ X : TraceFormulaGeometricSpace F,
    (P.dualizingComp (𝟙 X)).hom = (P.exceptionalId X).hom.app (P.omega X)
  /-- Ambient monoidal identity has the canonical identity unit comparison. -/
  monoidalIdentity : ∀ X : TraceFormulaGeometricSpace F,
    (pullUnitIso F l E n (𝟙 X) (P.monoidal (𝟙 X))).hom ≫
      (pullId F l E n X).hom.app (unitObj F l E n X) = 𝟙 _
  /-- Proper comparisons commute with the canonical direct compositor. -/
  properComposition : ∀ {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.hom.hom.left] [IsProper g.hom.hom.left] (K : Ctf F l E n X),
    (@P.proper X Z (f ≫ g)
      (inferInstanceAs (IsProper (f.hom.hom.left ≫ g.hom.hom.left)))).hom.app K ≫
      (directComp F l hl E n G f g).hom.app K =
      (P.composition f g).hom.app K ≫
        (supportCtf F l hl E n G g).map ((P.proper f).hom.app K) ≫
        (P.proper g).hom.app ((directCtf F l hl E n f).obj K)
  /-- Dualizing composition uses the adjoint support compositor. -/
  dualizingComposition : ∀ {X Y Z : TraceFormulaGeometricSpace F} (f : X ⟶ Y) (g : Y ⟶ Z),
    (P.dualizingComp (f ≫ g)).hom =
      (P.exceptionalComp f g).hom.app (P.omega Z) ≫
        (exceptionalCtf F l hl E n G f).map (P.dualizingComp g).hom ≫
        (P.dualizingComp f).hom
  /-- Base change respects vertical composition, component by component. -/
  baseChangeVertical : ∀ (X Y Z X' Y' Z' : TraceFormulaGeometricSpace F)
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : Z' ⟶ Z)
    (h₁ : ChosenCartesianSquare x.hom.hom.left f'.hom.hom.left
      f.hom.hom.left y.hom.hom.left)
    (h₂ : ChosenCartesianSquare y.hom.hom.left g'.hom.hom.left
      g.hom.hom.left z.hom.hom.left)
    (h₃ : ChosenCartesianSquare x.hom.hom.left (f' ≫ g').hom.hom.left
      (f ≫ g).hom.hom.left z.hom.hom.left) (K : Ctf F l E n X),
    (P.baseChange ⟨X, Z, X', Z', f ≫ g, z, x, f' ≫ g', h₃⟩).hom.app K ≫
      (P.composition f' g').hom.app ((pullCtf F l hl E n G x).obj K) =
    (pullCtf F l hl E n G z).map ((P.composition f g).hom.app K) ≫
      (P.baseChange ⟨Y, Z, Y', Z', g, z, y, g', h₂⟩).hom.app
        ((supportCtf F l hl E n G f).obj K) ≫
      (supportCtf F l hl E n G g').map
        ((P.baseChange ⟨X, Y, X', Y', f, y, x, f', h₁⟩).hom.app K)

end Comparisons
end GeometricOperationPackage

/-- A geometric operation package on the given coefficient setup and six operations.
Its data are the five displayed types of comparison, with precisely the component
coherence, and invertibility of the canonical evaluation and Kunneth--Verdier maps.
All schemes are separated finite-type schemes over the fixed algebraically closed
finite-field base. Hence every structure map and every morphism is compactifiable;
quantifying over all chosen product squares is equivalent to using fibre products.
Source: current blueprint sec-trace-formula/sk-d-six, and the reviewed DAG's explicit
D^b_ctf-domain and canonical-map clarifications (blueprint: sk-d-six). -/
structure GeometricOperations
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    (G : TraceFormulaCoefficientSetup F l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)))
    (A : GeometricOperationPackage.ExceptionalAdjunctions F l hl E n G)
    where
  /-- The specified comparisons on the given operations. -/
  comparisons : GeometricOperationPackage.Comparisons F l hl E n G A
  /-- Exactly the identity, composition and vertical base-change equations. -/
  coherence : comparisons.Coherence
  /-- The evaluation-adjoint biduality arrow is invertible on D^b_ctf. -/
  biduality : ∀ (X : TraceFormulaGeometricSpace F)
    (K : GeometricOperationPackage.Ctf F l E n X), IsIso (comparisons.biduality X K.obj)
  /-- Over this field base all geometric schemes are quasi-compact and compactifiable.
  The arrow is the displayed trace/evaluation adjunct, not another comparison. -/
  kunnethVerdier : ∀ (X Y Z : TraceFormulaGeometricSpace F) (px : Z ⟶ X) (py : Z ⟶ Y)
    (h : ChosenCartesianSquare py.hom.hom.left px.hom.hom.left
      (TraceFormulaGeometricSpace.structureMap Y).hom.hom.left
      (TraceFormulaGeometricSpace.structureMap X).hom.hom.left)
    (M : GeometricOperationPackage.Ctf F l E n X)
    (N : GeometricOperationPackage.Ctf F l E n Y),
    IsIso (comparisons.kunnethVerdier X Y Z px py h M N)

end WeilConjectures
