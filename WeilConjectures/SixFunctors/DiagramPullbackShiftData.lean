/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import WeilConjectures.Algebra.Homology.TotalTensorSignedCoherence
public import WeilConjectures.AlgebraicGeometry.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Simultaneous pullback, tensor and shift models on strict systems

Source: blueprint, sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
maps-used sentence; Stacks 06YS, 0G7E, 07A4, 0FPQ and 0FPT; More on Algebra, 0FNH.
(blueprint: def-pur-diagram-pullback-shift-data).

All module categories are the existing modules on the entire sequence site. The
presentation fields below fix actual maps by section and resolving normalizations.
They are conclusions of the existence theorem, never hypotheses on the ring tower.

## Main definitions

* `Models`: simultaneous presentations of the specified operations on ring diagrams.
* `Models.Coherence`: their resolving, chain and intrinsic derived shift identities.

## Main statements

* The existence and coherence theorems are in `DiagramPullbackMonoidalShiftModels`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open SheafOfModules.DerivedTensorConstraints

namespace WeilConjectures.DiagramPullbackShift

variable (A : ℕ → CommRingCat.{u + 1}) (δ : ∀ n : ℕ, A (n + 1) ⟶ A n)

/-- The given constant ring tower on W, with no flatness assumption on its maps.
Source: Zheng Construction 4.1; Stacks 0941
(blueprint: def-pur-diagram-pullback-shift-data). -/
def rings (W : Scheme.{u}) (n : ℕ) : Sheaf (ProEt.topology W) CommRingCat.{u + 1} :=
  letI : HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u} W
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj (A n)

/-- The actual constant-sheaf images of the adjacent coefficient homomorphisms.
Source: Zheng Construction 4.1
(blueprint: def-pur-diagram-pullback-shift-data). -/
def transitions (W : Scheme.{u}) (n : ℕ) : rings A W (n + 1) ⟶ rings A W n :=
  letI : HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u} W
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map (δ n)

/-- B_bullet on the simultaneous vertical sequence site, using the dependency's construction.
Source: Zheng Construction 4.1
(blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev ring (W : Scheme.{u}) :=
  SemilinearSections.systemRing (ProEt.topology W) (rings A W) (transitions A δ W)

/-- The ordinary module-sheaf category of strict semilinear systems, not derived diagrams.
Source: lem-coef-semilinear-derived-sections
(blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev Modules (W : Scheme.{u}) := SheafOfModules.DerivedTensorConstraints.Modules (ring A δ W)

/-- All unbounded integer-indexed cochain complexes of strict systems.
Source: Stacks 05RU (blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev Complex (W : Scheme.{u}) := CochainComplex (Modules A δ W) ℤ

/-- The ordinary unbounded localization, at the standard localization universe.
Source: Stacks 05RU (blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev Derived (W : Scheme.{u}) := SemilinearSections.DS
  (ProEt.topology W) (rings A W) (transitions A δ W)

/-- The fixed K-flat tensor, with the dependency's actual representative comparison.
Source: Stacks 06YU (blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev tensor (W : Scheme.{u}) : Derived A δ W × Derived A δ W ⥤ Derived A δ W :=
  SheafOfModules.DerivedTensorConstraints.tensor (ring A δ W)

/-- The native ring complex in degree zero, the tensor unit of cochain complexes.
Source: Stacks 0FPQ (blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev unitComplex (W : Scheme.{u}) : Complex A δ W :=
  @MonoidalCategoryStruct.tensorUnit (Complex A δ W) _
    (complexMonoidalStruct (ring A δ W))

/-- An adjunction presentation of actual system inverse image. The right adjoints are
fixed on the sequence site, and rho has the canonical constant-ring component at every
index. Thus the presentation is the geometric inverse image for v, not a free exact map.
Source: Stacks 03D2, 0941 and 07A4
(blueprint: def-pur-diagram-pullback-shift-data). -/
structure Pullback {X Y : Scheme.{u}} (v : X ⟶ Y) where
  rho : ring A δ Y ⟶
    ((integralComparisonSequenceBaseChange v).sheafPushforwardContinuous
      CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X))).obj (ring A δ X)
  rho_component : ∀ (n : ℕ) (U : Y.ProEt),
    rho.hom.app (op (n, U)) = (coefficientProEtaleDirectRingMap.{u, u} v (A n)).hom.app (op U)
  geometric : RingedPullback.{u + 1, u + 1, u, u + 1, u} (ring A δ Y) (ring A δ X)
  rightSets : geometric.uPush =
    (integralComparisonSequenceBaseChange v).sheafPushforwardContinuous (Type (u + 1))
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X))
  rightModules : geometric.V = SheafOfModules.pushforward.{u + 1}
    (F := integralComparisonSequenceBaseChange v)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := SemilinearSections.ring _ (ring A δ Y))
    (R := SemilinearSections.ring _ (ring A δ X))
    ⟨Functor.whiskerRight rho.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  [limits : PreservesFiniteLimits geometric.L]
  [colimits : PreservesFiniteColimits geometric.L]
  comparison : Comparison.{u + 1, u + 1, u, u + 1, u} geometric
  unit_normalization : ∀ M : Modules A δ Y,
    HEq ((underlying (ring A δ Y)).map (geometric.moduleAdj.unit.app M))
      (geometric.adj.unit.app ((underlying (ring A δ Y)).obj M) ≫
        geometric.uPush.map
          (geometric.I.moduleUnderlying.inv.app M ≫ comparison.q M))

attribute [instance] Pullback.limits Pullback.colimits

/-- The exact termwise-localized inverse image of the preceding geometric presentation.
Source: Stacks 015F (blueprint: def-pur-diagram-pullback-shift-data). -/
abbrev Pullback.derived {X Y : Scheme.{u}} {v : X ⟶ Y} (P : Pullback A δ v) :
    Derived A δ Y ⥤ Derived A δ X := P.geometric.L.mapDerivedCategory

/-- The specified two-shift, associator and symmetry constraints, with the existing
representative-square predicate, and action unitors normalized on the same models.
Source: Stacks 0FPQ, 0FPT (blueprint: def-pur-diagram-pullback-shift-data). -/
structure TensorConstraints (W : Scheme.{u}) where
  shift : ∀ a b : ℤ, shiftedSource (ring A δ W) a b ≅ shiftedTarget (ring A δ W) a b
  associator : leftAssociated (ring A δ W) ≅ rightAssociated (ring A δ W)
  symmetry : tensor A δ W ≅ swapped (ring A δ W)
  normalized : IsNormalized (ring A δ W) shift associator symmetry
  unit_resolving : resolvingComplex (ring A δ W) (unitComplex A δ W)
  left : (Functor.curry.obj (tensor A δ W)).obj
    (DerivedCategory.Q.obj (unitComplex A δ W)) ≅ 𝟭 (Derived A δ W)
  right : (Functor.curry.obj (tensor A δ W)).flip.obj
    (DerivedCategory.Q.obj (unitComplex A δ W)) ≅ 𝟭 (Derived A δ W)
  left_model : ∀ E : Model (ring A δ W),
    (representative (ring A δ W) ⟨unitComplex A δ W, unit_resolving⟩ E).hom ≫
        left.hom.app (DerivedCategory.Q.obj E.obj) =
      DerivedCategory.Q.map
        (@MonoidalCategory.leftUnitor (Complex A δ W) _
          (complexMonoidalStruct (ring A δ W)) E.obj).hom
  right_model : ∀ E : Model (ring A δ W),
    (representative (ring A δ W) E ⟨unitComplex A δ W, unit_resolving⟩).hom ≫
        right.hom.app (DerivedCategory.Q.obj E.obj) =
      DerivedCategory.Q.map
        (@MonoidalCategory.rightUnitor (Complex A δ W) _
          (complexMonoidalStruct (ring A δ W)) E.obj).hom

/-- Extract a shift from the first input, inserting only the canonical zero shift in the
other slot. Source: Stacks 0FNH
(blueprint: def-pur-diagram-pullback-shift-data). -/
def TensorConstraints.firstShift {W : Scheme.{u}} (T : TensorConstraints A δ W)
    (a : ℤ) (M N : Derived A δ W) :
    (tensor A δ W).obj (M⟦a⟧, N) ≅ ((tensor A δ W).obj (M, N))⟦a⟧ :=
  (tensor A δ W).mapIso
      (Iso.prod (Iso.refl _) ((shiftFunctorZero (Derived A δ W) ℤ).app N).symm) ≪≫
    (T.shift a 0).app (M, N) ≪≫
    eqToIso (congrArg (fun n : ℤ ↦ ((tensor A δ W).obj (M, N))⟦n⟧) (add_zero a))

/-- Extract a shift from the second input, with the prescribed coefficient (-1)^(bp).
Source: Stacks 0FNH (blueprint: def-pur-diagram-pullback-shift-data). -/
def TensorConstraints.secondShift {W : Scheme.{u}} (T : TensorConstraints A δ W)
    (b : ℤ) (M N : Derived A δ W) :
    (tensor A δ W).obj (M, N⟦b⟧) ≅ ((tensor A δ W).obj (M, N))⟦b⟧ :=
  (tensor A δ W).mapIso
      (Iso.prod ((shiftFunctorZero (Derived A δ W) ℤ).app M).symm (Iso.refl _)) ≪≫
    (T.shift 0 b).app (M, N) ≪≫
    eqToIso (congrArg (fun n : ℤ ↦ ((tensor A δ W).obj (M, N))⟦n⟧) (zero_add b))

/-- The derived tensor constraints commute with every selected occurrence of a shift.
The simultaneous equations imply the three associator slots and the two permuted
symmetry slots. CommShift supplies precisely the zero and addition laws in each slot.
Source: Stacks 0FNH, 0FPQ and 0FPT
(blueprint: def-pur-diagram-pullback-shift-data). -/
structure TensorCoherence {W : Scheme.{u}} (T : TensorConstraints A δ W) : Prop where
  shift_laws :
    ∃ (s₁ : ∀ N : Derived A δ W, ((Functor.curry.obj (tensor A δ W)).flip.obj N).CommShift ℤ)
      (s₂ : ∀ M : Derived A δ W, ((Functor.curry.obj (tensor A δ W)).obj M).CommShift ℤ),
      (∀ (M N : Derived A δ W) (r : ℤ),
        (Functor.commShiftIso _ (self := s₁ N) r).app M = T.firstShift A δ r M N) ∧
      (∀ (M N : Derived A δ W) (r : ℤ),
        (Functor.commShiftIso _ (self := s₂ M) r).app N = T.secondShift A δ r M N)
  extraction : ∀ (M N : Derived A δ W) (a b : ℤ),
    (T.shift a b).app (M, N) =
      T.secondShift A δ b (M⟦a⟧) N ≪≫
        (shiftFunctor _ b).mapIso (T.firstShift A δ a M N) ≪≫
        ((shiftFunctorAdd (Derived A δ W) a b).app ((tensor A δ W).obj (M, N))).symm
  interchange : ∀ (M N : Derived A δ W) (a b : ℤ),
    (T.shift a b).hom.app (M, N) =
      (a * b).negOnePow • ((T.firstShift A δ a M (N⟦b⟧)).hom ≫
        (T.secondShift A δ b M N).hom⟦a⟧' ≫
        (shiftFunctorAdd' (Derived A δ W) b a (a + b) (add_comm b a)).inv.app
          ((tensor A δ W).obj (M, N)))
  associativity : ∀ (M N H : Derived A δ W) (a b c : ℤ),
    (tensor A δ W).map (Prod.mkHom ((T.shift a b).hom.app (M, N)) (𝟙 (H⟦c⟧))) ≫
        (T.shift (a + b) c).hom.app ((tensor A δ W).obj (M, N), H) ≫
        (T.associator.hom.app ((M, N), H))⟦(a + b) + c⟧' =
      T.associator.hom.app ((M⟦a⟧, N⟦b⟧), H⟦c⟧) ≫
        (tensor A δ W).map (Prod.mkHom (𝟙 (M⟦a⟧)) ((T.shift b c).hom.app (N, H))) ≫
        (T.shift a (b + c)).hom.app (M, (tensor A δ W).obj (N, H)) ≫
        eqToHom (congrArg
          (fun n : ℤ ↦ ((tensor A δ W).obj (M, (tensor A δ W).obj (N, H)))⟦n⟧)
          (add_assoc a b c).symm)
  symmetry : ∀ (M N : Derived A δ W) (a b : ℤ),
    (T.shift a b).hom.app (M, N) ≫ (T.symmetry.hom.app (M, N))⟦a + b⟧' =
      (a * b).negOnePow • (T.symmetry.hom.app (M⟦a⟧, N⟦b⟧) ≫
        (T.shift b a).hom.app (N, M) ≫
        eqToHom (congrArg (fun n : ℤ ↦ ((tensor A δ W).obj (N, M))⟦n⟧) (add_comm b a)))
  left_unitor : ∀ (M : Derived A δ W) (r : ℤ),
    T.left.hom.app (M⟦r⟧) =
      (T.secondShift A δ r (DerivedCategory.Q.obj (unitComplex A δ W)) M).hom ≫
        (T.left.hom.app M)⟦r⟧'
  right_unitor : ∀ (M : Derived A δ W) (r : ℤ),
    T.right.hom.app (M⟦r⟧) =
      (T.firstShift A δ r M (DerivedCategory.Q.obj (unitComplex A δ W))).hom ≫
        (T.right.hom.app M)⟦r⟧'

/-- The entire chain-level signed tensor calculation, in the existing module monoidal
structure, including the two displayed exponent identities for all integers.
Source: Stacks 0FPQ, More on Algebra 0FNH
(blueprint: def-pur-diagram-pullback-shift-data). -/
def ChainSignedCoherence (W : Scheme.{u}) : Prop :=
  letI := SheafOfModules.monoidalCategory (ring A δ W)
  CategoryTheory.RingedDerivedNative.TotalTensorSignedCoherence (A := Modules A δ W)

/-- The comparison preserves each total bidegree and commutes with the signed two-shift
map before localization. Every arrow is already a morphism of whole strict systems.
Source: Stacks 07A4, 0FNH
(blueprint: def-pur-diagram-pullback-shift-data). -/
def ChainPullbackCoherence {X Y : Scheme.{u}} {v : X ⟶ Y} (P : Pullback A δ v) : Prop :=
  letI := SheafOfModules.monoidalCategory (ring A δ Y)
  letI := SheafOfModules.monoidalCategory (ring A δ X)
  letI := complexMonoidal (ring A δ Y)
  letI := complexMonoidalStruct (ring A δ Y)
  letI := complexMonoidal (ring A δ X)
  letI := complexMonoidalStruct (ring A δ X)
  (∀ (E F : Complex A δ Y) (p q n : ℤ) (h : p + q = n),
    P.geometric.L.map (HomologicalComplex.ιTensorObj E F p q n h) ≫
        (comparison P.geometric P.comparison E F).hom.f n =
      (P.comparison.mu (E.X p) (F.X q)).hom ≫
        HomologicalComplex.ιTensorObj ((pull P.geometric).obj E)
          ((pull P.geometric).obj F) p q n h) ∧
  (∀ (E F : Complex A δ Y) (a b : ℤ),
    (comparison P.geometric P.comparison (E⟦a⟧) (F⟦b⟧)).hom ≫
        (((pull P.geometric).commShiftIso a).hom.app E ⊗ₘ
          ((pull P.geometric).commShiftIso b).hom.app F) ≫
        (chainShift (ring A δ X) ((pull P.geometric).obj E)
          ((pull P.geometric).obj F) a b).hom =
      (pull P.geometric).map (chainShift (ring A δ Y) E F a b).hom ≫
        ((pull P.geometric).commShiftIso (a + b)).hom.app (E ⊗ F) ≫
        (comparison P.geometric P.comparison E F).hom⟦a + b⟧')

/-- A derived pullback/tensor comparison with its actual resolving normalization.
The normalization uses the recorded representative isomorphisms and total comparison.
Source: Stacks 07A4, 0FPT
(blueprint: def-pur-diagram-pullback-shift-data). -/
structure TensorPullback {X Y : Scheme.{u}} {v : X ⟶ Y} (P : Pullback A δ v) where
  iso : tensor A δ Y ⋙ P.derived A δ ≅
    ((P.derived A δ).prod (P.derived A δ)) ⋙ tensor A δ X
  preserves_resolving : ∀ E : Model (ring A δ Y),
    resolvingComplex (ring A δ X) ((pull P.geometric).obj E.obj)
  normalized : ∀ E F : Model (ring A δ Y),
    (P.derived A δ).map (representative (ring A δ Y) E F).hom ≫
        iso.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
        (tensor A δ X).map
          (Prod.mkHom (P.geometric.L.mapDerivedCategoryFactors.hom.app E.obj)
            (P.geometric.L.mapDerivedCategoryFactors.hom.app F.obj)) =
      P.geometric.L.mapDerivedCategoryFactors.hom.app
          ((SheafOfModules.KFlatFixedTensor.totalTensor (ring A δ Y)).obj E.obj |>.obj F.obj) ≫
        DerivedCategory.Q.map (comparison P.geometric P.comparison E.obj F.obj).hom ≫
        (representative (ring A δ X)
          ⟨(pull P.geometric).obj E.obj, preserves_resolving E⟩
          ⟨(pull P.geometric).obj F.obj, preserves_resolving F⟩).hom

/-- The two-shift square for the normalized derived pullback/tensor isomorphism.
Source: Stacks 07A4 and 0FNH
(blueprint: def-pur-diagram-pullback-shift-data). -/
def TensorPullback.ShiftCoherence {X Y : Scheme.{u}} {v : X ⟶ Y}
    {P : Pullback A δ v} (mu : TensorPullback A δ P)
    (TY : TensorConstraints A δ Y) (TX : TensorConstraints A δ X) : Prop :=
  ∀ (M N : Derived A δ Y) (a b : ℤ),
    mu.iso.hom.app (M⟦a⟧, N⟦b⟧) ≫
        (tensor A δ X).map
          (Prod.mkHom (((P.derived A δ).commShiftIso a).hom.app M)
            (((P.derived A δ).commShiftIso b).hom.app N)) ≫
        (TX.shift a b).hom.app ((P.derived A δ).obj M, (P.derived A δ).obj N) =
      (P.derived A δ).map ((TY.shift a b).hom.app (M, N)) ≫
        ((P.derived A δ).commShiftIso (a + b)).hom.app ((tensor A δ Y).obj (M, N)) ≫
        (mu.iso.hom.app (M, N))⟦a + b⟧'

/-- The unsigned action unitors on total models, including their coefficient-one formulas
on the summands with degree-zero ring input. Source: Stacks 0FPQ
(blueprint: def-pur-diagram-pullback-shift-data). -/
def ChainUnitCoherence (W : Scheme.{u}) : Prop :=
  letI := SheafOfModules.monoidalCategory (ring A δ W)
  letI := complexMonoidal (ring A δ W)
  letI := complexMonoidalStruct (ring A δ W)
  ∀ (E : Complex A δ W) (p : ℤ),
    HomologicalComplex.ιTensorObj (unitComplex A δ W) E 0 p p (zero_add p) ≫
        (λ_ E).hom.f p =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (𝟙_ (Modules A δ W))).hom ▷ E.X p) ≫ (λ_ (E.X p)).hom ∧
    HomologicalComplex.ιTensorObj E (unitComplex A δ W) p 0 p (add_zero p) ≫
        (ρ_ E).hom.f p =
      (E.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (𝟙_ (Modules A δ W))).hom) ≫ (ρ_ (E.X p)).hom

/-- Simultaneous presentations of the specified operations on all the actual ringed
sequence sites. The right-module compositor is fixed on sections by the scheme
fiber-product isomorphism; the dependency's scalarAssociation fixes its left mate.
Source: Stacks 03D8, 07A4, 0FPQ and 0FPT; blueprint maps-used sentence
(blueprint: def-pur-diagram-pullback-shift-data). -/
structure Models where
  constraints : ∀ W : Scheme.{u}, TensorConstraints A δ W
  inverseImage : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y), Pullback A δ v
  tensorPullback : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y),
    TensorPullback A δ (inverseImage v)
  compose : ∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z),
    CompositePresentation.{u + 1, u + 1, u, u + 1, u, u + 1, u}
      (inverseImage w).geometric (inverseImage v).geometric (inverseImage (v ≫ w)).geometric
      (inverseImage w).comparison (inverseImage v).comparison (inverseImage (v ≫ w)).comparison
  compose_sections : ∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z)
    (N : Modules A δ X) (n : ℕ) (U : Z.ProEt),
    HEq (((compose v w).rightModules.hom.app N).val.app (op (n, U)))
      (N.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) v w).inv.app U)).op)

/-- The specified derived compositor is the localization of its ordinary adjunction mate,
with the canonical derived-composition identification. Its inverse is its actual inverse.
Source: Stacks 015F, 03D8 (blueprint: def-pur-diagram-pullback-shift-data). -/
def Models.compositor (S : Models A δ) {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z) :
    (S.inverseImage (v ≫ w)).derived A δ ≅
      (S.inverseImage w).derived A δ ⋙ (S.inverseImage v).derived A δ :=
  Functor.mapDerivedCategoryNatIso
      (compositionModule (S.inverseImage w).geometric (S.inverseImage v).geometric
        (S.inverseImage (v ≫ w)).geometric (S.compose v w).rightModules) ≪≫
    Functor.mapDerivedCategoryCompIso (S.inverseImage w).geometric.L
      (S.inverseImage v).geometric.L

/-- The ordinary compositor's shifted degree-p map is its ordinary degree-(p+r) map,
for both orientations. All these maps are strict-system maps before localization.
Source: Stacks 015F, 03D8; explicit termwise comparison in the node's proof step 2
(blueprint: def-pur-diagram-pullback-shift-data). -/
def Models.CompositorModels (S : Models A δ) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z)
    (E : Complex A δ Z) (r p : ℤ),
    HEq ((composition (S.inverseImage w).geometric (S.inverseImage v).geometric
        (S.inverseImage (v ≫ w)).geometric (S.compose v w) (E⟦r⟧)).hom.f p)
      ((compositionModule (S.inverseImage w).geometric (S.inverseImage v).geometric
        (S.inverseImage (v ≫ w)).geometric (S.compose v w).rightModules).hom.app
          (E.X (p + r))) ∧
    HEq ((composition (S.inverseImage w).geometric (S.inverseImage v).geometric
        (S.inverseImage (v ≫ w)).geometric (S.compose v w) (E⟦r⟧)).inv.f p)
      ((compositionModule (S.inverseImage w).geometric (S.inverseImage v).geometric
        (S.inverseImage (v ≫ w)).geometric (S.compose v w).rightModules).inv.app
          (E.X (p + r)))

/-- The derived compositor and its inverse commute with the specified termwise shifts.
Source: Stacks 015F, 03D8 (blueprint: def-pur-diagram-pullback-shift-data). -/
def Models.CompositorShifts (S : Models A δ) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z),
    NatTrans.CommShift (S.compositor A δ v w).hom ℤ ∧
      NatTrans.CommShift (S.compositor A δ v w).inv ℤ

/-- Equality of scheme arrows gives the ordinary equality identification in every degree,
including shifts, and its localization has exactly the specified shift square. This also
covers equalities between composites and all their inverses, by replacing e with e.symm.
Source: Stacks 015F; node proof step 2
(blueprint: def-pur-diagram-pullback-shift-data). -/
def Models.EqualityShifts (S : Models A δ) : Prop :=
  ∀ {X Y : Scheme.{u}} (v w : X ⟶ Y) (e : v = w),
    (∀ (E : Complex A δ Y) (r p : ℤ),
      HEq ((NatTrans.mapHomologicalComplex
          (eqToHom (congrArg (fun f ↦ (S.inverseImage f).geometric.L) e)) (.up ℤ)).app
            (E⟦r⟧) |>.f p)
        ((eqToHom (congrArg (fun f ↦ (S.inverseImage f).geometric.L) e)).app
          (E.X (p + r)))) ∧
    ∀ (M : Derived A δ Y) (r : ℤ),
      (eqToHom (congrArg (fun f ↦ (S.inverseImage f).derived A δ) e)).app (M⟦r⟧) ≫
          (((S.inverseImage w).derived A δ).commShiftIso r).hom.app M =
        (((S.inverseImage v).derived A δ).commShiftIso r).hom.app M ≫
          ((eqToHom (congrArg (fun f ↦ (S.inverseImage f).derived A δ) e)).app M)⟦r⟧'

/-- All resolving and shift assertions, intrinsically in D(S_W). The tensor and shift
closures are the dependency's actual totalModel and shiftModel. No evaluated map equality
is used. Source: Stacks 06YS, 0G7E, 07A4, 0FPQ, 0FPT and 0FNH
(blueprint: def-pur-diagram-pullback-shift-data). -/
structure Models.Coherence (S : Models A δ) : Prop where
  resolutions : ∀ (W : Scheme.{u}) (n : ℕ) (E : Fin n → Complex A δ W),
    ∃ (P : Fin n → Model (ring A δ W)) (q : ∀ i : Fin n, (P i).obj ⟶ E i),
      ∀ i : Fin n, QuasiIso (q i)
  chain_signed : ∀ W : Scheme.{u}, ChainSignedCoherence A δ W
  chain_unit : ∀ W : Scheme.{u}, ChainUnitCoherence A δ W
  tensor_shifts : ∀ W : Scheme.{u}, TensorCoherence A δ (S.constraints W)
  chain_pullback : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y),
    ChainPullbackCoherence A δ (S.inverseImage v)
  derived_pullback : ∀ {X Y : Scheme.{u}} (v : X ⟶ Y),
    (S.tensorPullback v).ShiftCoherence A δ (S.constraints Y) (S.constraints X)
  compositor_models : S.CompositorModels A δ
  compositor_shifts : S.CompositorShifts A δ
  equality_shifts : S.EqualityShifts A δ

end WeilConjectures.DiagramPullbackShift
