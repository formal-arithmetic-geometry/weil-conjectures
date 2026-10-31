/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.KInjectiveTotalDerivedLinear
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.KInjectiveDerivedMapComputation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Derived functors act on global mapping complexes

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, second paragraph, the arrow labelled Ra_!
and its action on every H^i (blueprint: lem-sf-derived-functor-mapping-complex-action).
The structures specify the conclusion by its ordinary-cochain normalization. `CoeffRing`
and `coefficientDerivedEquivalence` implement the canonical coefficient transport back to
D(B). This avoids any equality between the coefficient and site universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe b v u w k c r s
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace CategoryTheory.DerivedMappingAction

variable (B : Type b) [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]

/-- A larger presentation of B, canonically equivalent to B by ULift.ringEquiv.
Source: size convention (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
abbrev CoeffRing := ULift.{v} B

/-- Coefficient modules in a common universe, without identifying ring and site universes.
Restriction along ULift.ringEquiv identifies this category with B-modules in that universe.
Source: size convention (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
abbrev CoeffModules := ModuleCat.{max b v} (CoeffRing.{b, v} B)

/-- Undo the harmless coefficient-ring lift, without lifting module carriers again.
Source: size convention and Stacks 0B6E
(blueprint: lem-sf-derived-functor-mapping-complex-action). -/
abbrev coefficientEquivalence : CoeffModules.{b, v} B ≌ ModuleCat.{max b v} B :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : CoeffRing.{b, v} B ≃+* B).symm

/-- The explicit identification of the coefficient derived category with D(B).
Its functor transports every action arrow to the ring B of the statement.
Source: size convention and Stacks 0B6E
(blueprint: lem-sf-derived-functor-mapping-complex-action). -/
abbrev coefficientDerivedEquivalence
    [HasDerivedCategory.{max b v} (ModuleCat.{max b v} B)] :
    DerivedCategory (CoeffModules.{b, v} B) ≌ DerivedCategory (ModuleCat.{max b v} B) :=
  (coefficientEquivalence.{b, v} B).mapDerivedCategory

/-- Ordinary direct-sum total tensor with its Koszul differential.
Source: Stacks 09L9 (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
abbrev ordinaryTensor :
    CochainComplex (CoeffModules.{b, v} B) ℤ ×
      CochainComplex (CoeffModules.{b, v} B) ℤ ⥤
      CochainComplex (CoeffModules.{b, v} B) ℤ :=
  Functor.uncurry.obj
    ((curriedTensor (CoeffModules.{b, v} B)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

variable {B}
variable (A : Type u) [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A]

/-- Specification of global derived Hom by linear cochains, the ordinary comparison,
composition, identities, shifts and their normalization. Inverting `comparison` for a
K-injective target gives precisely the single-resolution Hom model.
Source: Stacks 09L9, 070I and 0B6E, blueprint's Ra_! arrow
(blueprint: lem-sf-derived-functor-mapping-complex-action). -/
structure HomModel where
  ordinary : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤
    CochainComplex (CoeffModules.{b, v} B) ℤ
  degree : ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
    (ordinary.obj (op X, Y)).X n ≅ ModuleCat.of (CoeffRing.{b, v} B) (ULift.{b} (Cochain X Y n))
  differential : ∀ (X Y : CochainComplex A ℤ) (n m : ℤ)
      (x : (ordinary.obj (op X, Y)).X n),
    ((degree X Y m).hom ((ordinary.obj (op X, Y)).d n m x)).down =
      δ n m (((degree X Y n).hom x).down)
  ordinary_naturality : ∀ (X X' Y Y' : CochainComplex A ℤ) (f : X' ⟶ X) (g : Y ⟶ Y')
      (n p q : ℤ) (hpq : p + n = q) (x : (ordinary.obj (op X, Y)).X n),
    (((degree X' Y' n).hom ((ordinary.map (f.op, g)).f n x)).down).v p q hpq =
      f.f p ≫ (((degree X Y n).hom x).down).v p q hpq ≫ g.f q
  hom : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤
    DerivedCategory (CoeffModules.{b, v} B)
  comparison : ordinary ⋙ DerivedCategory.Q ⟶
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ hom
  resolved : ∀ (X I : CochainComplex A ℤ) [I.IsKInjective],
    IsIso (comparison.app (op X, I))
  ordinaryComp : ∀ X Y Z : CochainComplex A ℤ,
    (ordinaryTensor B).obj (ordinary.obj (op Y, Z), ordinary.obj (op X, Y)) ⟶
      ordinary.obj (op X, Z)
  ordinaryComp_apply : ∀ (X Y Z : CochainComplex A ℤ) (a d n : ℤ) (h : a + d = n)
      (g : (ordinary.obj (op Y, Z)).X a) (f : (ordinary.obj (op X, Y)).X d),
    ((degree X Z n).hom ((ordinaryComp X Y Z).f n
      (HomologicalComplex.ιTensorObj (ordinary.obj (op Y, Z))
        (ordinary.obj (op X, Y)) a d n h (TensorProduct.tmul (ULift.{v} B) g f)))).down =
      (((degree X Y d).hom f).down).comp (((degree Y Z a).hom g).down) ((add_comm d a).trans h)
  comp : ∀ P Q R : DerivedCategory A,
    hom.obj (op Q, R) ⊗ hom.obj (op P, Q) ⟶ hom.obj (op P, R)
  comp_normalization : ∀ X Y Z : CochainComplex A ℤ,
    (comparison.app (op Y, Z) ⊗ₘ comparison.app (op X, Y)) ≫
        comp (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) (DerivedCategory.Q.obj Z) =
      Functor.LaxMonoidal.μ DerivedCategory.Q (ordinary.obj (op Y, Z))
        (ordinary.obj (op X, Y)) ≫ DerivedCategory.Q.map (ordinaryComp X Y Z) ≫
          comparison.app (op X, Z)
  ordinaryUnit : ∀ X : CochainComplex A ℤ,
    (CochainComplex.singleFunctor (CoeffModules.{b, v} B) (0 : ℤ)).obj
      (ModuleCat.of (CoeffRing.{b, v} B) (ULift.{v} B)) ⟶
      ordinary.obj (op X, X)
  ordinaryUnit_apply : ∀ (X : CochainComplex A ℤ) (a : ULift.{v} B),
    ((degree X X 0).hom ((ordinaryUnit X).f 0 a)).down = a.down • Cochain.ofHom (𝟙 X)
  unit : ∀ P : DerivedCategory A,
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor (CoeffModules.{b, v} B) (0 : ℤ)).obj
      (ModuleCat.of (CoeffRing.{b, v} B) (ULift.{v} B))) ⟶ hom.obj (op P, P)
  unit_normalization : ∀ X : CochainComplex A ℤ,
    unit (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (ordinaryUnit X) ≫ comparison.app (op X, X)
  ordinaryShift : ∀ (X Y : CochainComplex A ℤ) (a : ℤ),
    ordinary.obj (op X, Y⟦a⟧) ≅ (ordinary.obj (op X, Y))⟦a⟧
  ordinaryShift_apply : ∀ (X Y : CochainComplex A ℤ) (a n : ℤ)
      (x : (ordinary.obj (op X, Y⟦a⟧)).X n),
    ((degree X Y (n + a)).hom
      (((ordinary.obj (op X, Y)).shiftFunctorObjXIso a n (n + a) rfl).hom
        ((ordinaryShift X Y a).hom.f n x))).down =
      (((degree X (Y⟦a⟧) n).hom x).down).rightUnshift (n + a) rfl
  shift : ∀ (P Q : DerivedCategory A) (a : ℤ),
    hom.obj (op P, Q⟦a⟧) ≅ (hom.obj (op P, Q))⟦a⟧
  shift_normalization : ∀ (X Y : CochainComplex A ℤ) (a : ℤ),
    comparison.app (op X, Y⟦a⟧) ≫
        hom.map (X := (op (DerivedCategory.Q.obj X), DerivedCategory.Q.obj (Y⟦a⟧)))
          (Y := (op (DerivedCategory.Q.obj X), (DerivedCategory.Q.obj Y)⟦a⟧))
          (𝟙 _, (DerivedCategory.Q.commShiftIso a).hom.app Y) ≫
        (shift (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) a).hom =
      DerivedCategory.Q.map (ordinaryShift X Y a).hom ≫
        (DerivedCategory.Q.commShiftIso a).hom.app (ordinary.obj (op X, Y)) ≫
        (comparison.app (op X, Y))⟦a⟧'
  cohomology : ∀ (P Q : DerivedCategory A) (n : ℤ),
    ((DerivedCategory.homologyFunctor (CoeffModules.{b, v} B) n).obj
      (hom.obj (op P, Q))) ≃+ (P ⟶ Q⟦n⟧)
  cohomology_normalization : ∀ (X Y : CochainComplex A ℤ) (n : ℤ) (f : X ⟶ Y⟦n⟧),
    ∃ x : (ordinary.obj (op X, Y)).cycles n,
      ((degree X Y n).hom ((ordinary.obj (op X, Y)).iCycles n x)).down =
          (Cocycle.equivHomShift f).val ∧
        cohomology (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) n
          ((DerivedCategory.homologyFunctor (CoeffModules.{b, v} B) n).map
            (comparison.app (op X, Y))
            (((DerivedCategory.homologyFunctorFactors (CoeffModules.{b, v} B) n).inv.app
              (ordinary.obj (op X, Y))) ((ordinary.obj (op X, Y)).homologyπ n x))) =
          DerivedCategory.Q.map f ≫ (DerivedCategory.Q.commShiftIso n).hom.app Y

/-- A separately derived linear functor with a specified universal comparison. Exact
termwise models are included through the unit-compatible isomorphism `iso`.
Source: Stacks 070K and 070Y (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
structure Step (A' : Type u) [Category.{v} A'] [Abelian A'] [Linear B A']
    [HasDerivedCategory.{w} A'] where
  original : A ⥤ A'
  additive : original.Additive
  linear : original.Linear B
  enough : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s
  derived : DerivedCategory A ⥤ DerivedCategory A'
  iso : @Functor.rightDerivedFunctorOfQuasiIsoResolutions _ _ _ _ _ _ _ _
    original additive enough ≅ derived
  commShift : derived.CommShift ℤ

attribute [instance] Step.additive Step.linear Step.commShift

variable {A}
variable {A' : Type u} [Category.{v} A'] [Abelian A'] [Linear B A']
  [HasDerivedCategory.{w} A']

/-- The recorded universal unit, transported to the specified model of RF.
Source: Stacks 070K (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Step.unit (e : Step (B := B) A A') :
    e.original.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ e.derived :=
  e.original.rightDerivedFunctorOfQuasiIsoResolutionsUnit e.enough ≫
    Functor.whiskerLeft DerivedCategory.Qh e.iso.hom

/-- The same universal unit on complexes, transported through quotientCompQhIso.
Source: Stacks 070K (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Step.complexUnit (e : Step (B := B) A A') (X : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj X) ⟶
      e.derived.obj (DerivedCategory.Q.obj X) :=
  (DerivedCategory.quotientCompQhIso A').inv.app
      ((e.original.mapHomologicalComplex (.up ℤ)).obj X) ≫
    e.unit.app ((HomotopyCategory.quotient A (.up ℤ)).obj X) ≫
    e.derived.map ((DerivedCategory.quotientCompQhIso A).hom.app X)

/-- Canonical shift normalization: the universal unit commutes with shifts.
Source: Stacks 070Y (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Step.HasCanonicalShift (e : Step (B := B) A A') : Prop :=
  NatTrans.CommShift e.unit ℤ

/-- Comparison RF(QI) to Q(FI), using the recorded resolution comparison at the identity.
Source: Stacks 070I (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Step.representativeIso (e : Step (B := B) A A')
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    e.derived.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj I) :=
  e.iso.symm.app (DerivedCategory.Q.obj I) ≪≫
    e.original.rightDerivedFunctorOfQuasiIsoResolutionsObjIso e.enough (𝟙 I)

variable {ι : Type k} (C : ι → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, Abelian (C i)] [∀ i, Linear B (C i)] [∀ i, HasDerivedCategory.{w} (C i)]

/-- Finite lists of separately derived functors, including the empty list.
Source: finite-composite clause (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
inductive Path : ι → ι → Type (max b u v w k) where
  | nil (i : ι) : Path i i
  | cons {i j l : ι} (e : Step (B := B) (C i) (C j))
      (canonical : e.HasCanonicalShift) (p : Path j l) : Path i l

variable {C}

/-- Evaluate a finite list; the empty list is the identity.
Source: finite-composite clause (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Path.eval {i j : ι} : Path (B := B) C i j →
    (DerivedCategory (C i) ⥤ DerivedCategory (C j))
  | .nil _ => 𝟭 _
  | .cons e _ p => e.derived ⋙ p.eval

/-- Concatenate lists of separately derived functors.
Source: finite-composite clause (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Path.append {i j l : ι} : Path (B := B) C i j → Path (B := B) C j l →
    Path (B := B) C i l
  | .nil _, q => q
  | .cons e h p, q => .cons e h (p.append q)

/-- The canonical composite shift structure on a finite list.
Source: target-shift clause (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
@[instance_reducible]
def Path.commShift {i j : ι} (p : Path (B := B) C i j) : p.eval.CommShift ℤ :=
  match p with
  | .nil i => (inferInstance : (𝟭 (DerivedCategory (C i))).CommShift ℤ)
  | .cons e _ p => by
      haveI := p.commShift
      exact (inferInstance : (e.derived ⋙ p.eval).CommShift ℤ)

attribute [instance] Path.commShift

/-- Full action on mapping complexes, with naturality, identity and derived composition,
the cohomology formula, and the entire target-shift square.
Source: the Ra_! arrow (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
structure Action (S : ∀ i, HomModel (B := B) (C i)) {i j : ι} (p : Path (B := B) C i j) where
  map : ∀ P Q : DerivedCategory (C i),
    (S i).hom.obj (op P, Q) ⟶ (S j).hom.obj (op (p.eval.obj P), p.eval.obj Q)
  naturality : ∀ (P P' Q Q' : DerivedCategory (C i)) (f : P' ⟶ P) (g : Q ⟶ Q'),
    (S i).hom.map (f.op, g) ≫ map P' Q' =
      map P Q ≫ (S j).hom.map ((p.eval.map f).op, p.eval.map g)
  identity : ∀ P : DerivedCategory (C i),
    (S i).unit P ≫ map P P = (S j).unit (p.eval.obj P)
  composition : ∀ P Q R : DerivedCategory (C i),
    (S i).comp P Q R ≫ map P R = (map Q R ⊗ₘ map P Q) ≫
      (S j).comp (p.eval.obj P) (p.eval.obj Q) (p.eval.obj R)
  cohomology : ∀ (P Q : DerivedCategory (C i)) (n : ℤ)
      (x : (DerivedCategory.homologyFunctor (CoeffModules.{b, v} B) n).obj
        ((S i).hom.obj (op P, Q))),
    (S j).cohomology (p.eval.obj P) (p.eval.obj Q) n
      ((DerivedCategory.homologyFunctor (CoeffModules.{b, v} B) n).map (map P Q) x) =
        p.eval.map ((S i).cohomology P Q n x) ≫ (p.eval.commShiftIso n).hom.app Q
  target_shift : ∀ (P Q : DerivedCategory (C i)) (n : ℤ),
    map P (Q⟦n⟧) ≫
        (S j).hom.map (X := (op (p.eval.obj P), p.eval.obj (Q⟦n⟧)))
          (Y := (op (p.eval.obj P), (p.eval.obj Q)⟦n⟧))
          (𝟙 _, (p.eval.commShiftIso n).hom.app Q) ≫
        ((S j).shift (p.eval.obj P) (p.eval.obj Q) n).hom =
      ((S i).shift P Q n).hom ≫ (map P Q)⟦n⟧'

/-- The global derived Hom object, with coefficients literally in B.
Source: Stacks 0B6E (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def HomModel.overB [HasDerivedCategory.{max b v} (ModuleCat.{max b v} B)]
    (S : HomModel (B := B) A) :
    (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory (ModuleCat.{max b v} B) :=
  S.hom ⋙ (coefficientDerivedEquivalence.{b, v} B).functor

/-- Transport the action arrow along the canonical coefficient-ring equivalence to D(B).
Source: the Ra_! arrow (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Action.mapOverB [HasDerivedCategory.{max b v} (ModuleCat.{max b v} B)]
    {S : ∀ i, HomModel (B := B) (C i)} {i j : ι} {p : Path (B := B) C i j}
    (a : Action S p) (P Q : DerivedCategory (C i)) :
    (S i).overB.obj (op P, Q) ⟶ (S j).overB.obj (op (p.eval.obj P), p.eval.obj Q) :=
  (coefficientDerivedEquivalence.{b, v} B).functor.map (a.map P Q)

/-- The canonical comparison of evaluating a concatenation with composing evaluations.
Source: finite-composite clause (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
def Path.appendIso {i j l : ι} (p : Path (B := B) C i j) (q : Path (B := B) C j l) :
    (p.append q).eval ≅ p.eval ⋙ q.eval := by
  induction p with
  | nil i => exact (Functor.leftUnitor q.eval).symm
  | cons e h p ih =>
      exact Functor.isoWhiskerLeft e.derived (ih q) ≪≫
        (Functor.associator e.derived p.eval q.eval).symm

/-- Simultaneous mapping objects and actions, normalized on every K-injective pair.
Thus replacing any resolution uses the same derived morphism. Concatenation and the
empty list are equalities in D(B), beyond their cohomology formulas.
Source: blueprint's Ra_! arrow (blueprint: lem-sf-derived-functor-mapping-complex-action). -/
structure System where
  canonical_shifts : ∀ {i j : ι} (e : Step (B := B) (C i) (C j)),
    ∃ s : e.derived.CommShift ℤ, (Step.HasCanonicalShift { e with commShift := s })
  models : ∀ i, HomModel (B := B) (C i)
  actions : ∀ {i j : ι} (p : Path (B := B) C i j), Action models p
  empty : ∀ (i : ι) (P Q : DerivedCategory (C i)),
    (actions (.nil i)).map P Q = 𝟙 _
  concat : ∀ {i j l : ι} (p : Path (B := B) C i j) (q : Path (B := B) C j l)
      (P Q : DerivedCategory (C i)),
    (actions (p.append q)).map P Q =
      (actions p).map P Q ≫ (actions q).map (p.eval.obj P) (p.eval.obj Q) ≫
        (models l).hom.map
          (X := (op (q.eval.obj (p.eval.obj P)), q.eval.obj (p.eval.obj Q)))
          (Y := (op ((p.append q).eval.obj P), (p.append q).eval.obj Q))
          (((p.appendIso q).hom.app P).op, (p.appendIso q).inv.app Q)
  cochainMap : ∀ {i j : ι} (e : Step (B := B) (C i) (C j))
      (X Y : CochainComplex (C i) ℤ),
    (models i).ordinary.obj (op X, Y) ⟶ (models j).ordinary.obj
      (op ((e.original.mapHomologicalComplex (.up ℤ)).obj X),
        (e.original.mapHomologicalComplex (.up ℤ)).obj Y)
  cochainMap_apply : ∀ {i j : ι} (e : Step (B := B) (C i) (C j))
      (X Y : CochainComplex (C i) ℤ) (n a d : ℤ) (h : a + n = d)
      (x : ((models i).ordinary.obj (op X, Y)).X n),
    ((((models j).degree ((e.original.mapHomologicalComplex (.up ℤ)).obj X)
      ((e.original.mapHomologicalComplex (.up ℤ)).obj Y) n).hom
      ((cochainMap e X Y).f n x)).down).v a d h =
        e.original.map (((((models i).degree X Y n).hom x).down).v a d h)
  resolution_normalization : ∀ {i j : ι} (e : Step (B := B) (C i) (C j))
      (h : e.HasCanonicalShift) (I J : CochainComplex (C i) ℤ)
      [I.IsKInjective] [J.IsKInjective],
    (models i).comparison.app (op I, J) ≫
        (actions (.cons e h (.nil j))).map (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map (cochainMap e I J) ≫
        (models j).comparison.app
          (op ((e.original.mapHomologicalComplex (.up ℤ)).obj I),
            (e.original.mapHomologicalComplex (.up ℤ)).obj J) ≫
        (models j).hom.map
          (X := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj I)),
            DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj J)))
          (Y := (op (e.derived.obj (DerivedCategory.Q.obj I)),
            e.derived.obj (DerivedCategory.Q.obj J)))
          ((e.representativeIso I).hom.op, (e.representativeIso J).inv)
  exact_unit : ∀ {i j : ι} (e : Step (B := B) (C i) (C j))
      [PreservesFiniteLimits e.original] [PreservesFiniteColimits e.original]
      (X : CochainComplex (C i) ℤ), IsIso (e.complexUnit X)
  exact_normalization : ∀ {i j : ι} (e : Step (B := B) (C i) (C j))
      [PreservesFiniteLimits e.original] [PreservesFiniteColimits e.original]
      (h : e.HasCanonicalShift) (X Y : CochainComplex (C i) ℤ),
    (models i).comparison.app (op X, Y) ≫
        (actions (.cons e h (.nil j))).map (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) ≫
        (models j).hom.map
          (X := (op (e.derived.obj (DerivedCategory.Q.obj X)),
            e.derived.obj (DerivedCategory.Q.obj Y)))
          (Y := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj X)),
            e.derived.obj (DerivedCategory.Q.obj Y)))
          ((e.complexUnit X).op, 𝟙 _) =
      DerivedCategory.Q.map (cochainMap e X Y) ≫
        (models j).comparison.app
          (op ((e.original.mapHomologicalComplex (.up ℤ)).obj X),
            (e.original.mapHomologicalComplex (.up ℤ)).obj Y) ≫
        (models j).hom.map
          (X := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj X)),
            DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj Y)))
          (Y := (op (DerivedCategory.Q.obj ((e.original.mapHomologicalComplex (.up ℤ)).obj X)),
            e.derived.obj (DerivedCategory.Q.obj Y)))
          (𝟙 _, e.complexUnit Y)

/-- Mapping-complex actions for all finite lists of separately right derived functors.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, second paragraph, Ra_! arrow and H^i assertion
(blueprint: lem-sf-derived-functor-mapping-complex-action).

Proof:
1. Choose K-injective representatives, using prop-pur-kinjective-resolutions-exist.
Precomposition with a source resolution is a quasi-isomorphism into a K-injective
(lem-sf-global-hom-resolution-roof). The ordinary linear cochains compute global RHom;
lem-sfb-derived-internal-hom-sections-model identifies its underlying global sections.
2. Apply each F componentwise to these cochains. Additivity and B-linearity make a
chain map; it preserves identities and cochain composition without preserving products.
3. Follow by the target ordinary-to-resolved Hom comparison. Its precomposition roof
is invertible by K-injectivity, without assuming F preserves K-injectives.
4. Naturality and independence of resolutions follow from the unique homotopy-class
lifts and canonical comparisons of lem-sf-kinjective-derived-map-computation and
lem-weil-kinjective-total-derived-linear. Applying F preserves homotopy equivalences.
5. The composition equation of lem-sf-global-hom-resolution-roof includes the tensorator
from derived tensor to ordinary tensor; combine it with strict cochain composition.
6. Shift the target resolution. The signed cochain reindexing commutes with the map,
so the full shift square commutes. Every degree-n cocycle represents a map into [n];
its image is RF(h) followed by the canonical shift comparison. Use
lem-weil-pbc-kinjective-shift and lem-pc-right-derived-functor-triangulated.
7. If F is exact, lem-pur-exact-derived-unit identifies its termwise model with RF;
the unit-compatible comparison transports this same action, even if FI is not K-injective.
8. Compose the actions along lists, starting with the identity for the empty list.
Paste the preceding equations. Associativity gives the concatenation formula; this
never identifies the composite of separate right derivations with R of the composite. -/
theorem derivedFunctorMappingComplexAction
    [∀ i, IsGrothendieckAbelian.{v} (C i)]
    (sites : ι → Type c) [∀ i, Category.{r} (sites i)]
    [∀ i, EssentiallySmall.{v} (sites i)]
    (topologies : ∀ i, GrothendieckTopology (sites i))
    (rings : ∀ i, Sheaf (topologies i) RingCat.{s})
    (_moduleModels : ∀ i, Nonempty ((C i) ≌ ringedSiteModules.{v, s, r, c} (rings i))) :
    Nonempty (System (B := B) (C := C)) := by
  sorry

end CategoryTheory.DerivedMappingAction
