/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.IntegralOperationShiftData
public import WeilConjectures.SixFunctors.CompletedTensorShiftRight
import WeilConjectures.SixFunctors.SystemTensorShiftRepresentativeModels
import WeilConjectures.SixFunctors.SystemTensorShiftCoherence
import WeilConjectures.SixFunctors.CompletedTensorSlotShiftLaws
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Resolution-normalized shifts of the basic system operations

Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, maps-used sentence; Stacks 011G, 014E, 015F,
070I, 079P and 0FPQ.
(blueprint: lem-pur-basic-system-shift-resolution-calculus).

The helpers below spell out properties of the already prescribed comparisons.
They do not choose new operations, resolutions, tensor products or adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false

universe u v₁ v₂ u₁ u₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor

namespace WeilConjectures.IntegralSystemRealization

/-- Termwise identity normalization and its exact-localization square, for a specified
shift structure. Source: Stacks 015F and 011G
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicExactShiftModels
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (s : F.mapDerivedCategory.CommShift ℤ) : Prop :=
  (∀ (M : CochainComplex A ℤ) (r i : ℤ),
    (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app M).f i = 𝟙 _) ∧
  (∀ (M : CochainComplex A ℤ) (r : ℤ),
    F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
        (Functor.commShiftIso F.mapDerivedCategory (self := s) r).hom.app
          (DerivedCategory.Q.obj M) ≫
        (shiftFunctor (DerivedCategory B) r).map (F.mapDerivedCategoryFactors.hom.app M) =
      F.mapDerivedCategoryFactors.hom.app (M⟦r⟧) ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app M) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj M))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical computation on any simultaneous K-injective resolution, using the
actual universal derived-unit component. No evaluation of K-injectives is involved.
Source: Stacks 070I and 079P
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def basicSystemImageResolutionIso (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M I : CochainComplex (coefficientSequenceModules l E X) ℤ}
    (a : M ⟶ I) [QuasiIso a] [I.IsKInjective] :
    (Operations.push l E o p).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (((pullbackTensorSequenceDirect l E p).mapHomologicalComplex (.up ℤ)).obj I) :=
  (Operations.push l E o p).mapIso (asIso (DerivedCategory.Q.map a)) ≪≫
    (@asIso _ _ _ _ ((o.direct p).model.directUnit.app I)
      ((o.direct p).model.computes I inferInstance)).symm

/-- The prescribed mate shift computed on every shifted simultaneous resolution.
Naturality of the two computation maps also gives independence of the resolution.
Source: Stacks 070I, 079P and the actual adjunction of Stacks 07A6
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemImageShiftModels (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Prop :=
  ∀ (M I : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (a : M ⟶ I) [QuasiIso a] [I.IsKInjective] (r : ℤ),
    (I⟦r⟧).IsKInjective ∧ QuasiIso (a⟦r⟧') ∧
    (Operations.push l E o p).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
        (Functor.commShiftIso _ (self := systemPushShift l E o p) r).hom.app
          (DerivedCategory.Q.obj M) ≫
        (shiftFunctor (System l E Y) r).map
          (basicSystemImageResolutionIso l E o p a).hom =
      (basicSystemImageResolutionIso l E o p (a⟦r⟧')).hom ≫
        DerivedCategory.Q.map
          ((((pullbackTensorSequenceDirect l E p).mapHomologicalComplex (.up ℤ)).commShiftIso
            r).hom.app I) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((pullbackTensorSequenceDirect l E p).mapHomologicalComplex (.up ℤ)).obj I)

/-- The actual adjunction, including its unit and counit, respects the prescribed
inverse-image and direct-image shifts. Source: Stacks 07A6
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemImageMate (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  letI := systemPullShift l E p
  letI := systemPushShift l E o p
  (o.direct p).adj.CommShift ℤ

/-- Extract the second shift, then the first, and identify [a][b] with [a+b]. This
uses exactly the two comparisons already fixed in TensorShifts.
Source: Stacks 011G, 0FPQ; blueprint maps-used sentence
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def basicSystemTensorShift (W : Scheme.{u}) (a b : ℤ) :
    ((shiftFunctor (System l E W) a).prod (shiftFunctor (System l E W) b)) ⋙
        (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) (a + b) :=
  isoWhiskerLeft (tensorShiftFirst (System l E W) a) ((tensorShifts l E).systemRight W b) ≪≫
    isoWhiskerRight ((tensorShifts l E).systemLeft W a) (shiftFunctor (System l E W) b) ≪≫
    isoWhiskerLeft (calculus l E W).systemClosed.tensor
      (shiftFunctorAdd (System l E W) a b).symm

/-- Coefficient (-1)^(b i) on the shifted (i,j) summand, on the whole sequence site.
The isomorphism is a chain map and a strict-system map, so both differential and
quotient-transition squares are retained. Source: Stacks 011G and 0FPQ
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemTensorFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (a b : ℤ)
    (α : (systemTotalTensor l E W).obj (P⟦a⟧, Q⟦b⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦a + b⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i + a)).val.obj U) (y : (Q.X (j + b)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (P⟦a⟧) (Q⟦b⟧) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      (a + b) (i + j) ((i + a) + (j + b)) (by omega)).inv.val.app U)
      ((b * i).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        P Q (i + a) (j + b) ((i + a) + (j + b)) rfl U x y)

/-- Identification with the fixed derived tensor shift on every K-flat pair, through
the actual recorded tensor-model comparisons. Source: Stacks 06YU and 0FPQ
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemTensorModels (W : Scheme.{u}) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q) (a b : ℤ),
    ∃ (hPa : systemKFlat l E W (P⟦a⟧)) (hQb : systemKFlat l E W (Q⟦b⟧))
      (α : (systemTotalTensor l E W).obj (P⟦a⟧, Q⟦b⟧) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦a + b⟧),
      BasicSystemTensorFormula l E W P Q a b α ∧
      (calculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app P)
            ((DerivedCategory.Q.commShiftIso b).hom.app Q)) ≫
          (basicSystemTensorShift l E W a b).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        ((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          (P⟦a⟧) (Q⟦b⟧) hPa hQb).inv ≫ DerivedCategory.Q.map α.hom ≫
        (DerivedCategory.Q.commShiftIso (a + b)).hom.app
          ((systemTotalTensor l E W).obj (P, Q)) ≫
        (shiftFunctor (System l E W) (a + b)).map
          (((calculus l E W).systemTensorModel.iso
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
            P Q hP hQ).hom)

/-- A slot's prescribed natural isomorphisms extend to coherent zero/addition shift
structures on each partial tensor functor. Naturality in both inputs is retained by
those prescribed isomorphisms. Source: Stacks 011G and 0FPQ
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicTensorSlotLaws {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
    (T : A × A ⥤ A)
    (L : ∀ r : ℤ, tensorShiftFirst A r ⋙ T ≅ T ⋙ shiftFunctor A r)
    (R : ∀ r : ℤ, completedTensorShiftSecond A r ⋙ T ≅ T ⋙ shiftFunctor A r) : Prop :=
  ∃ (s₁ : ∀ N : A, ((Functor.curry.obj T).flip.obj N).CommShift ℤ)
    (s₂ : ∀ M : A, ((Functor.curry.obj T).obj M).CommShift ℤ),
    (∀ (M N : A) (r : ℤ), (Functor.commShiftIso _ (self := s₁ N) r).app M =
      (L r).app (M, N)) ∧
    (∀ (M N : A) (r : ℤ), (Functor.commShiftIso _ (self := s₂ M) r).app N =
      (R r).app (M, N))

/-- The unsigned associator of the actual closed tensor commutes with the prescribed
simultaneous shifts in all three inputs. Source: Stacks 0FPQ, 0FNH
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemTensorAssociativity (W : Scheme.{u}) : Prop :=
  ∀ (M N H : System l E W) (a b c : ℤ),
    (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((basicSystemTensorShift l E W a b).hom.app (M, N)) (𝟙 (H⟦c⟧))) ≫
      (basicSystemTensorShift l E W (a + b) c).hom.app
        ((calculus l E W).systemClosed.tensor.obj (M, N), H) ≫
      ((calculus l E W).systemClosed.monoidal.associator M N H).hom⟦(a + b) + c⟧' =
    ((calculus l E W).systemClosed.monoidal.associator (M⟦a⟧) (N⟦b⟧) (H⟦c⟧)).hom ≫
      (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 (M⟦a⟧)) ((basicSystemTensorShift l E W b c).hom.app (N, H))) ≫
      (basicSystemTensorShift l E W a (b + c)).hom.app
        (M, (calculus l E W).systemClosed.tensor.obj (N, H)) ≫
      eqToHom (congrArg
        (fun n : ℤ ↦ ((calculus l E W).systemClosed.tensor.obj
          (M, (calculus l E W).systemClosed.tensor.obj (N, H)))⟦n⟧) (add_assoc a b c).symm)

/-- Normalize the symmetry by the actual Koszul chain formula and derived tensor
comparison on every pair. The formula fixes the symmetry, rather than accepting an
arbitrary isomorphism with the same endpoints. Source: Stacks 0FPQ, 0FNH
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemTensorSymmetryModel (W : Scheme.{u})
    (s : (calculus l E W).systemClosed.tensor ≅
      CategoryTheory.Prod.swap (System l E W) (System l E W) ⋙
        (calculus l E W).systemClosed.tensor) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ α : (systemTotalTensor l E W).obj (P, Q) ≅
      (systemTotalTensor l E W).obj (Q, P),
      (∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        ((α.hom.f (i + j)).val.app U)
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q i j (i + j) rfl U x y) =
        (i * j).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) Q P j i (i + j) (add_comm j i) U y x) ∧
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        P Q hP hQ).hom ≫ s.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map α.hom ≫
        ((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          Q P hQ hP).hom

/-- The signed symmetry square for simultaneous shifts; its sign is (-1)^(ab).
Source: Stacks 0FPQ, 0FNH
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
def BasicSystemTensorSymmetry (W : Scheme.{u}) : Prop :=
  ∃ s : (calculus l E W).systemClosed.tensor ≅
      CategoryTheory.Prod.swap (System l E W) (System l E W) ⋙
        (calculus l E W).systemClosed.tensor,
    BasicSystemTensorSymmetryModel l E W s ∧
    ∀ (M N : System l E W) (a b : ℤ),
      (basicSystemTensorShift l E W a b).hom.app (M, N) ≫
          (s.hom.app (M, N))⟦a + b⟧' =
        (a * b).negOnePow • (s.hom.app (M⟦a⟧, N⟦b⟧) ≫
          (basicSystemTensorShift l E W b a).hom.app (N, M) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ ((calculus l E W).systemClosed.tensor.obj (N, M))⟦n⟧)
            (add_comm b a)))

/-- Every clause is about the prescribed maps on ambient unbounded derived systems.
The geometric range is finite-type k-schemes, with separated finite-type inverse
images, proper direct images and quasi-compact open extensions. Source: blueprint
maps-used sentence and Stacks 015F, 070I, 0FPQ
(blueprint: lem-pur-basic-system-shift-resolution-calculus). -/
structure BasicSystemShiftResolutionCalculus (D : FiniteFieldDatum.{u})
    (o : Operations l E) : Prop where
  pull_models : ∀ {U V : Over (Spec (.of D.k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (v : U ⟶ V) [IsSeparated v.left] [LocallyOfFiniteType v.left] [QuasiCompact v.left],
    BasicExactShiftModels (pullbackTensorSequenceInverse l E v.left)
      (systemPullShift l E v.left)
  open_models : ∀ {U V : Over (Spec (.of D.k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (j : U ⟶ V) [IsOpenImmersion j.left] [QuasiCompact j.left],
    BasicExactShiftModels (o.extension j.left).ordinary (systemOpenShift l E o j.left)
  push_models : ∀ {U V : Over (Spec (.of D.k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (p : U ⟶ V) [IsProper p.left], BasicSystemImageShiftModels l E o p.left
  push_mate : ∀ {U V : Over (Spec (.of D.k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (p : U ⟶ V) [IsProper p.left], BasicSystemImageMate l E o p.left
  tensor_models : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    BasicSystemTensorModels l E W.left
  system_tensor_laws : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    BasicTensorSlotLaws (calculus l E W.left).systemClosed.tensor
      ((tensorShifts l E).systemLeft W.left) ((tensorShifts l E).systemRight W.left)
  tensor_associativity : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    BasicSystemTensorAssociativity l E W.left
  tensor_symmetry : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    BasicSystemTensorSymmetry l E W.left
  system_left : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (r : ℤ),
    systemTensorLeftProperty l E W.left r ((tensorShifts l E).systemLeft W.left r)
  system_right : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (r : ℤ),
    systemTensorRightProperty l E W.left r ((tensorShifts l E).systemRight W.left r)
  integral_left : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (r : ℤ),
    integralTensorLeftProperty l E W.left r ((tensorShifts l E).integralLeft W.left r)
  integral_right : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (r : ℤ),
    integralCompletedTensorRightShiftProperty l E W.left r
      ((tensorShifts l E).integralRight W.left r)
  integral_tensor_laws : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
    BasicTensorSlotLaws (integralCompletedTensor l E W.left)
      ((tensorShifts l E).integralLeft W.left) ((tensorShifts l E).integralRight W.left)

attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf

private theorem exact_shift_models
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    BasicExactShiftModels F inferInstance := by
  refine ⟨fun M r i ↦ F.mapHomologicalComplex_commShiftIso_hom_app_f M r i, ?_⟩
  intro M r
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc]
    using NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom r M

private theorem normalized_unit_shift
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (d : SheafOfModules.CoefficientDerivedImage F G adj)
    (e : d.inverse ≅ F.mapDerivedCategory)
    (he : ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫
      F.mapDerivedCategoryFactors.hom.app P = d.inverseFactors.hom.app P) :
    letI := (d.adjunction.ofNatIsoLeft e).rightAdjointCommShift ℤ
    NatTrans.CommShift d.directUnit ℤ := by
  let H := G.mapHomologicalComplex (.up ℤ)
  let ad := d.adjunction.ofNatIsoLeft e
  let := ad.rightAdjointCommShift ℤ
  let : ad.CommShift ℤ := ad.commShift_of_leftAdjoint ℤ
  let a := adj.mapHomologicalComplex (.up ℤ)
  let : a.CommShift ℤ := Adjunction.CommShift.mk' a ℤ inferInstance
  let α : (H ⋙ DerivedCategory.Q) ⋙ F.mapDerivedCategory ⟶ DerivedCategory.Q :=
    (Functor.associator H DerivedCategory.Q F.mapDerivedCategory).hom ≫
      Functor.whiskerLeft H F.mapDerivedCategoryFactors.hom ≫
      (Functor.associator H (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).inv ≫
      Functor.whiskerRight a.counit DerivedCategory.Q ≫
      (Functor.leftUnitor DerivedCategory.Q).hom
  let β : H ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ d.direct :=
    (Functor.rightUnitor (H ⋙ DerivedCategory.Q)).inv ≫
      Functor.whiskerLeft (H ⋙ DerivedCategory.Q) ad.unit ≫
      (Functor.associator (H ⋙ DerivedCategory.Q) F.mapDerivedCategory d.direct).inv ≫
      Functor.whiskerRight α d.direct
  have hβ : NatTrans.CommShift β ℤ := by dsimp [β, α]; infer_instance
  have heq : d.directUnit = β := by
    ext I
    have h := d.transpose (H.obj I) I (a.counit.app I)
    have hc : a.homEquiv (H.obj I) I (a.counit.app I) = 𝟙 _ := by
      rw [Adjunction.homEquiv_unit]
      exact a.right_triangle_components I
    change d.adjunction.homEquiv _ _ _ =
      DerivedCategory.Q.map (a.homEquiv (H.obj I) I (a.counit.app I)) ≫ _ at h
    rw [hc, CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [← h]
    have hb : β.app I = ad.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app (H.obj I) ≫
          DerivedCategory.Q.map (a.counit.app I)) := by
      simp only [β, α, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
        CategoryTheory.Functor.map_comp, Category.id_comp, Adjunction.homEquiv_unit]
      dsimp only [Functor.comp_obj]
      erw [d.direct.map_id, Category.comp_id]
    rw [hb, Adjunction.homEquiv_ofNatIsoLeft_apply]
    congr 1
    rw [← Category.assoc, he]
  rw [heq]
  exact hβ

private theorem direct_unit_shift (o : Operations l E) {X Y : Scheme.{u}}
    (p : X ⟶ Y) :
    letI := systemPushShift l E o p
    NatTrans.CommShift (o.direct p).model.directUnit ℤ := by
  exact normalized_unit_shift _ _ (pullbackTensorSequenceAdjunction l E p)
    (o.direct p).model (o.direct p).inverse (o.direct p).factors

private theorem resolution_shift_square
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (G : A ⥤ B) [G.Additive] (R : DerivedCategory A ⥤ DerivedCategory B)
    [R.CommShift ℤ]
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    [NatTrans.CommShift η ℤ] {M I : CochainComplex A ℤ} (a : M ⟶ I) (r : ℤ)
    [IsIso (η.app I)] [IsIso (η.app (I⟦r⟧))] :
    R.map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
        (R.commShiftIso r).hom.app (DerivedCategory.Q.obj M) ≫
        (shiftFunctor (DerivedCategory B) r).map
          (R.map (DerivedCategory.Q.map a) ≫ inv (η.app I)) =
      R.map (DerivedCategory.Q.map (a⟦r⟧')) ≫ inv (η.app (I⟦r⟧)) ≫
        DerivedCategory.Q.map (((G.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) := by
  have hu := NatTrans.shift_app_comm η r I
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hu
  have hu' := congrArg
    (fun f ↦ inv (η.app (I⟦r⟧)) ≫ f ≫
      (shiftFunctor (DerivedCategory B) r).map (inv (η.app I))) hu
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] at hu'
  have hn := (R.commShiftIso r).hom.naturality (DerivedCategory.Q.map a)
  have hq := (DerivedCategory.Q.commShiftIso r).hom.naturality a
  simp only [Functor.comp_map] at hn hq
  simp only [CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% hn, ← R.map_comp_assoc, ← hq, R.map_comp, Category.assoc]
  rw [← hu']

private theorem direct_resolution_shift (o : Operations l E) {X Y : Scheme.{u}}
    (p : X ⟶ Y) : BasicSystemImageShiftModels l E o p := by
  intro M I a _ _ r
  refine ⟨inferInstance, inferInstance, ?_⟩
  let := systemPushShift l E o p
  let η := (o.direct p).model.directUnit
  let : NatTrans.CommShift η ℤ := direct_unit_shift l E o p
  let : IsIso (η.app I) := (o.direct p).model.computes I inferInstance
  let : IsIso (η.app (I⟦r⟧)) := (o.direct p).model.computes (I⟦r⟧) inferInstance
  simpa only [basicSystemImageResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc] using
      resolution_shift_square (pullbackTensorSequenceDirect l E p)
        (Operations.push l E o p) η a r

/-- Resolution-normalized shifts for the fixed basic system operations and completed tensor.
Source: current blueprint sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, maps-used sentence; Stacks 011G, 014E, 015F,
070I, 079P and 0FPQ (blueprint: lem-pur-basic-system-shift-resolution-calculus).

Proof:
1. Use lem-coef-semilinear-derived-sections to work on the whole ringed sequence site.
   Apply prop-pur-kinjective-resolutions-exist there, never to individual evaluations.
2. Apply lem-weil-pbc-exact-functor-derived-factorization to inverse image and open
   extension. Their cochain shifts are identity in each reindexed degree, including
   the signed differential. Their localized squares give pull_models and open_models.
3. Shift any simultaneous K-injective resolution using lem-weil-pbc-kinjective-shift.
   Termwise direct image commutes with this shift. The canonical derived-unit
   computation gives push_models. By lem-sf-kinjective-derived-map-computation,
   changing resolutions conjugates by the unique homotopy classes, giving naturality
   and independence. By lem-sp-canonical-right-derived-adjunction-shift these are
   the mates through the actual adjunction, with its unit and counit: push_mate.
4. Specialize lem-pur-diagram-pullback-monoidal-shift-models to R/t^(n+1).
   Extract the right shift first and then the left. On shifted bidegree (i,j) this
   has sign (-1)^(bi). Zero/addition laws follow in each slot. Associativity uses
   bi+c(i+j)=cj+(b+c)i; the symmetry exponents differ by 2bi and give (-1)^(ab).
   The representative characterization in def-pur-integral-operation-shift-data
   identifies the resulting maps with the prescribed tensorShifts, not new choices.
5. For completed tensor use good flat-term K-flat models. Their shifts remain good
   by lem-weil-pbc-kflat-fixed-tensor-triangulated. Apply the chain formulas from
   lem-pur-total-tensor-signed-coherence to their finite reductions; these reductions
   need not be K-flat. Every quotient transition preserves degree, hence commutes
   with the signs. Pass to products, then Cone(1-s), with (b,a) sent to
   (b,(-1)^r a), and finally [-1]. This is integralTensorLeftProperty; on the right
   it is exactly lem-sf-completed-tensor-shift-right. The cone formula is natural,
   identity at zero, and multiplicative under addition of shifts.
6. By lem-pur-integral-operations-well-defined the model functors invert the resolving
   quasi-isomorphisms. Fully faithful restriction in
   lem-pur-derived-tensor-additive-constraints (or
   lem-weil-pbc-localization-universal-property in each input) descends these natural
   comparisons and their zero/addition equations uniquely. Every displayed model
   square quantifies over all resolving representatives, giving independence.
-/
theorem basicSystemShiftResolutionCalculus (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) : BasicSystemShiftResolutionCalculus l E D o := by
  refine
    { pull_models := ?_
      open_models := ?_
      push_models := ?_
      push_mate := ?_
      tensor_models := ?_
      system_tensor_laws := ?_
      tensor_associativity := ?_
      tensor_symmetry := ?_
      system_left := ?_
      system_right := ?_
      integral_left := ?_
      integral_right := ?_
      integral_tensor_laws := ?_ }
  · intro U V _ _ _ _ v _ _ _
    exact exact_shift_models (pullbackTensorSequenceInverse l E v.left)
  · intro U V _ _ _ _ j _ _
    exact exact_shift_models (o.extension j.left).ordinary
  · intro U V _ _ _ _ p _
    exact direct_resolution_shift l E o p.left
  · intro U V _ _ _ _ p _
    let := systemPullShift l E p.left
    exact (o.direct p.left).adj.commShift_of_leftAdjoint ℤ
  · intro W _ _
    exact systemTensorShiftRepresentativeModels l E W.left
  · intro W _ _
    exact (systemTensorShiftCoherence l E W.left).1
  · intro W _ _
    exact (systemTensorShiftCoherence l E W.left).2.1
  · intro W _ _
    exact (systemTensorShiftCoherence l E W.left).2.2
  · intro W _ _ r
    exact (tensorShifts l E).systemLeft_normalized W.left r
  · intro W _ _ r
    exact (tensorShifts l E).systemRight_normalized W.left r
  · intro W _ _ r
    exact (tensorShifts l E).integralLeft_normalized W.left r
  · intro W _ _ r
    exact (tensorShifts l E).integralRight_normalized W.left r
  · intro W _ _
    exact completedTensorSlotShiftLaws l E W.left

end WeilConjectures.IntegralSystemRealization
