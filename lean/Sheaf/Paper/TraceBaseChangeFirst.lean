/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedProjectionTensorComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons


/-!
# Trace and base-change rearrangement before the first triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-line.proof.md`, (1), first triangle
(blueprint: lem-sfb-trace-base-change-first).

All operations below are on the ordinary unbounded derived categories of internal
modules over the pulled-back condensed coefficient ring. The square and tensor
comparisons, projection maps and source identification are specified constructions.
The internal-module tensor helpers are owned by this item; the general ringed-topos
tensor-pullback interface remains publicly imported with its recorded declaration.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section TensorPullbackHelpers

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ordinary comparison sends the tensor of the two universal pullback sections to
its universal tensor section; on the regular module it is the coefficient map alpha.
These are equalities of sheaf maps, so include all local generators, rather than only
sections over schemes in the image of base change.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def CondensedTensorNormalization (m : (upperStar Λ f).CoreMonoidal) : Prop :=
  (∀ M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y),
    (Mod.tensorObjπ M N) ≫ ((upperStarLowerStarAdjunction Λ f).unit.app (M ⊗ N)).hom ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map ((m.μIso M N).inv.hom) =
      (((upperStarLowerStarAdjunction Λ f).unit.app M).hom ⊗ₘ
        ((upperStarLowerStarAdjunction Λ f).unit.app N).hom) ≫
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f)
        ((upperStar Λ f).obj M).X ((upperStar Λ f).obj N).X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N))) ∧
  ((upperStarLowerStarAdjunction Λ f).unit.app (𝟙_ _)).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map m.εIso.inv.hom =
    condensedPushforwardHom Λ f

/-- The ordinary tensor pullback has one uniquely normalized strong monoidal structure.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first).
Proof: present relative tensor by its two balancing arrows. Inverse image preserves
this coequalizer and the abelian-sheaf tensor. Extension along alpha sends
s tensor (m tensor n) to (s tensor m) tensor (1 tensor n), with inverse multiplying
the coefficient factors. The adjunction unit gives precisely the displayed equations.
The balancing quotient and sheafification show that these equations determine the
maps uniquely. The associativity and unit diagrams agree on these generators, so
these maps constitute CoreMonoidal, uniquely, including its inverse and proof fields. -/
theorem condensedTensorCore_existsUnique :
    ∃! m : (upperStar Λ f).CoreMonoidal, CondensedTensorNormalization Λ f m := by
  sorry

/-- The specified ordinary strong monoidal structure, selected by its unique equations.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
def condensedTensorCore : (upperStar Λ f).CoreMonoidal :=
  (condensedTensorCore_existsUnique Λ f).exists.choose

/-- Canonical strong monoidal module inverse image.
Source: Stacks 03EL (blueprint: lem-sfb-trace-base-change-first). -/
instance condensedUpperStarMonoidal : (upperStar Λ f).Monoidal :=
  (condensedTensorCore Λ f).toMonoidal

/-- Module inverse image preserves flat modules.
Source: Stacks 0G7E (blueprint: lem-sfb-trace-base-change-first).
Proof: pass through the exact internal-to-sectionwise module equivalence. The
normalized tensor comparison is the usual scalar-extension comparison there by its
unit-generator equations. Pullback of a flat sheaf is flat by the local tensor
criterion, so tensoring with the pulled-back module is exact. Transport back through
the exact equivalence. This is flatness in the existing monoidal module category. -/
@[instance] theorem condensedUpperStarPreservesFlat : (upperStar Λ f).PreservesFlat := by
  sorry

/-- The canonical derived tensor comparison; the generic derived comparison is uniquely
characterized by its square with the two derived counits and the ordinary tensorator.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def condensedDerivedTensorComparison := (upperStar Λ f).leftDerivedTensorComparison

/-- The canonical derived tensor comparison as an isomorphism of bifunctors.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def condensedDerivedTensorIso := asIso (upperStar Λ f).leftDerivedTensorComparison

/-- The canonical derived unit comparison, computed on the regular module in degree zero.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def condensedDerivedUnitIso :
    (upperStar Λ f).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ f).app _ ≪≫
    ((upperStar Λ f).mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (upperStar Λ f) (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso
          (Functor.Monoidal.εIso (upperStar Λ f)).symm)

/-- The actual Koszul symmetry descended from complexes by the existing two-variable
localization construction. No symmetry is chosen from a mere existence statement.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def condensedDerivedSymmetry (Z : Scheme.{u})
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    K ⊗ M ≅ M ⊗ K :=
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) (.up ℤ)) K M

end TensorPullbackHelpers

/-- The adjunction transpose defining projection, expressed over abstract categories.
Source: Stacks 0B56 (blueprint: lem-sfb-trace-base-change-first). -/
def traceProjectionFromComparison
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {P : D ⥤ C} (adj : F ⊣ P)
    (δ : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M) (K : C) (N : D) :
    K ⊗ P.obj N ⟶ P.obj (F.obj K ⊗ N) :=
  adj.homEquiv (K ⊗ P.obj N) (F.obj K ⊗ N)
    (δ K (P.obj N) ≫ (𝟙 (F.obj K) ⊗ₘ adj.counit.app N))

/-- Compose the specified symmetry, inverse projection and inverse base change.
The concrete B below supplies only the canonical comparisons.
Source: blueprint definition of B (blueprint: lem-sfb-trace-base-change-first). -/
def traceBFromComparisons
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory D] [MonoidalCategory V]
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q : V ⥤ D)
    (TY : C) (N : D)
    (s : U₂.obj (F.obj TY) ≅ U₁.obj (F.obj TY))
    (π : F.obj TY ⊗ Q.obj (U₁.obj N) ≅
      Q.obj (U₂.obj (F.obj TY) ⊗ U₁.obj N))
    (b : F.obj (P.obj N) ≅ Q.obj (U₁.obj N))
    (σ : U₁.obj N ⊗ U₁.obj (F.obj TY) ≅ U₁.obj (F.obj TY) ⊗ U₁.obj N)
    (τ : F.obj TY ⊗ Q.obj (U₁.obj N) ≅ Q.obj (U₁.obj N) ⊗ F.obj TY) :
    Q.obj (U₁.obj N ⊗ U₁.obj (F.obj TY)) ≅ F.obj (P.obj N) ⊗ F.obj TY :=
  Q.mapIso (σ ≪≫ tensorIso s.symm (Iso.refl _)) ≪≫ π.symm ≪≫ τ ≪≫
    tensorIso b.symm (Iso.refl _)

/-- The trace hypotheses written over arbitrary monoidal categories. Specialization below
supplies the canonical module functors, square mates, projection maps and unit comparison.
Source: blueprint hypotheses (blueprint: lem-sfb-trace-base-change-first). -/
structure TraceFirstHypotheses
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (b₁ : P ⋙ F ⟶ U₂ ⋙ Q₁) (b₂ : P ⋙ F ⟶ U₁ ⋙ Q₂)
    (unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (πF : ∀ (K : C) (N : D), K ⊗ P.obj N ⟶ P.obj (F.obj K ⊗ N))
    (πP : ∀ (K : D) (N : V), K ⊗ Q₁.obj N ⟶ Q₁.obj (U₁.obj K ⊗ N))
    (πQ : ∀ (K : D) (N : V), K ⊗ Q₂.obj N ⟶ Q₂.obj (U₂.obj K ⊗ N))
    (TY : C) where
  /-- The trace for f. -/
  t : P.obj (F.obj TY) ⟶ 𝟙_ C
  /-- The trace for p1, on the common twist. -/
  t₁ : Q₁.obj (U₁.obj (F.obj TY)) ⟶ 𝟙_ D
  /-- The trace for p2, on the common twist. -/
  t₂ : Q₂.obj (U₁.obj (F.obj TY)) ⟶ 𝟙_ D
  /-- The first trace compatibility, including the square comparison. -/
  trace₁ : b₁.app (F.obj TY) ≫ Q₁.map (s.hom.app TY) ≫ t₁ =
    F.map t ≫ unitIso.hom
  /-- The second trace compatibility. -/
  trace₂ : b₂.app (F.obj TY) ≫ t₂ = F.map t ≫ unitIso.hom
  /-- The first base-change mate is invertible on the localizing category. -/
  base₁ : ∀ N : D, LD N → IsIso (b₁.app N)
  /-- The second base-change mate is invertible on the localizing category. -/
  base₂ : ∀ N : D, LD N → IsIso (b₂.app N)
  /-- The projections used to define e are invertible. -/
  projectionF : ∀ K : C, LC K → IsIso (πF K (F.obj TY))
  /-- The projections on the right side are invertible. -/
  projectionP : ∀ N : D, LD N → IsIso (πP N (U₁.obj (F.obj TY)))
  /-- The projections used in B are invertible. -/
  projectionQ : ∀ N : D, LD N → IsIso (πQ (F.obj TY) (U₁.obj N))
  /-- Preservation by the inverse image of f. -/
  pullF : ∀ K : C, LC K → LD (F.obj K)
  /-- Preservation by the direct image of f. -/
  pushF : ∀ N : D, LD N → LC (P.obj N)
  /-- Preservation by the inverse image of p1. -/
  pullP : ∀ N : D, LD N → LV (U₁.obj N)
  /-- Preservation by the direct image of p1. -/
  pushP : ∀ N : V, LV N → LD (Q₁.obj N)
  /-- Preservation by the inverse image of p2. -/
  pullQ : ∀ N : D, LD N → LV (U₂.obj N)
  /-- Preservation by the direct image of p2. -/
  pushQ : ∀ N : V, LV N → LD (Q₂.obj N)
  /-- Preservation by G. -/
  preservesG : ∀ K : C, LC K → LD (F.obj K ⊗ F.obj TY)
  /-- Preservation by H. -/
  preservesH : ∀ N : D, LD N → LV (U₁.obj N ⊗ U₁.obj (F.obj TY))


/-- Trace evaluation by an inverse projection, with the right unit identification.
Source: blueprint definition of e (blueprint: lem-sfb-trace-base-change-first). -/
def traceAbstractCounit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (P : D ⥤ C) (K : C) (T : D)
    (π : K ⊗ P.obj T ⟶ P.obj (F.obj K ⊗ T)) (hπ : IsIso π)
    (t : P.obj T ⟶ 𝟙_ C) : P.obj (F.obj K ⊗ T) ⟶ K :=
  @inv _ _ _ _ π hπ ≫ (𝟙 K ⊗ₘ t) ≫ (ρ_ K).hom


/-- A square mate, with the canonical adjunctions supplied as data.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
def traceAbstractMate
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {P : D ⥤ C} {U₁ U₂ : D ⥤ V} {Q : V ⥤ D}
    (a : F ⊣ P) (b : U₂ ⊣ Q) (s : F ⋙ U₂ ≅ F ⋙ U₁) :
    P ⋙ F ⟶ U₁ ⋙ Q :=
  (mateEquiv a b (TwoSquare.mk _ _ _ _ s.hom)).natTrans

/-- Extract a component of a tensor comparison at its declared endpoints.
Source: Stacks 07A4 (blueprint: lem-sfb-trace-base-change-first). -/
def traceTensorComponent
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D)) (K M : C) :
    F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M :=
  (δ.app K).app M

/-- The complete displayed formula, on arbitrary monoidal categories. Its specialization
below fixes every functor, adjunction, mate, tensor comparison and symmetry canonically.
The conclusion includes the naturality of B and the stated trace identity.
Source: blueprint first triangle (blueprint: lem-sfb-trace-base-change-first). -/
def TraceFirstFormula
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory V]
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (F : C ⥤ D) (P : D ⥤ C) (U₁ U₂ : D ⥤ V) (Q₁ Q₂ : V ⥤ D)
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁)
    (unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (δF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (δ₁ : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M)
    (δ₂ : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M)
    (σD : ∀ K M : D, K ⊗ M ≅ M ⊗ K)
    (σV : ∀ K M : V, K ⊗ M ≅ M ⊗ K) (TY : C) : Prop :=
  ∀ H : TraceFirstHypotheses LC LD LV F P U₁ U₂ Q₁ Q₂ s
      (traceAbstractMate a a₁ s.symm) (traceAbstractMate a a₂ s) unitIso
      (traceProjectionFromComparison a δF)
      (traceProjectionFromComparison a₁ δ₁)
      (traceProjectionFromComparison a₂ δ₂) TY,
    (∀ (M N : D) (hM : LD M) (hN : LD N) (m : M ⟶ N),
      Q₂.map ((U₁ ⋙ tensorRight (U₁.obj (F.obj TY))).map m) ≫
          (traceBFromComparisons F P U₁ U₂ Q₂ TY N (s.app TY)
            (@asIso _ _ _ _ _ (H.projectionQ N hN))
            (@asIso _ _ _ _ _ (H.base₂ N hN))
            (σV _ _) (σD _ _)).hom =
        (traceBFromComparisons F P U₁ U₂ Q₂ TY M (s.app TY)
          (@asIso _ _ _ _ _ (H.projectionQ M hM))
          (@asIso _ _ _ _ _ (H.base₂ M hM)) (σV _ _) (σD _ _)).hom ≫
            (P ⋙ F ⋙ tensorRight (F.obj TY)).map m) ∧
    ∀ (N : D) (hN : LD N),
      P.map (traceBFromComparisons F P U₁ U₂ Q₂ TY N (s.app TY)
          (@asIso _ _ _ _ _ (H.projectionQ N hN))
          (@asIso _ _ _ _ _ (H.base₂ N hN)) (σV _ _) (σD _ _)).hom ≫
        traceAbstractCounit F P (P.obj N) (F.obj TY)
          (traceProjectionFromComparison a δF _ _) (H.projectionF _ (H.pushF N hN)) H.t =
      (conjugateIsoEquiv (a.comp a₂) (a.comp a₁) s.symm).hom.app
          (U₁.obj N ⊗ U₁.obj (F.obj TY)) ≫
        P.map (traceAbstractCounit U₁ Q₁ N (U₁.obj (F.obj TY))
          (traceProjectionFromComparison a₁ δ₁ _ _) (H.projectionP N hN) H.t₁)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The recorded ambient unbounded internal-module derived category.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
abbrev TraceD (Z : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))

/-- Loc(Dbc), using the recorded constant-model constructibility and localizing closure.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def TraceLoc (Z : Scheme.{u}) : ObjectProperty (TraceD Λ Z) :=
  CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ Z)

/-- Alias for the total left derived functor of the full module inverse image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePull {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ B ⥤ TraceD Λ Z :=
  moduleObjectDerivedPullback Λ h

/-- Alias for the total right derived functor of the full module direct image.
Source: blueprint standing setting (blueprint: lem-sfb-trace-base-change-first). -/
def tracePush {Z B : Scheme.{u}} (h : Z ⟶ B) : TraceD Λ Z ⥤ TraceD Λ B :=
  moduleObjectDerivedPushforward Λ h

/-- The existing canonical adjunction, with its functors named explicitly.
Source: blueprint derived module adjunction (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceAdjunction {Z B : Scheme.{u}} (h : Z ⟶ B) :
    tracePull Λ h ⊣ tracePush Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

variable {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)

/-- The canonical pullback composition with named functor endpoints.
Source: Stacks 0D6D (blueprint: lem-sfb-trace-base-change-first). -/
def tracePullComp {Z B C : Scheme.{u}} (a : Z ⟶ B) (b : B ⟶ C) :
    tracePull Λ (a ≫ b) ≅ tracePull Λ b ⋙ tracePull Λ a :=
  leftDerivedUpperStarComp Λ a b

/-- The canonical inverse-image square comparison, from the recorded composition maps.
Source: Stacks 07A7 (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def tracePullSquare (w : p ≫ f = q ≫ f) :
    tracePull Λ f ⋙ tracePull Λ q ≅ tracePull Λ f ⋙ tracePull Λ p :=
  (tracePullComp Λ q f).symm ≪≫
    eqToIso (congrArg (fun h : W ⟶ Y => tracePull Λ h) w.symm) ≪≫
      tracePullComp Λ p f


/-- The base twist R_Y(1)[2], its recorded integral line placed in degree zero.
Source: sk-def-sp-tate-twist (blueprint: lem-sfb-trace-base-change-first). -/
@[irreducible]
def traceTate (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Z : Scheme.{u}) : TraceD (Profinite.padicIntegersRingObj ℓ E.1) Z :=
  ((DerivedCategory.singleFunctor _ 0).obj (spIntegralTwist Z ℓ E)) ⟦(2 : ℤ)⟧


/-- The exact formula with all data fixed by the canonical internal-module operations.
The monoidal structures occur only in this proposition's body, avoiding the repeated
proof-irrelevance descent described in DerivedCategory/Complete/Defs.lean.
Source: blueprint first triangle (blueprint: lem-sfb-trace-base-change-first). -/
def TraceFirstAssertion {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)
    (sq : ChosenCartesianSquare p q f f) (TY : TraceD Λ Y) : Prop :=
  TraceFirstFormula (TraceLoc Λ Y) (TraceLoc Λ X) (TraceLoc Λ W)
    (tracePull Λ f) (tracePush Λ f)
    (tracePull Λ p) (tracePull Λ q)
    (tracePush Λ p) (tracePush Λ q)
    (traceAdjunction Λ f)
    (traceAdjunction Λ p) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w)
    (condensedDerivedUnitIso Λ f)
    (traceTensorComponent (tracePull Λ f)
      (condensedDerivedTensorComparison Λ f))
    (traceTensorComponent (tracePull Λ p)
      (condensedDerivedTensorComparison Λ p))
    (traceTensorComponent (tracePull Λ q)
      (condensedDerivedTensorComparison Λ q))
    (condensedDerivedSymmetry Λ X) (condensedDerivedSymmetry Λ W) TY

/-- Trace/base-change rearrangement before the first triangle, over O_E.
Source: blueprint main-20261015, sk-thm-int-restriction-line.proof.md, (1)
(blueprint: lem-sfb-trace-base-change-first).

Proof plan, following the seven DAG steps:
1. Use the canonical module adjunctions and Cartesian coefficient comparisons. The
ringed-derived monoidal comparison lemma identifies pullback compositions, symmetric
tensors and adjunction-compatible direct-image compositions. Write P=Rf*, F=f*,
Qi=Rpi*, Ui=pi*, T=F TY, A=PN, C=PT and H=U1 N tensor U2 T.
2. Form D2=P(lambda_q) P(b2 tensor 1) pi_f and
D1=P(pi_p) P(1 tensor b1) lambda_f. The definition of B gives
D2 followed by P(B) = pi_f; hence D2 is invertible by the stated hypotheses.
No invertibility is required of the auxiliary lambda_f at (N,C).
3. Transpose D2 under the composite adjunction. The adjunct-counit identity and
mate-counit equation reduce its transpose to U1(c_f,N) tensor U2(c_f,T).
4. Transpose D1 using the other factorization. Its mate-counit equation gives the
same tensor of counits. Injectivity of the Hom bijection yields D1=D2 with exactly
the conjugate square identification used below.
5. Precompose the left side with D2. Cancel the inverse projection in e to obtain
1_A tensor t, followed by the canonical right unitor.
6. Precompose the right side with D1. Cancel its inverse projection and use trace1.
Projection naturality in the scalar argument, from ringedProjectionTensorComposition,
and its tensor-unit normalization, from ringedProjectionMateExact, give the same
1_A tensor t. The comparisons include the unit isomorphism f* RY = RX.
7. Cancel the common isomorphism D2. This is the displayed equality for every N in
Loc(Dbc), without requiring any completeness or finite-Tor hypothesis on N. -/
theorem trace_base_change_first
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y W : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (p q : W ⟶ X) [p.IsOver (Spec (.of k))] [q.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare p q f f) :
    TraceFirstAssertion (Profinite.padicIntegersRingObj ℓ E.1) f p q sq
      (traceTate ℓ E Y) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
