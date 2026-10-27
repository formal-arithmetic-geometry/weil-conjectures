/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.PointedAffineDevissage
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.FiniteSingletonFibreLocalization
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents

/-! # Pointed base change and standard shrinking of affine dévissage

Source: Stacks Project, flat.tex, Tags 05H7--05HA and 05HJ--05HM, for the auxiliary
support-dimension-free data (blueprint: lem-trf-devissage-pointed-restriction).
The comparison structures below record the actual pullbacks of the given diagrams,
presentations, basis maps and cokernels. They contain no existence assumptions.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PointedAffineDevissage

/-- The base-changed one-step diagram. The two Cartesian squares identify the new
schemes with base changes; the presentation uses the canonical pushforward comparison.
The marked points are the unique lifts over the specified new base point.
Source: Stacks, 05H7 and 05H8 (blueprint: lem-trf-devissage-pointed-restriction). -/
structure OneStepBaseChange {X B X' B' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {F : X.Modules} {F' : X'.Modules}
    {x : X} {x' : X'} (s : PointedAffineOneStep f F x) (s' : PointedAffineOneStep f' F' x')
    (aB : B' ⟶ B) (aX : X' ⟶ X)
    (eF : (Scheme.Modules.tensorPullback aX).obj F ≅ F') where
  baseSquare : IsPullback aX f' f aB
  markedX : aX x' = x
  uniqueX : ∀ t : X', aX t = x → f' t = f' x' → t = x'
  aZ : s'.Z ⟶ s.Z
  aY : s'.Y ⟶ s.Y
  closedSquare : IsPullback aZ s'.i s.i aX
  finiteSquare : IsPullback aZ s'.π s.π aY
  smoothSquare : IsPullback aY s'.g s.g aB
  markedZ : aZ s'.z = s.z
  markedY : aY s'.y = s.y
  uniqueZ : ∀ t : s'.Z, aZ t = s.z → (s'.i ≫ f') t = f' x' → t = s'.z
  uniqueY : ∀ t : s'.Y, aY t = s.y → s'.g t = f' x' → t = s'.y
  moduleIso : (Scheme.Modules.tensorPullback aZ).obj s.G ≅ s'.G
  presentationSquare : (Scheme.Modules.tensorPullback aX).map s.presentation.hom ≫ eF.hom =
    Scheme.Modules.moduleBaseChangeMap s.i s'.i aX aZ closedSquare.w s.G ≫
      (Scheme.Modules.pushforward s'.i).map moduleIso.hom ≫ s'.presentation.hom
  dimension : s'.d = s.d

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Base change of a chain, using the canonical finite-pushforward map at every step.
The next input is identified by the induced map on cokernels, not an unrelated isomorphism.
Source: Stacks, 05HJ and 05HK (blueprint: lem-trf-devissage-pointed-restriction). -/
inductive ChainBaseChange {B B' : Scheme.{u}} (aB : B' ⟶ B) :
    {X X' : Scheme.{u}} → {f : X ⟶ B} → {f' : X' ⟶ B'} →
    {F : X.Modules} → {F' : X'.Modules} → {x : X} → {x' : X'} → {n : ℕ} →
    PointedAffineDevissage B f F x n → PointedAffineDevissage B' f' F' x' n →
    (aX : X' ⟶ X) → ((Scheme.Modules.tensorPullback aX).obj F ≅ F') → Prop
  | nil {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
      {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'}
      {hf : LocallyOfFiniteType f} {hf' : LocallyOfFiniteType f'}
      {hF : Scheme.Modules.IsQuasiCoherentFiniteType F}
      {hF' : Scheme.Modules.IsQuasiCoherentFiniteType F'}
      {hX : IsAffine X} {hX' : IsAffine X'} {hB : IsAffine B} {hB' : IsAffine B'}
      {zero : IsZero F} {zero' : IsZero F'} (aX : X' ⟶ X)
      (eF : (Scheme.Modules.tensorPullback aX).obj F ≅ F')
      (sq : IsPullback aX f' f aB) (marked : aX x' = x)
      (unique : ∀ t : X', aX t = x → f' t = f' x' → t = x') :
      ChainBaseChange aB (.nil f F x hf hF hX hB zero)
        (.nil f' F' x' hf' hF' hX' hB' zero') aX eF
  | cons {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
      {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} {n r : ℕ}
      {s : PointedAffineOneStep f F x} {s' : PointedAffineOneStep f' F' x'}
      {α : SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s.π).obj s.G}
      {α' : SheafOfModules.free (R := s'.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s'.π).obj s'.G}
      {hα : ∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α (s.g.fiberι (f x) ξ)}
      {hα' : ∀ ξ : s'.g.fiber (f' x'), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α' (s'.g.fiberι (f' x') ξ)}
      {tail : PointedAffineDevissage B s.g (cokernel α) s.y n}
      {tail' : PointedAffineDevissage B' s'.g (cokernel α') s'.y n}
      (aX : X' ⟶ X) (eF : (Scheme.Modules.tensorPullback aX).obj F ≅ F')
      (R : OneStepBaseChange s s' aB aX eF)
      (eQ : (Scheme.Modules.tensorPullback R.aY).obj (cokernel α) ≅ cokernel α')
      (alphaSquare : ∀ k : ULift.{u} (Fin r),
        (Scheme.Modules.tensorPullback R.aY).map
          (SheafOfModules.ιFree (R := s.Y.ringCatSheaf) k) ≫
          (Scheme.Modules.tensorPullback R.aY).map α ≫
          Scheme.Modules.moduleBaseChangeMap s.π s'.π R.aY R.aZ R.finiteSquare.w s.G ≫
          (Scheme.Modules.pushforward s'.π).map R.moduleIso.hom =
            Scheme.Modules.tensorPullbackObjUnitToUnit R.aY ≫
              SheafOfModules.ιFree (R := s'.Y.ringCatSheaf) k ≫ α')
      (quotientSquare :
        (Scheme.Modules.tensorPullback R.aY).map (cokernel.π α) ≫ eQ.hom =
          Scheme.Modules.moduleBaseChangeMap s.π s'.π R.aY R.aZ R.finiteSquare.w s.G ≫
          (Scheme.Modules.pushforward s'.π).map R.moduleIso.hom ≫ cokernel.π α')
      (tailChange : ChainBaseChange aB tail tail' R.aY eQ) :
      ChainBaseChange aB (.cons s r α hα tail) (.cons s' r α' hα' tail') aX eF

/-- Package the schemes and inclusions of a one-step standard shrinking.
Source: Stacks, 05HA (blueprint: lem-trf-devissage-pointed-restriction). -/
structure OneStepRestriction {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X}
    (s : PointedAffineOneStep f F x) where
  B' : Scheme.{u}
  X' : Scheme.{u}
  f' : X' ⟶ B'
  F' : X'.Modules
  x' : X'
  s' : PointedAffineOneStep f' F' x'
  aB : B' ⟶ B
  aX : X' ⟶ X
  openB : IsOpenImmersion aB
  openX : IsOpenImmersion aX
  eF : (@Scheme.Modules.restrictFunctor _ _ aX openX).obj F ≅ F'
  comparison : @OneStepShrinking _ _ _ _ f f' F F' x x' s s' aB aX openB openX eF
  finiteCartesian : IsPullback comparison.aZ s'.π s.π comparison.aY

attribute [instance] OneStepRestriction.openB OneStepRestriction.openX

/-- Package a standard shrinking without choosing any maps arbitrarily.
Source: Stacks, 05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
structure ChainRestriction {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
    (c : PointedAffineDevissage B f F x n) where
  B' : Scheme.{u}
  X' : Scheme.{u}
  f' : X' ⟶ B'
  F' : X'.Modules
  x' : X'
  c' : PointedAffineDevissage B' f' F' x' n
  aB : B' ⟶ B
  aX : X' ⟶ X
  openB : IsOpenImmersion aB
  openX : IsOpenImmersion aX
  eF : (@Scheme.Modules.restrictFunctor _ _ aX openX).obj F ≅ F'
  comparison : @StandardShrinking _ _ aB openB _ _ f f' F F' x x' n c c' aX openX eF

attribute [instance] ChainRestriction.openB ChainRestriction.openX

/-- The final target (the initial scheme in length zero).
Source: Stacks, 05HH, 05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
noncomputable def lastScheme {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
    (c : PointedAffineDevissage B f F x n) : Scheme.{u} :=
  match c with
  | .nil .. => X
  | .cons _ _ _ _ tail => lastScheme tail
termination_by structural c

/-- The final marked point.
Source: Stacks, 05HI, 05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
noncomputable def lastPoint {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
    (c : PointedAffineDevissage B f F x n) : lastScheme c :=
  match c with
  | .nil .. => x
  | .cons _ _ _ _ tail => lastPoint tail
termination_by structural c

/-- The final target's structure map.
Source: Stacks, 05HH, 05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
noncomputable def lastStructureMap {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
    (c : PointedAffineDevissage B f F x n) : lastScheme c ⟶ B :=
  match c with
  | .nil .. => f
  | .cons _ _ _ _ tail => lastStructureMap tail
termination_by structural c

/-- The target images of all positive steps of a standard shrinking, in chain order.
Source: Stacks, 05HL, 05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
noncomputable def targetImages {B B' : Scheme.{u}} {aB : B' ⟶ B} [hB : IsOpenImmersion aB]
    {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} {n : ℕ}
    {c : PointedAffineDevissage B f F x n} {c' : PointedAffineDevissage B' f' F' x' n}
    {aX : X' ⟶ X} {haX : IsOpenImmersion aX}
    {eF : (@Scheme.Modules.restrictFunctor _ _ aX haX).obj F ≅ F'}
    (R : @StandardShrinking B B' aB hB X X' f f' F F' x x' n c c' aX haX eF) :
    List ((T : Scheme.{u}) × Set T) :=
  StandardShrinking.rec
    (motive := fun {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _ ↦ List ((T : Scheme.{u}) × Set T))
    (fun {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ ↦ [])
    (fun {_ _ _ _ _ _ _ _ _ _ s _ _ _ _ _ _ _} _ [_] _ R _ _ _ _ images ↦
      ⟨s.Y, Set.range R.aY⟩ :: images) R

/-- Every marked residue map in a chain shrinking, including its initial and base maps.
Source: Stacks, 05HL (blueprint: lem-trf-devissage-pointed-restriction). -/
def MarkedResidueIsos {B B' : Scheme.{u}} {aB : B' ⟶ B} [hB : IsOpenImmersion aB]
    {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} {n : ℕ}
    {c : PointedAffineDevissage B f F x n} {c' : PointedAffineDevissage B' f' F' x' n}
    {aX : X' ⟶ X} {haX : IsOpenImmersion aX}
    {eF : (@Scheme.Modules.restrictFunctor _ _ aX haX).obj F ≅ F'}
    (R : @StandardShrinking B B' aB hB X X' f f' F F' x x' n c c' aX haX eF) : Prop :=
  StandardShrinking.rec
    (motive := fun {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _ ↦ Prop)
    (fun {_ _ _ f' _ _ _ x' _ _ _ _ _ _ _ _ _ _} aX _ _ _ _ _ _ ↦
      IsIso (aB.residueFieldMap (f' x')) ∧ IsIso (aX.residueFieldMap x'))
    (fun {_ _ _ _ _ _ _ x' _ _ _ s' _ _ _ _ _ _} aX [_] _ R _ _ _ _ residues ↦
      IsIso (aX.residueFieldMap x') ∧ IsIso (R.aZ.residueFieldMap s'.z) ∧
        IsIso (R.aY.residueFieldMap s'.y) ∧ residues) R

/-- In a base-only shrinking every scheme is exactly the inverse image of the base open.
Source: Stacks, 05HA(1), 05HM(1) (blueprint: lem-trf-devissage-pointed-restriction). -/
def BaseRestrictionImages {B B' : Scheme.{u}} {aB : B' ⟶ B} [hB : IsOpenImmersion aB]
    {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} {n : ℕ}
    {c : PointedAffineDevissage B f F x n} {c' : PointedAffineDevissage B' f' F' x' n}
    {aX : X' ⟶ X} {haX : IsOpenImmersion aX}
    {eF : (@Scheme.Modules.restrictFunctor _ _ aX haX).obj F ≅ F'}
    (R : @StandardShrinking B B' aB hB X X' f f' F F' x x' n c c' aX haX eF) : Prop :=
  StandardShrinking.rec
    (motive := fun {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _ ↦ Prop)
    (fun {_ _ f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} aX _ _ _ _ _ _ ↦
      Set.range aX = f ⁻¹' Set.range aB)
    (fun {_ _ f _ _ _ _ _ _ _ s _ _ _ _ _ _ _} aX [_] _ R _ _ _ _ images ↦
      Set.range aX = f ⁻¹' Set.range aB ∧
      Set.range R.aZ = (s.i ≫ f) ⁻¹' Set.range aB ∧
      Set.range R.aY = s.g ⁻¹' Set.range aB ∧ images) R

/-- All base-change and shrinking assertions for one-step data, including an auxiliary basis
map when supplied. The requests on the initial and target opens can be made after any
prescribed principal base restriction; the base-only request keeps its exact inverse image.
Source: Stacks, 05H7--05HA and the cokernel calculation in 05HJ
(blueprint: lem-trf-devissage-pointed-restriction). -/
def OneStepRestrictionProperties : Prop :=
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X}
      (s : PointedAffineOneStep f F x)
      (B' : Scheme.{u}) [IsAffine B'] (aB : B' ⟶ B) (b' : B')
      (_hb : aB b' = f x) (_hk : IsIso (aB.residueFieldMap b')),
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ B') (aX : X' ⟶ X) (x' : X')
      (s' : PointedAffineOneStep f' ((Scheme.Modules.tensorPullback aX).obj F) x'),
      f' x' = b' ∧ Nonempty (OneStepBaseChange s s' aB aX (Iso.refl _))) ∧
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X}
      (s : PointedAffineOneStep f F x) (a : Γ(B, ⊤)) (_ha : f x ∈ B.basicOpen a),
    (∃ R : OneStepRestriction s,
      Set.range R.aB = (B.basicOpen a : Set B) ∧
      Set.range R.aX = f ⁻¹' (B.basicOpen a : Set B) ∧
      Set.range R.comparison.aY = s.g ⁻¹' (B.basicOpen a : Set B) ∧
      Set.range R.comparison.aZ = (s.i ≫ f) ⁻¹' (B.basicOpen a : Set B)) ∧
    (∀ w : Γ(s.Y, ⊤), s.y ∈ s.Y.basicOpen w → ∃ R : OneStepRestriction s,
      Set.range R.aB ⊆ (B.basicOpen a : Set B) ∧
      Set.range R.comparison.aY =
        (s.Y.basicOpen w : Set s.Y) ∩ s.g ⁻¹' Set.range R.aB) ∧
    (∀ U : X.Opens, x ∈ U → ∃ R : OneStepRestriction s,
      Set.range R.aB ⊆ (B.basicOpen a : Set B) ∧ Set.range R.aX ⊆ (U : Set X))) ∧
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X}
      (s : PointedAffineOneStep f F x) (R : OneStepRestriction s)
      (r : ℕ) (α : SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s.π).obj s.G)
      (_hα : ∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α (s.g.fiberι (f x) ξ)),
    ∃ (α' : SheafOfModules.free (R := R.s'.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward R.s'.π).obj R.s'.G)
      (eQ : (Scheme.Modules.restrictFunctor R.comparison.aY).obj (cokernel α) ≅ cokernel α'),
      (∀ ξ : R.s'.g.fiber (R.f' R.x'), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α' (R.s'.g.fiberι (R.f' R.x') ξ)) ∧
      SheafOfModules.mapFree (Scheme.Modules.restrictFunctor R.comparison.aY)
        (ULift.{u} (Fin r)) (Scheme.Modules.restrictUnitIso R.comparison.aY).inv ≫
        (Scheme.Modules.restrictFunctor R.comparison.aY).map α ≫
        restrictionPushforwardMap s.π R.s'.π R.comparison.aY R.comparison.aZ
          R.comparison.finiteSquare s.G ≫
        (Scheme.Modules.pushforward R.s'.π).map R.comparison.moduleIso.hom = α' ∧
      (Scheme.Modules.restrictFunctor R.comparison.aY).map (cokernel.π α) ≫ eQ.hom =
        restrictionPushforwardMap s.π R.s'.π R.comparison.aY R.comparison.aZ
          R.comparison.finiteSquare s.G ≫
        (Scheme.Modules.pushforward R.s'.π).map R.comparison.moduleIso.hom ≫ cokernel.π α') ∧
  (∀ {X B X' B' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
      {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'}
      (s : PointedAffineOneStep f F x) (s' : PointedAffineOneStep f' F' x')
      (aB : B' ⟶ B) (aX : X' ⟶ X) [IsOpenImmersion aB] [IsOpenImmersion aX]
      (eF : (Scheme.Modules.restrictFunctor aX).obj F ≅ F')
      (R : OneStepShrinking s s' aB aX eF),
    IsIso (aB.residueFieldMap (f' x')) ∧ IsIso (aX.residueFieldMap x') ∧
      IsIso (R.aZ.residueFieldMap s'.z) ∧ IsIso (R.aY.residueFieldMap s'.y))

/-- All requests for complete chains. `n = 0` is included, and only the last-target request
requires positive length. The chain comparison retains all dimensions and cokernel maps.
Source: Stacks, 05HJ--05HM (blueprint: lem-trf-devissage-pointed-restriction). -/
def ChainRestrictionProperties : Prop :=
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
      (c : PointedAffineDevissage B f F x n)
      (B' : Scheme.{u}) [IsAffine B'] (aB : B' ⟶ B) (b' : B')
      (_hb : aB b' = f x) (_hk : IsIso (aB.residueFieldMap b')),
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ B') (aX : X' ⟶ X) (x' : X')
      (c' : PointedAffineDevissage B' f' ((Scheme.Modules.tensorPullback aX).obj F) x' n),
      f' x' = b' ∧ ChainBaseChange aB c c' aX (Iso.refl _)) ∧
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
      (c : PointedAffineDevissage B f F x n)
      (a : Γ(B, ⊤)) (_ha : f x ∈ B.basicOpen a),
    (∃ R : ChainRestriction c,
      Set.range R.aB = (B.basicOpen a : Set B) ∧
      BaseRestrictionImages R.comparison) ∧
    (∀ U : X.Opens, x ∈ U → ∃ R : ChainRestriction c,
      Set.range R.aB ⊆ (B.basicOpen a : Set B) ∧ Set.range R.aX ⊆ (U : Set X)) ∧
    (0 < n → ∀ w : Γ(lastScheme c, ⊤), lastPoint c ∈ (lastScheme c).basicOpen w →
      ∃ R : ChainRestriction c, Set.range R.aB ⊆ (B.basicOpen a : Set B) ∧
        (targetImages R.comparison).getLast? =
          some ⟨lastScheme c, ((lastScheme c).basicOpen w : Set (lastScheme c)) ∩
            lastStructureMap c ⁻¹' Set.range R.aB⟩)) ∧
  (∀ {X B : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
      (c : PointedAffineDevissage B f F x n) (R : ChainRestriction c),
    MarkedResidueIsos R.comparison)

/-- Pointed base change and standard shrinking preserve the auxiliary affine dévissage data.
Source: Stacks Project, flat.tex, Tags 05H7--05HA and 05HJ--05HM
(blueprint: lem-trf-devissage-pointed-restriction).
Proof: (1) Base-change the affine diagrams; local finite type, closed finite presentation,
finite and smooth maps persist. Geometrically irreducible fibres persist by their fibre
formula. Smooth relative dimensions persist; the equidimensional local-dimension and
Noetherian component lemmas identify the Krull dimensions with the original integers.
(2) Pullback preserves quasi-coherence and finite generation, using affine tensor sections.
Affine pushforward base change gives the presentation and finite-pushforward comparisons.
(3) The marked fibre is unchanged because the base residue map is invertible, giving the
unique lifts, singleton fibres and the same purely transcendental residue extension.
(4) Pull back each basis map through that comparison. Tensor right exactness identifies
its cokernel with the pullback of the old one; the stalk formula preserves the generic
residue isomorphism. The terminal zero cokernel remains zero.
(5) A prescribed principal base restriction is a special case; inverse images and finite
intersections of principal opens remain principal.
(6) For a principal target open, smooth openness supplies a principal base neighbourhood
inside its image. Its fibres are nonempty opens in the old geometrically irreducible
fibres, with the same dimension. Lift the target's defining function across the affine
closed immersion and intersect its principal open with the inverse base open.
(7) For an initial open, choose a principal neighbourhood inside it, then apply the finite
singleton-fibre neighbourhood lemma to obtain a target open whose inverse image lies
inside it; apply (6) and intersect the initial open once more.
(8) Restrict basis maps through the canonical pushforward comparison. Cokernels restrict
by right exactness, and the nonempty fibre open has the same generic point and residue
field, so the generic isomorphism persists.
(9) For a chain's last target, apply (6) backwards, matching adjacent targets and initial
schemes and restricting the already treated tail only on the base. The cokernels match
by (8). (10) For an initial open, induct on length using (7) for the head and the induction
hypothesis for the tail, then (6) to match them; compose principal base restrictions.
(11) Length zero has zero initial module, and restriction and pullback preserve zero;
choose a principal initial neighbourhood when needed. Every shrinking inclusion is open
and therefore induces an isomorphism on marked residue fields. -/
theorem pointed_devissage_baseChange_and_shrinking :
    OneStepRestrictionProperties.{u} ∧ ChainRestrictionProperties.{u} := by
  sorry

end AlgebraicGeometry.PointedAffineDevissage
