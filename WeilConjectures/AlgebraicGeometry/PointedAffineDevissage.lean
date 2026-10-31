/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.FieldTheory.PurelyTranscendentalExtension

/-! # Pointed affine scheme dévissage data

Source: Stacks Project, flat.tex, Tags 05H4, 05H5, 05HH, 05HI, 05H9 and 05HL.
This auxiliary variant omits the equalities with support dimensions, as in Tag 05HX.
(blueprint: def-trf-pointed-scheme-devissage-data).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An elementary étale map of pointed schemes, including the residue-field isomorphism.
Source: Stacks, flat.tex, proposition-existence-complete-at-x, pointed étale neighbourhoods
(blueprint: def-trf-pointed-scheme-devissage-data). -/
def IsElementaryEtalePointed {U V : Scheme.{u}} (h : U ⟶ V) (u : U) (v : V) : Prop :=
  Etale h ∧ h u = v ∧ IsIso (h.residueFieldMap u)

/-- The one-step pointed affine datum; `d` is independent of support dimensions.
The equation `over` makes both arrows maps over the same base.
Source: Stacks, flat.tex, Tags 05H4 and 05H5, auxiliary variant from 05HX
(blueprint: def-trf-pointed-scheme-devissage-data). -/
structure PointedAffineOneStep {X B : Scheme.{u}} (f : X ⟶ B) (F : X.Modules) (x : X) where
  locallyOfFiniteType : LocallyOfFiniteType f
  finiteType : Scheme.Modules.IsQuasiCoherentFiniteType F
  affineX : IsAffine X
  affineB : IsAffine B
  Z : Scheme.{u}
  Y : Scheme.{u}
  affineZ : IsAffine Z
  affineY : IsAffine Y
  i : Z ⟶ X
  π : Z ⟶ Y
  g : Y ⟶ B
  over : i ≫ f = π ≫ g
  closed : IsClosedImmersion i
  finitePresentation : LocallyOfFinitePresentation i
  finite : IsFinite π
  smooth : Smooth g
  geometricallyIrreducible : GeometricallyIrreducible g
  d : ℕ
  fibreDimension : ∀ b : B, topologicalKrullDim (g.fiber b) = (d : WithBot ℕ∞)
  G : Z.Modules
  finiteTypeG : Scheme.Modules.IsQuasiCoherentFiniteType G
  presentation : (Scheme.Modules.pushforward i).obj G ≅ F
  z : Z
  y : Y
  markedX : i z = x
  markedY : π z = y
  markedBase : g y = f x
  singletonFibre : ∀ t : Z, π t = y ↔ t = z
  purelyTranscendental : @Algebra.IsPurelyTranscendentalExtension
    (B.residueField (g y)) (Y.residueField y) _ _ (g.residueFieldMap y).hom.toAlgebra

/-- The actual stalk map tensored with the residue field is bijective.
The tensor product is `H_ξ ⊗ κ(ξ)`, with its canonical local-ring action.
Source: Stacks, flat.tex, Tag 05HH, clause (2)
(blueprint: def-trf-pointed-scheme-devissage-data). -/
def IsResidueFibreIso {Y : Scheme.{u}} {H K : Y.Modules} (α : H ⟶ K) (ξ : Y) : Prop :=
  letI := (Y.residue ξ).hom.toAlgebra
  Function.Bijective (LinearMap.rTensor (Y.residueField ξ)
    ((RingedSpace.moduleStalkFunctor Y.toRingedSpace ξ).map α).hom)

/-- A finite complete pointed chain. The recursive input is exactly the previous cokernel.
The nil constructor permits length zero precisely for an affine zero-module situation.
`free (ULift (Fin r))` is the finite sum of `r` copies of the structure sheaf, also for `r = 0`.
Source: Stacks, flat.tex, Tags 05HH and 05HI, with the explicit auxiliary zero-length convention
(blueprint: def-trf-pointed-scheme-devissage-data). -/
inductive PointedAffineDevissage (B : Scheme.{u}) :
    {X : Scheme.{u}} → (X ⟶ B) → (F : X.Modules) → X → ℕ → Type (u + 1)
  | nil {X : Scheme.{u}} (f : X ⟶ B) (F : X.Modules) (x : X)
      (hf : LocallyOfFiniteType f) (hF : Scheme.Modules.IsQuasiCoherentFiniteType F)
      (hX : IsAffine X) (hB : IsAffine B) (zero : IsZero F) :
      PointedAffineDevissage B f F x 0
  | cons {X : Scheme.{u}} {f : X ⟶ B} {F : X.Modules} {x : X} {n : ℕ}
      (s : PointedAffineOneStep f F x) (r : ℕ)
      (α : SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s.π).obj s.G)
      (genericIso : ∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α (s.g.fiberι (f x) ξ))
      (tail : PointedAffineDevissage B s.g (cokernel α) s.y n) :
      PointedAffineDevissage B f F x (n + 1)

namespace PointedAffineDevissage

/-- The canonical comparison from restriction of a pushforward to pushforward of restriction.
It is the adjunction mate of the restriction unit on `G`; thus no arbitrary comparison is chosen.
Source: Stacks, flat.tex, Tags 05H9 and 05HL, restriction of the displayed diagrams
(blueprint: def-trf-pointed-scheme-devissage-data). -/
noncomputable def restrictionPushforwardMap
    {T W T' W' : Scheme.{u}} (p : T ⟶ W) (p' : T' ⟶ W')
    (a : W' ⟶ W) (c : T' ⟶ T) [IsOpenImmersion a] [IsOpenImmersion c]
    (square : c ≫ p = p' ≫ a) (G : T.Modules) :
    (Scheme.Modules.restrictFunctor a).obj ((Scheme.Modules.pushforward p).obj G) ⟶
      (Scheme.Modules.pushforward p').obj ((Scheme.Modules.restrictFunctor c).obj G) :=
  ((Scheme.Modules.restrictAdjunction a).homEquiv _ _).symm
    ((Scheme.Modules.pushforward p).map ((Scheme.Modules.restrictAdjunction c).unit.app G) ≫
      (Scheme.Modules.pushforwardComp c p).hom.app _ ≫
      eqToHom (congrArg (fun k ↦ (Scheme.Modules.pushforward k).obj
        ((Scheme.Modules.restrictFunctor c).obj G)) square) ≫
      (Scheme.Modules.pushforwardComp p' a).inv.app _)

/-- For an open immersion, this says its image is a principal open of its target.
On an affine target this is precisely a standard affine open `D(a)`.
Source: Stacks, flat.tex, Tags 05H9 and 05HL
(blueprint: def-trf-pointed-scheme-devissage-data). -/
def HasPrincipalRange {T' T : Scheme.{u}} (a : T' ⟶ T) : Prop :=
  ∃ t : Γ(T, ⊤), Set.range a = (T.basicOpen t : Set T)

/-- Restriction of a one-step datum, including the restriction of its presentation isomorphism.
Both old and new data already satisfy every one-step condition.
Source: Stacks, flat.tex, Tag 05H9
(blueprint: def-trf-pointed-scheme-devissage-data). -/
structure OneStepShrinking {X B X' B' : Scheme.{u}}
    {f : X ⟶ B} {f' : X' ⟶ B'} {F : X.Modules} {F' : X'.Modules}
    {x : X} {x' : X'} (s : PointedAffineOneStep f F x) (s' : PointedAffineOneStep f' F' x')
    (aB : B' ⟶ B) (aX : X' ⟶ X) [IsOpenImmersion aB] [IsOpenImmersion aX]
    (eF : (Scheme.Modules.restrictFunctor aX).obj F ≅ F') where
  baseSquare : aX ≫ f = f' ≫ aB
  principalB : HasPrincipalRange aB
  principalX : HasPrincipalRange aX
  markedX : aX x' = x
  aZ : s'.Z ⟶ s.Z
  aY : s'.Y ⟶ s.Y
  openZ : IsOpenImmersion aZ
  openY : IsOpenImmersion aY
  principalZ : HasPrincipalRange aZ
  principalY : HasPrincipalRange aY
  closedSquare : aZ ≫ s.i = s'.i ≫ aX
  finiteSquare : aZ ≫ s.π = s'.π ≫ aY
  smoothSquare : aY ≫ s.g = s'.g ≫ aB
  markedZ : aZ s'.z = s.z
  markedY : aY s'.y = s.y
  moduleIso : (@Scheme.Modules.restrictFunctor _ _ aZ openZ).obj s.G ≅ s'.G
  presentationSquare : (Scheme.Modules.restrictFunctor aX).map s.presentation.hom ≫ eF.hom =
    @restrictionPushforwardMap _ _ _ _ s.i s'.i aX aZ _ openZ closedSquare s.G ≫
      (Scheme.Modules.pushforward s'.i).map moduleIso.hom ≫ s'.presentation.hom
  dimension : s'.d = s.d

attribute [instance] OneStepShrinking.openZ OneStepShrinking.openY

/-- A standard shrinking of a complete chain, with its given restriction identifications.
The principal open immersions contain all marked points. In each positive-length step,
`alphaSquare` restricts the basis map using the canonical free-module comparison, and
`quotientSquare` makes the next input identification the one induced on cokernels.
The one-step presentation square also restricts the original presentation isomorphism.
Thus all the displayed maps and isomorphisms, and not just their objects, are retained.
Source: Stacks, flat.tex, Tags 05H9 and 05HL
(blueprint: def-trf-pointed-scheme-devissage-data). -/
inductive StandardShrinking {B B' : Scheme.{u}} (aB : B' ⟶ B) [IsOpenImmersion aB] :
    {X X' : Scheme.{u}} → {f : X ⟶ B} → {f' : X' ⟶ B'} →
    {F : X.Modules} → {F' : X'.Modules} → {x : X} → {x' : X'} → {n : ℕ} →
    PointedAffineDevissage B f F x n → PointedAffineDevissage B' f' F' x' n →
    (aX : X' ⟶ X) → (haX : IsOpenImmersion aX) →
    ((@Scheme.Modules.restrictFunctor _ _ aX haX).obj F ≅ F') → Type (u + 1)
  | nil {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
      {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'}
      {hf : LocallyOfFiniteType f} {hf' : LocallyOfFiniteType f'}
      {hF : Scheme.Modules.IsQuasiCoherentFiniteType F}
      {hF' : Scheme.Modules.IsQuasiCoherentFiniteType F'}
      {hX : IsAffine X} {hX' : IsAffine X'} {hB : IsAffine B} {hB' : IsAffine B'}
      {zero : IsZero F} {zero' : IsZero F'}
      (aX : X' ⟶ X) (haX : IsOpenImmersion aX)
      (eF : (@Scheme.Modules.restrictFunctor _ _ aX haX).obj F ≅ F')
      (baseSquare : aX ≫ f = f' ≫ aB)
      (principalB : HasPrincipalRange aB) (principalX : HasPrincipalRange aX)
      (markedX : aX x' = x) :
      StandardShrinking aB (.nil f F x hf hF hX hB zero)
        (.nil f' F' x' hf' hF' hX' hB' zero') aX haX eF
  | cons {X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
      {F : X.Modules} {F' : X'.Modules} {x : X} {x' : X'} {n r : ℕ}
      {s : PointedAffineOneStep f F x} {s' : PointedAffineOneStep f' F' x'}
      {α : SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s.π).obj s.G}
      {α' : SheafOfModules.free (R := s'.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
        (Scheme.Modules.pushforward s'.π).obj s'.G}
      {genericIso : ∀ ξ : s.g.fiber (f x), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α (s.g.fiberι (f x) ξ)}
      {genericIso' : ∀ ξ : s'.g.fiber (f' x'), IsGenericPoint ξ Set.univ →
        IsResidueFibreIso α' (s'.g.fiberι (f' x') ξ)}
      {tail : PointedAffineDevissage B s.g (cokernel α) s.y n}
      {tail' : PointedAffineDevissage B' s'.g (cokernel α') s'.y n}
      (aX : X' ⟶ X) [haX : IsOpenImmersion aX]
      (eF : (Scheme.Modules.restrictFunctor aX).obj F ≅ F')
      (R : OneStepShrinking s s' aB aX eF)
      (eQ : (Scheme.Modules.restrictFunctor R.aY).obj (cokernel α) ≅ cokernel α')
      (alphaSquare :
        SheafOfModules.mapFree (Scheme.Modules.restrictFunctor R.aY)
          (ULift.{u} (Fin r)) (Scheme.Modules.restrictUnitIso R.aY).inv ≫
          (Scheme.Modules.restrictFunctor R.aY).map α ≫
          restrictionPushforwardMap s.π s'.π R.aY R.aZ R.finiteSquare s.G ≫
          (Scheme.Modules.pushforward s'.π).map R.moduleIso.hom = α')
      (quotientSquare :
        (Scheme.Modules.restrictFunctor R.aY).map (cokernel.π α) ≫ eQ.hom =
          restrictionPushforwardMap s.π s'.π R.aY R.aZ R.finiteSquare s.G ≫
          (Scheme.Modules.pushforward s'.π).map R.moduleIso.hom ≫ cokernel.π α')
      (tailShrinking : StandardShrinking aB tail tail' R.aY R.openY eQ) :
      StandardShrinking aB (.cons s r α genericIso tail)
        (.cons s' r α' genericIso' tail') aX haX eF

end PointedAffineDevissage
end AlgebraicGeometry
