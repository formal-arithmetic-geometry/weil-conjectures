/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Comma.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePullbackChartTensorFlatStalks
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.PointwiseModuleFlatnessBaseChange
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange
import Sheaf.RingTheory.FlatModuleFibreProductPatching
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Relative flat-module patching on an algebraic space

Source: Stacks Project, spaces-pushouts.tex, Tag 08KV, equivalence and part (b)
(blueprint: lem-sfb-space-relative-flat-module-pushout).

The categories below have all module homomorphisms. Natural identifications of the two
restriction functors, compatible with tensor associativity, specify the restriction
functor up to natural isomorphism, including its action on arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace.RelativeFlatModulePatching

/-- A scheme map as a map of its represented algebraic spaces.
Source: Stacks, Tags 025Y and 08KV
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
def schemeMap {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U) :
    schemeSpace T ⟶ schemeSpace U :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map f)

/-- The base span and its three cartesian inverse images, with the canonical overlap maps.
The projection equations uniquely determine the overlap maps by the pullback properties.
Source: Stacks, Tag 08KV, notation preceding the equivalence
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
structure Diagram (S : Scheme.{u}) where
  T₀ : Over S
  T₁ : Over S
  T₂ : Over S
  P : Over S
  i : T₀ ⟶ T₁
  a : T₀ ⟶ T₂
  j₂ : T₂ ⟶ P
  j₁ : T₁ ⟶ P
  V : AlgebraicSpace S
  h : V ⟶ schemeSpace P
  V₀ : AlgebraicSpace S
  V₁ : AlgebraicSpace S
  V₂ : AlgebraicSpace S
  r₀ : V₀ ⟶ V
  r₁ : V₁ ⟶ V
  r₂ : V₂ ⟶ V
  t₀ : V₀ ⟶ schemeSpace T₀
  t₁ : V₁ ⟶ schemeSpace T₁
  t₂ : V₂ ⟶ schemeSpace T₂
  cartesian₀ : IsPullback r₀.hom t₀.hom h.hom (schemeMap (a ≫ j₂)).hom
  cartesian₁ : IsPullback r₁.hom t₁.hom h.hom (schemeMap j₁).hom
  cartesian₂ : IsPullback r₂.hom t₂.hom h.hom (schemeMap j₂).hom
  a₂ : V₀ ⟶ V₂
  a₁ : V₀ ⟶ V₁
  a₂_r : a₂ ≫ r₂ = r₀
  a₁_r : a₁ ≫ r₁ = r₀
  a₂_t : a₂ ≫ t₂ = t₀ ≫ schemeMap a
  a₁_t : a₁ ≫ t₁ = t₀ ≫ schemeMap i

/-- Quasi-coherent modules relatively flat over the indicated base, with all module maps.
Source: Stacks, Tag 08KV, category (1) and conditions (2)(a,b)
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
abbrev FlatQCoh {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :=
  ObjectProperty.FullSubcategory
    (fun M : X.Modules ↦ M.IsQuasicoherent ∧ ModuleIsFlatOver f M)

/-- The overlap triples before imposing quasi-coherence, relative flatness and invertibility.
Comma morphisms are precisely pairs of module maps commuting with the overlap comparison.
Source: Stacks, Tag 08KV, category (2)
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
abbrev ModuleTriple {S : Scheme.{u}} (D : Diagram S) :=
  Comma (moduleTensorPullback D.a₂) (moduleTensorPullback D.a₁)

/-- Exactly the admissible triples in Tag 08KV, without finiteness or support conditions.
Source: Stacks, Tag 08KV, category (2), correcting its X to X-prime in (2)(b)
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
def AdmissibleTriple {S : Scheme.{u}} (D : Diagram S) (M : ModuleTriple D) : Prop :=
  M.left.IsQuasicoherent ∧ ModuleIsFlatOver D.t₂ M.left ∧
    M.right.IsQuasicoherent ∧ ModuleIsFlatOver D.t₁ M.right ∧ IsIso M.hom

/-- The category of relatively flat quasi-coherent overlap triples and all compatible maps.
Source: Stacks, Tag 08KV, category (2)
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
abbrev FlatTriple {S : Scheme.{u}} (D : Diagram S) :=
  ObjectProperty.FullSubcategory (AdmissibleTriple D)

/-- Forget a flat triple to its module on V₂, including its component on morphisms.
Source: Stacks, Tag 08KV (blueprint: lem-sfb-space-relative-flat-module-pushout). -/
def leftForget {S : Scheme.{u}} (D : Diagram S) : FlatTriple D ⥤ D.V₂.Modules :=
  ObjectProperty.ι _ ⋙ Comma.fst _ _

/-- Forget a flat triple to its module on V₁, including its component on morphisms.
Source: Stacks, Tag 08KV (blueprint: lem-sfb-space-relative-flat-module-pushout). -/
def rightForget {S : Scheme.{u}} (D : Diagram S) : FlatTriple D ⥤ D.V₁.Modules :=
  ObjectProperty.ι _ ⋙ Comma.snd _ _

/-- The specified overlap comparison for the two restrictions of a module on V.
It is tensor associativity through their common composite V₀ to V, with no choice of iso.
Source: Stacks, Tag 08KV, displayed restriction functor; Tags 03D7 and 03G8
(blueprint: lem-sfb-space-relative-flat-module-pushout). -/
def restrictionComparison {S : Scheme.{u}} (D : Diagram S) (M : D.V.Modules) :
    (moduleTensorPullback D.a₂).obj ((moduleTensorPullback D.r₂).obj M) ≅
      (moduleTensorPullback D.a₁).obj ((moduleTensorPullback D.r₁).obj M) :=
  (moduleTensorComposition D.a₂ D.r₂).app M ≪≫
    eqToIso (congrArg (fun f ↦ (moduleTensorPullback f).obj M)
      (D.a₂_r.trans D.a₁_r.symm)) ≪≫
    ((moduleTensorComposition D.a₁ D.r₁).app M).symm

/-- Restriction gives the relative flat-module patching equivalence. The natural
identifications identify both components on objects and on every module homomorphism;
the equation identifies the overlap map with the canonical tensor-composition comparison.
Under local finite presentation of h, finite presentation is detected by the two pieces.
Source: Stacks, Tag 08KV, equivalence and part (b), for scheme bases and finite-order ideals
(blueprint: lem-sfb-space-relative-flat-module-pushout).

Proof: (1) The infinitesimal-pushout affine-chart lemma gives rings R = B times_A A-prime
on an affine cover of P, with A-prime to A surjective, and all three base maps affine.
The affine-spectra fibre-product lemma computes their inverse images on affine charts of V.
(2) The affine-chart calculus, Zariski/etale comparison, affine-pullback section/stalk
flatness lemma and chart independence identify the relative flatness tests with flatness
of section modules over R, B and A-prime. No flatness of the chart algebra over R is used.
(3) Quasi-coherence is preserved by tensor pullback. Pointwise flatness base change and
chart independence preserve relative flatness. The chart-adjunction tensor realization
identifies the overlap with the specified composition comparison, naturally on all maps.
(4) For a triple, put M₀ = a₁-star M₁. Form the fibre product of the direct images of
M₂ and M₁ over that of M₀, using the adjoints of the comparison maps. Affine module
base change and affine-chart calculus show this kernel is quasi-coherent, and compatible
pairs of module maps induce maps of the kernels.
(5) On an affine chart with algebra D over R, the kernel is N times_M M-prime.
Tensor associativity and tensor-over-quotient identify M with both overlap restrictions.
Flat-module fibre-product patching makes the kernel flat over R; patched-module base
change identifies its restrictions with N and M-prime, including their D-linear actions.
Chart independence gives relative flatness on every chart and the counit isomorphism.
(6) The adjunction-unit map L to its recovered fibre product is an isomorphism by the
flat-module reconstruction lemma. Its inverse and the recovery maps commute with every
module map. Thus restriction is fully faithful and essentially surjective on all arrows.
(7) If h is locally finitely presented, choose anew affine charts with D finitely
presented over R. If the restrictions are finitely presented, the relative-fp-module
fp-algebra pushout lemma with flat intermediate algebra E = R makes the kernel finitely
presented over D. The affine-chart criterion and recovery give finite presentation on V.
(8) Conversely tensor pullback of a local finite presentation preserves its cokernel,
finite free modules and its covering charts, proving finite presentation on both pieces.
-/
theorem restriction_equivalence {S : Scheme.{u}} (D : Diagram S)
    [IsClosedImmersion D.i.left] [IsAffineHom D.a.left]
    (hnil : ∃ n : ℕ, 1 ≤ n ∧ D.i.left.ker ^ n = ⊥)
    (hpush : IsPushout D.a.left D.i.left D.j₂.left D.j₁.left) :
    ∃ E : FlatQCoh D.h ≌ FlatTriple D,
      ∃ (e₂ : E.functor ⋙ leftForget D ≅
          ObjectProperty.ι _ ⋙ moduleTensorPullback D.r₂)
        (e₁ : E.functor ⋙ rightForget D ≅
          ObjectProperty.ι _ ⋙ moduleTensorPullback D.r₁),
        (∀ M : FlatQCoh D.h,
          (moduleTensorPullback D.a₂).map (e₂.hom.app M) ≫
              (restrictionComparison D M.obj).hom =
            (E.functor.obj M).obj.hom ≫
              (moduleTensorPullback D.a₁).map (e₁.hom.app M)) ∧
        (MapIsLocallyOfFinitePresentation D.h → ∀ M : FlatQCoh D.h,
          M.obj.IsFinitePresentation ↔
            ((moduleTensorPullback D.r₂).obj M.obj).IsFinitePresentation ∧
              ((moduleTensorPullback D.r₁).obj M.obj).IsFinitePresentation) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeFlatModulePatching
