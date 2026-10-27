/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra

/-! # A representative presentation of the relative Picard sheaf

Source: Stacks, quot.tex, Situation 0D25; sites.tex, sheafification;
sites-modules.tex, Tag 03EK (blueprint: def-sfb-space-picard-presentation).

Local representatives and local equality characterize the associated fppf sheaf.
The commutative regular-functions sheaf is the existing `commStructureSheaf`
(blueprint: def-sfb-space-quasi-coherent-algebra).
The class map is normalized by canonical tensor pullback, not an arbitrary map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The sectionwise ULift transport to a universe containing the entire small site.
Source: Stacks, Tag 03EK; size convention
(blueprint: def-sfb-space-picard-presentation). -/
def picardLiftModule (Y : AlgebraicSpace S) (L : Y.Modules) :=
  SheafOfModules.CochainUniverseTransport.module.{u + 1, u, u, u, u + 1}
    (commStructureSheaf Y) L

/-- The existing sheafified tensor product, after fully faithful coefficient transport.
Source: Stacks, Tag 03EK (blueprint: def-sfb-space-picard-presentation). -/
def picardLineTensor (Y : AlgebraicSpace S) (L M : Y.Modules) :=
  (SheafOfModules.siteSheafTensorRight
    (A := SheafOfModules.CochainUniverseTransport.ring.{u + 1, u, u, u, u + 1}
      (commStructureSheaf Y)) (picardLiftModule Y M)).obj (picardLiftModule Y L)

/-- Refine a scheme test by its given scheme map, composing the map to B.
Source: Stacks, Situation 0D25 (blueprint: def-sfb-space-picard-presentation). -/
def picardRefinedTest (T : ProperQuotTest B) {U : Over S} (a : U ⟶ T.left) :
    ProperQuotTest B :=
  CostructuredArrow.mk (yoneda.map a ≫ T.hom)

/-- The canonical arrow from a refined test to the original test.
Source: Stacks, Situation 0D25 (blueprint: def-sfb-space-picard-presentation). -/
def picardRefinementMap (T : ProperQuotTest B) {U : Over S} (a : U ⟶ T.left) :
    picardRefinedTest T a ⟶ T :=
  CostructuredArrow.homMk a

/-- The relative Picard sheaf represented by Q, expressed by local representatives.
The local equality condition is exactly equality in the sheafification of line
isomorphism classes. Naturality uses the fixed tensor pullback. The group law on Q
is fixed by tensor product and the unit; its inverse is consequently dualization.
Source: Stacks, Situation 0D25; sheafification local-section criterion
(blueprint: def-sfb-space-picard-presentation). -/
structure SpacePicardPresentation (f : X ⟶ groupSpaceBase S) (Q : AlgebraicSpace S)
    (G : CommutativeSpaceGroup Q) where
  /-- Class of each actual line module on the actual fibre product. -/
  lineClass (T : ProperQuotTest (groupSpaceBase S)) (L : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L) : Q.obj.obj.obj (op T.left)
  /-- Isomorphic line modules have the same class. -/
  iso_class (T : ProperQuotTest (groupSpaceBase S)) (L M : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L)
    (hM : (properQuotFibre f T).IsLineModule M) :
    Nonempty (L ≅ M) → lineClass T L hL = lineClass T M hM
  /-- Restriction is canonical tensor pullback, including all scheme test maps. -/
  naturality {T U : ProperQuotTest (groupSpaceBase S)} (a : U ⟶ T)
    (L : (properQuotFibre f T).Modules) (M : (properQuotFibre f U).Modules)
    (hL : (properQuotFibre f T).IsLineModule L)
    (hM : (properQuotFibre f U).IsLineModule M) :
    Nonempty ((moduleTensorPullback (properQuotFibreMap f a)).obj L ≅ M) →
      Q.obj.obj.map a.left.op (lineClass T L hL) = lineClass U M hM
  /-- Every section has line-module representatives on an fppf covering sieve. -/
  locally_represented (T : ProperQuotTest (groupSpaceBase S)) (s : Q.obj.obj.obj (op T.left)) :
    ∃ R : Sieve T.left, R ∈ Scheme.fppfTopology.over S T.left ∧
      ∀ (U : Over S) (a : U ⟶ T.left), R a →
        ∃ (L : (properQuotFibre f (picardRefinedTest T a)).Modules)
          (hL : (properQuotFibre f (picardRefinedTest T a)).IsLineModule L),
          Q.obj.obj.map a.op s = lineClass (picardRefinedTest T a) L hL
  /-- Equality of classes is exactly local isomorphism, with no chosen section. -/
  locally_equal (T : ProperQuotTest (groupSpaceBase S)) (L M : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L)
    (hM : (properQuotFibre f T).IsLineModule M) :
    lineClass T L hL = lineClass T M hM ↔
      ∃ R : Sieve T.left, R ∈ Scheme.fppfTopology.over S T.left ∧
        ∀ (U : Over S) (a : U ⟶ T.left), R a →
          Nonempty
            ((moduleTensorPullback (properQuotFibreMap f (picardRefinementMap T a))).obj L ≅
              (moduleTensorPullback (properQuotFibreMap f (picardRefinementMap T a))).obj M)
  /-- The tensor product induces multiplication, with its actual module object. -/
  tensor_class (T : ProperQuotTest (groupSpaceBase S)) (L M N : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L)
    (hM : (properQuotFibre f T).IsLineModule M)
    (hN : (properQuotFibre f T).IsLineModule N) :
    Nonempty (picardLineTensor (properQuotFibre f T) L M ≅
      picardLiftModule (properQuotFibre f T) N) →
      lineClass T N hN =
        @Mul.mul _ (G.group (op T.left)).toMul (lineClass T L hL) (lineClass T M hM)
  /-- The trivial module induces the identity. -/
  unit_class (T : ProperQuotTest (groupSpaceBase S)) (L : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L) :
    Nonempty (L ≅ SheafOfModules.unit (properQuotFibre f T).structureSheaf) →
      lineClass T L hL = @One.one _ (G.group (op T.left)).toOne
  /-- Tensor inverses, canonically the dual lines, induce group inversion. -/
  inverse_class (T : ProperQuotTest (groupSpaceBase S)) (L M : (properQuotFibre f T).Modules)
    (hL : (properQuotFibre f T).IsLineModule L)
    (hM : (properQuotFibre f T).IsLineModule M) :
    Nonempty (picardLineTensor (properQuotFibre f T) L M ≅
      picardLiftModule (properQuotFibre f T)
        (SheafOfModules.unit (properQuotFibre f T).structureSheaf)) →
      lineClass T M hM = @Inv.inv _ (G.group (op T.left)).toInv (lineClass T L hL)

end AlgebraicGeometry.AlgebraicSpace
