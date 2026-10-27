/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffinePushforwardIdealProduct
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Finite direct image, ideal multiples and twisted cohomology

Source: Stacks Project, Cohomology of Schemes, Tags 0B5V, 01YP and 089W;
Cohomology of Sheaves, Tag 01E8
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison).

The ideal-image definitions are registered by `def-trf-ideal-module-product-image`;
the structure map by `def-sfb-tensor-pullback-structure-sheaf-map`; and the power
comparison by `def-sc-tensor-pullback-power-comparison`.
The auxiliary definitions only assemble existing canonical maps. Tensor powers use
`Modules.tensorPow`, including its unit at zero; the associators and unitors identify
this convention with the positive left-associated powers in the source.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The extended ideal multiple, formed as the image of multiplication, including
non-flat morphisms. Source: Stacks 01YP
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison). -/
def finiteTwistIdealMultiple {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J : X.IdealSheafData) (F : Y.Modules) : Y.Modules :=
  idealModuleProduct ((tensorPullback f).map J.toModulesι ≫
    tensorPullbackObjUnitToUnit f) F

/-- Its inclusion in the original coefficient module. Source: Stacks 01YP
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison). -/
def finiteTwistIdealMultipleι {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J : X.IdealSheafData) (F : Y.Modules) : finiteTwistIdealMultiple f J F ⟶ F :=
  idealModuleProductι ((tensorPullback f).map J.toModulesι ≫
    tensorPullbackObjUnitToUnit f) F

/-- The ordinary projection map transported to the explicit tensor pullback through
its normalized adjunction. Source: Stacks 01E8
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison). -/
def finiteTwistProjectionHom {X Y : Scheme.{u}} (f : Y ⟶ X)
    (H : Y.Modules) (N : X.Modules) :
    (pushforward f).obj H ⊗ N ⟶ (pushforward f).obj (H ⊗ (tensorPullback f).obj N) :=
  projectionHom f H N ≫ (pushforward f).map
    (H ◁ (((tensorPullbackSectionAdjunction f).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).inv.app N))

/-- The coefficient comparison: equality of ideal multiples, projection, and the
canonical pullback-of-power comparison. Source: Stacks 0B5V, displayed calculation
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison). -/
def finiteTwistCoefficientMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J : X.IdealSheafData) (F : Y.Modules) (L : X.Modules) (n : ℕ)
    (e : idealModuleProduct J.toModulesι ((pushforward f).obj F) ≅
      (pushforward f).obj (finiteTwistIdealMultiple f J F)) :
    idealModuleProduct J.toModulesι ((pushforward f).obj F) ⊗ L.tensorPow n ⟶
      (pushforward f).obj
        (finiteTwistIdealMultiple f J F ⊗ ((tensorPullback f).obj L).tensorPow n) :=
  e.hom ▷ L.tensorPow n ≫
    finiteTwistProjectionHom f (finiteTwistIdealMultiple f J F) (L.tensorPow n) ≫
    (pushforward f).map
      (finiteTwistIdealMultiple f J F ◁ (boundaryPullbackPowIso f L n).hom)

/-- The displayed cohomology comparison, with the specified identity-map edge.
Source: Stacks 0B5V and 089W
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison). -/
def finiteTwistCohomologyMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (J : X.IdealSheafData) (F : Y.Modules) (L : X.Modules) (p n : ℕ)
    (e : idealModuleProduct J.toModulesι ((pushforward f).obj F) ≅
      (pushforward f).obj (finiteTwistIdealMultiple f J F)) :=
  (forget₂ _ AddCommGrpCat.{u}).map
    ((RingedSpace.moduleCohomology X.toRingedSpace p).map
      (finiteTwistCoefficientMap f J F L n e)) ≫
    moduleCohomologyEdgeMap f
      (finiteTwistIdealMultiple f J F ⊗ ((tensorPullback f).obj L).tensorPow n) p

/-- Coherence, the equality of submodules, exact invertible twists and the two
specified cohomology isomorphisms. Source: Stacks 0B5V, 01YP, 089W and 01E8
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison).

Proof:
1. Finiteness implies affineness. Finite pushforward preserves coherence
   [lem-weil-pbc-finite-pushforward-coherent]. Coherent modules on locally Noetherian
   schemes are quasi-coherent [pqf-lem-coherent-ft-locnoeth]. Apply the affine
   ideal-product theorem [lem-weil-pbc-affine-pushforward-ideal-product].
2. Its upstairs image is quasi-coherent and is a submodule of the coherent F,
   hence coherent [lem-weil-pbc-coherent-kernel-cokernel-locnoeth]. Its finite
   pushforward is coherent too; the equality gives coherence of the downstairs product.
   The equality of subobjects gives the unique isomorphism respecting inclusions.
3. Pullback and tensor products preserve invertibility
   [lem-weil-pbc-invertible-pullback-tensor]. Induct on the tensor power; at zero
   use the structure-sheaf pullback isomorphism
   [lem-weil-pbc-module-pullback-structure-sheaf]. The existing recursive comparison
   boundaryPullbackPowIso is the canonical comparison, including its unit at zero.
4. On a trivializing open, tensoring is the identity up to its unitor. Exactness
   is local, so both tensor functors preserve finite limits and finite colimits.
5. The projection map is h tensor s maps to h tensor f-star s. A local generator
   trivializes both factors; the map becomes the identity. The local inverses
   agree after multiplication of the generator by a unit, so they glue.
6. The upstairs ideal multiple is quasi-coherent; the invertible factor is too.
   Their tensor is quasi-coherent
   [lem-weil-pbc-quasi-coherent-tensor-product-affine-sections].
7. Compose the ideal-product identification, projection, and power comparison.
   Apply H-p for the first isomorphism. The affine cohomology edge theorem
   [lem-weil-pbc-affine-morphism-cohomology-edge] makes the specified edge invertible.
   Their composite is therefore invertible for every p and n, including zero. -/
theorem finite_ideal_twist_cohomology_comparison {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (F : Y.Modules) (hF : RingedSpace.IsCoherent Y.toRingedSpace F)
    (J : X.IdealSheafData) (L : X.Modules) [L.IsInvertible] :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward f).obj F) ∧
    RingedSpace.IsCoherent Y.toRingedSpace (finiteTwistIdealMultiple f J F) ∧
    RingedSpace.IsCoherent X.toRingedSpace
      (idealModuleProduct J.toModulesι ((pushforward f).obj F)) ∧
    imageSubobject (idealModuleProductι J.toModulesι ((pushforward f).obj F)) =
      imageSubobject ((pushforward f).map (finiteTwistIdealMultipleι f J F)) ∧
    ∃ e : idealModuleProduct J.toModulesι ((pushforward f).obj F) ≅
        (pushforward f).obj (finiteTwistIdealMultiple f J F),
      e.hom ≫ (pushforward f).map (finiteTwistIdealMultipleι f J F) =
        idealModuleProductι J.toModulesι ((pushforward f).obj F) ∧
      ∀ n : ℕ,
        (L.tensorPow n).IsInvertible ∧
        ((tensorPullback f).obj (L.tensorPow n)).IsInvertible ∧
        ((tensorPullback f).obj L).IsInvertible ∧
        PreservesFiniteLimits (tensorRight (L.tensorPow n)) ∧
        PreservesFiniteColimits (tensorRight (L.tensorPow n)) ∧
        PreservesFiniteLimits (tensorRight ((tensorPullback f).obj (L.tensorPow n))) ∧
        PreservesFiniteColimits (tensorRight ((tensorPullback f).obj (L.tensorPow n))) ∧
        IsIso (finiteTwistProjectionHom f (finiteTwistIdealMultiple f J F) (L.tensorPow n)) ∧
        (finiteTwistIdealMultiple f J F ⊗ ((tensorPullback f).obj L).tensorPow n).IsQuasicoherent ∧
        ∀ p : ℕ,
          IsIso ((RingedSpace.moduleCohomology X.toRingedSpace p).map
            (finiteTwistCoefficientMap f J F L n e)) ∧
          IsIso (moduleCohomologyEdgeMap f
            (finiteTwistIdealMultiple f J F ⊗ ((tensorPullback f).obj L).tensorPow n) p) ∧
          IsIso (finiteTwistCohomologyMap f J F L p n e) := by
  sorry

/-- The ordinary projection map on sections, hence the identity in the local
coordinates h maps to h tensor e and h maps to h tensor f-star e on a trivializing open.
Source: Stacks 01E8, degree-zero local projection argument
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison).
Proof: the upstream projectionHom sends h tensor s to h tensor the adjunction unit of s.
The left-adjoint uniqueness comparison carries that unit to the section-normalized
unit. The latter is tensorPullbackSection, namely 1 tensor s. This proves the formula
on every open; specializing s to a generator proves the claimed local identity.
The maps are canonical independently of the generator, so the local identities glue. -/
theorem finiteTwistProjectionHom_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (H : Y.Modules) (N : X.Modules) (U : X.Opens)
    (h : Γ(H, f ⁻¹ᵁ U)) (s : Γ(N, U)) :
    (finiteTwistProjectionHom f H N).app U
      (tmulSection (M := (pushforward f).obj H) h s) =
      tmulSection h (tensorPullbackSection f N U s) := by
  sorry

/-- Naturality in the original coherent module and in the invertible power factor.
The two image maps are the restrictions of v and f-star v. The transported map of
powers is written with the same canonical pullback comparison used in the main map.
Source: Stacks 0B5V, 01E8 and 01F8
(blueprint: lem-trf-finite-ideal-twist-cohomology-comparison).
Proof: multiplication commutes with every coefficient map, so v and f-star v restrict
uniquely to the two images. Their inclusion equations and the inclusion normalization
of e and e' imply naturality of the ideal-product identification. On pure tensor
sections the projection square commutes, and these sections generate locally. Compose
with the pullback power comparisons to obtain the displayed coefficient square.
Applying H-p and the coefficient-composition clause of
[lem-weil-pbc-module-cohomology-fmap-functorial] proves the cohomology square. -/
theorem finiteTwistCohomologyMap_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (J : X.IdealSheafData) (F F' : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F)
    (hF' : RingedSpace.IsCoherent Y.toRingedSpace F') (v : F ⟶ F')
    (L L' : X.Modules) [L.IsInvertible] [L'.IsInvertible] (n : ℕ)
    (q : L.tensorPow n ⟶ L'.tensorPow n)
    (e : idealModuleProduct J.toModulesι ((pushforward f).obj F) ≅
      (pushforward f).obj (finiteTwistIdealMultiple f J F))
    (e' : idealModuleProduct J.toModulesι ((pushforward f).obj F') ≅
      (pushforward f).obj (finiteTwistIdealMultiple f J F'))
    (he : e.hom ≫ (pushforward f).map (finiteTwistIdealMultipleι f J F) =
      idealModuleProductι J.toModulesι ((pushforward f).obj F))
    (he' : e'.hom ≫ (pushforward f).map (finiteTwistIdealMultipleι f J F') =
      idealModuleProductι J.toModulesι ((pushforward f).obj F')) :
    ∃ (h : finiteTwistIdealMultiple f J F ⟶ finiteTwistIdealMultiple f J F')
      (w : idealModuleProduct J.toModulesι ((pushforward f).obj F) ⟶
        idealModuleProduct J.toModulesι ((pushforward f).obj F')),
      h ≫ finiteTwistIdealMultipleι f J F' = finiteTwistIdealMultipleι f J F ≫ v ∧
      w ≫ idealModuleProductι J.toModulesι ((pushforward f).obj F') =
        idealModuleProductι J.toModulesι ((pushforward f).obj F) ≫ (pushforward f).map v ∧
      (w ⊗ₘ q) ≫ finiteTwistCoefficientMap f J F' L' n e' =
        finiteTwistCoefficientMap f J F L n e ≫ (pushforward f).map
          (h ⊗ₘ ((boundaryPullbackPowIso f L n).inv ≫
            (tensorPullback f).map q ≫ (boundaryPullbackPowIso f L' n).hom)) ∧
      ∀ p : ℕ,
        (forget₂ _ AddCommGrpCat.{u}).map
            ((RingedSpace.moduleCohomology X.toRingedSpace p).map (w ⊗ₘ q)) ≫
          finiteTwistCohomologyMap f J F' L' p n e' =
        finiteTwistCohomologyMap f J F L p n e ≫
          (forget₂ _ AddCommGrpCat.{u}).map
            ((RingedSpace.moduleCohomology Y.toRingedSpace p).map
              (h ⊗ₘ ((boundaryPullbackPowIso f L n).inv ≫
                (tensorPullback f).map q ≫ (boundaryPullbackPowIso f L' n).hom))) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
