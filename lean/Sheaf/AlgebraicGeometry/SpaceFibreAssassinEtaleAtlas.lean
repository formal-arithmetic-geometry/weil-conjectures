/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Associated points on the fibres of an étale scheme atlas

Source: Stacks Project, Divisors on Spaces, Tags 0CUY, 0CUZ and 0CVV
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas).

The fibre is the existing sheaf fibre product with Spec κ(y). Its scheme atlas is
specified by its pullback square; thus the theorem applies to every representative
of that fibre product. Its module is the ordinary fibre pullback of the Zariski
restriction of M to the original atlas. Downstairs the existing chartwise relative
assassin over Spec κ(y) is the absolute fibre assassin.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue-field spectrum of a scheme point, over the original base.
Source: Stacks, Divisors on Spaces, Tag 0CUZ, the scheme-base case
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas). -/
def assassinPointBase {S : Scheme.{u}} (Y : Over S) (y : Y.left) : Over S :=
  Over.mk (Y.left.fromSpecResidueField y ≫ Y.hom)

/-- The canonical residue-field map, viewed as a morphism of algebraic spaces.
Source: Stacks, Divisors on Spaces, Tag 0CUZ(6)
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas). -/
def assassinPointBaseMap {S : Scheme.{u}} (Y : Over S) (y : Y.left) :
    schemeSpace (assassinPointBase Y y) ⟶ schemeSpace Y :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk (Y.left.fromSpecResidueField y))⟩

/-- The actual sheaf fibre product defining the fibre of a space over a scheme point.
Source: Stacks, Divisors on Spaces, Tags 0CUZ and 0CVV
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas). -/
def assassinSchemeFibre {S : Scheme.{u}} {X : AlgebraicSpace S} (Y : Over S)
    (f : X ⟶ schemeSpace Y) (y : Y.left) : AlgebraicSpace S :=
  enlargedFibreProduct f (assassinPointBaseMap Y y)

/-- Projection of the sheaf fibre product to Spec κ(y).
Source: Stacks, Divisors on Spaces, Tag 0CUZ
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas). -/
def assassinSchemeFibreToPoint {S : Scheme.{u}} {X : AlgebraicSpace S} (Y : Over S)
    (f : X ⟶ schemeSpace Y) (y : Y.left) :
    assassinSchemeFibre Y f y ⟶ schemeSpace (assassinPointBase Y y) :=
  ObjectProperty.homMk (Limits.pullback.snd f.hom (assassinPointBaseMap Y y).hom)

/-- Fibre associated points are detected at every lift in a surjective étale scheme atlas,
and the image of the associated-point set is precisely the fibre assassin.
The atlas `T` encodes the representable étale map p. The chart `Ty` and `i`, with their
pullback square, specify its base change p_y to the actual sheaf fibre `X_y`.
The ordinary tensor pullback along `i.left` is N_y, where N is the Zariski restriction
of p^*M. The chartwise relative assassin over the residue-field spectrum is Ass(X_y,M_y).
Source: Stacks, Divisors on Spaces, Tags 0CUY, 0CUZ(3),(4),(6) and 0CVV
(blueprint: lem-sfb-space-fibre-assassin-etale-atlas).
Proof:
1. By finite type, atlas fibres are locally of finite type over κ(y), hence locally
   Noetherian [lem-weil-pbc-lft-base-change, pqf-lem-locnoeth-lft]. Common scheme
   refinements and étale descent make every fibre chart locally Noetherian
   [lem-trf-space-representable-etale-scheme-tests, lem-trf-etale-local-noetherian-descent].
2. Tensor pullbacks remain quasi-coherent [lem-sfb-space-module-pullback-quasicoherent].
   The étale/Zariski equivalence and normalized tensor composition identify N_y with
   p_y^*M_y, and identify both pullbacks on every common refinement
   [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
   lem-trf-space-chart-adjunction-tensor-realization].
3. An associated point of N_y witnesses membership in the chartwise assassin downstairs
   [def-sfb-space-universal-relative-purity]. Relative association over a field is
   absolute association.
4. Conversely choose an associated point u on a chart over p_y(t). Lift the compatible
   pair (u,t) to the scheme common refinement [lem-a1-space-point-open-calculus].
   Both projections are étale. Apply scheme étale invariance first from u to this lift,
   then from this lift to t [lem-sfb-scheme-etale-assassin-invariance], using the module
   comparisons in step 2. This proves the equivalence for every t.
5. Surjectivity of p_y on point classes supplies a lift of every associated point
   downstairs [lem-trf-space-representable-etale-scheme-tests,
   lem-a1-space-point-open-calculus]. Step 4 makes that lift associated; step 3 gives
   the reverse image inclusion. Empty fibres and zero modules give empty sets. -/
theorem space_fibre_assassin_etale_atlas
    {X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (_hf : MapIsFiniteType f) (_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.QCoh) (_hM : SheafOfModules.IsFiniteType M.obj)
    (T : X.EtaleSite) (_hp : IsSurjective T.obj.hom) (y : Y.left)
    (Ty : (assassinSchemeFibre Y f y).EtaleSite) (i : Ty.obj.left ⟶ T.obj.left)
    (_hcart : IsPullback Ty.obj.hom (yoneda.map i)
      (Limits.pullback.fst f.hom (assassinPointBaseMap Y y).hom).hom T.obj.hom) :
    (∀ t : Ty.obj.left.left,
      t ∈ Scheme.Modules.associatedPoints
        ((Scheme.Modules.tensorPullback i.left).obj ((X.schemeRestriction T).obj M.obj)) ↔
      schemePointMap Ty.obj.hom t ∈ relativeAssassin (assassinPointBase Y y)
        (assassinSchemeFibreToPoint Y f y)
        ((moduleTensorPullback
          (enlargedFibreProductFst f (assassinPointBaseMap Y y))).obj M.obj)) ∧
    (schemePointMap Ty.obj.hom) '' Scheme.Modules.associatedPoints
        ((Scheme.Modules.tensorPullback i.left).obj ((X.schemeRestriction T).obj M.obj)) =
      relativeAssassin (assassinPointBase Y y) (assassinSchemeFibreToPoint Y f y)
        ((moduleTensorPullback
          (enlargedFibreProductFst f (assassinPointBaseMap Y y))).obj M.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
