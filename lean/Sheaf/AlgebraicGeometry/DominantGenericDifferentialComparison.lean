/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-!
# Generic stalk comparison for the differential of a dominant morphism

Source: Stacks Project, Morphisms, Tag 01UV, and Sheaves, Tag 0098
(blueprint: lem-sfb-dominant-generic-differential-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Hom

/-- The differential of a dominant morphism at the generic point, in the prescribed
function-field differential coordinates. Writing the source structure morphism as
`f ≫ g` encodes exactly that `f` is a morphism over the base field. The two alpha
maps are normalized on germs on every neighbourhood of the generic point; these
are exactly the nonempty opens of an integral scheme. The beta formula uses the
actual section of the normalized tensor-pullback adjunction unit.
Source: Stacks Project, Morphisms, Tag 01UV; Sheaves, Tag 0098
(blueprint: lem-sfb-dominant-generic-differential-comparison).

Proof:
1. Continuity carries the generic point to a generic point of the closure of the
   image. Density makes this all of Y; scheme sobriety gives the stated equality
   (def-pc-integral-scheme, lem-sc-scheme-sober, def-sc-generic-point). The induced
   function-field map is the actual structure-sheaf stalk map and respects k
   (def-weil-locally-ringed-space-morphism, def-weil-scheme-over-base).
2. Apply lem-weil-pbc-module-stalk-pullback to Omega_Y/k at the generic point.
   Compose its tensor coordinates with alphaY (and tensor symmetry if needed).
   The inverse uses alphaY.symm. Pure tensors show these maps are inverse and
   the normalized unit formula gives the displayed beta formula on all sections
   (def-weil-pbc-module-tensor-product).
3. The derivation b maps to d(phi(b)) induces a K-linear map on Omega_K/k by
   def-weil-pbc-kahler-differentials. Tensor universality gives the L-linear map
   a tensor db maps to a times d(phi(b)). The db generate Omega_K/k, so the
   1 tensor db generate its extension of scalars.
4. Represent b by a regular function near the target generic point. The alphaY
   and beta formulas identify 1 tensor db with its pulled-back differential germ.
   The section characterization of def-a1-relative-differentials-pullback-map
   sends this to the differential of the pulled-back function. The alphaX formula
   identifies its germ with d(phi(b)). Stalk maps commute with germs by
   def-weil-pbc-module-stalk. Linearity and step 3 give the formula for all a,b.
-/
theorem dominant_generic_differential_comparison
    (k : Type u) [Field k] (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsDominant f]
    (αX : (RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).obj
      (f ≫ g).relativeDifferentials ≃ₗ[X.functionField]
        CommRingCat.KaehlerDifferential ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop ≫
          X.presheaf.germ ⊤ (genericPoint X) trivial))
    (αY : (RingedSpace.moduleStalkFunctor Y.toRingedSpace (genericPoint Y)).obj
      g.relativeDifferentials ≃ₗ[Y.functionField]
        CommRingCat.KaehlerDifferential ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
          Y.presheaf.germ ⊤ (genericPoint Y) trivial))
    (hαX : ∀ (U : X.Opens) (hx : genericPoint X ∈ U) (a : Γ(X, U)),
      αX (TopCat.Presheaf.germ (f ≫ g).relativeDifferentials.val.presheaf U
        (genericPoint X) hx ((f ≫ g).relativeDifferentialsDerivation.d (X := op U) a)) =
      CommRingCat.KaehlerDifferential.d (X.presheaf.germ U (genericPoint X) hx a))
    (hαY : ∀ (V : Y.Opens) (hy : genericPoint Y ∈ V) (a : Γ(Y, V)),
      αY (TopCat.Presheaf.germ g.relativeDifferentials.val.presheaf V
        (genericPoint Y) hy (g.relativeDifferentialsDerivation.d (X := op V) a)) =
      CommRingCat.KaehlerDifferential.d (Y.presheaf.germ V (genericPoint Y) hy a)) :
    ∃ hη : f (genericPoint X) = genericPoint Y,
      ∃ β : (RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).obj
          ((Modules.tensorPullback f).obj g.relativeDifferentials) ≃ₗ[X.functionField]
          (ModuleCat.extendScalars (f.functionFieldMap hη).hom).obj
            (CommRingCat.KaehlerDifferential ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
              Y.presheaf.germ ⊤ (genericPoint Y) trivial)),
        (∀ (V : Y.Opens) (hy : genericPoint Y ∈ V)
            (s : g.relativeDifferentials.val.obj (op V)),
          β (TopCat.Presheaf.germ
            ((Modules.tensorPullback f).obj g.relativeDifferentials).val.presheaf
            (f ⁻¹ᵁ V) (genericPoint X) ((congrArg (fun y : Y ↦ y ∈ V) hη).mpr hy)
            (Modules.tensorPullbackSection f g.relativeDifferentials V s)) =
          (1 : X.functionField) ⊗ₜ[Y.functionField, (f.functionFieldMap hη).hom]
            αY (TopCat.Presheaf.germ g.relativeDifferentials.val.presheaf
              V (genericPoint Y) hy s)) ∧
        ∀ (a : X.functionField) (b : Y.functionField),
          αX (((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
            (g.relativeDifferentialsPullbackMap f))
            (β.symm (a ⊗ₜ[Y.functionField, (f.functionFieldMap hη).hom]
              CommRingCat.KaehlerDifferential.d b))) =
            a • CommRingCat.KaehlerDifferential.d (f.functionFieldMap hη b) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
