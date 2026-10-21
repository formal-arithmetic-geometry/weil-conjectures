/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import Sheaf.Paper.RegularExtensionComparison
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Inverse image of finite scalar matrices

Source: blueprint main-20261015, proper base change unbounded pullback proof,
paragraph “Constructible complexes”, local coefficient models on strata
(blueprint: lem-sfb-scalar-matrix-inverse-image).

The comparisons below use the canonical coefficient morphism and the regular-module
scalar-extension comparison, followed by the finite biproduct comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {V U : Scheme.{u}} (h : V ⟶ U)

/-- The regular-module comparison induced by the canonical coefficient map α_h.
First transport the regular module along the monoidal inverse image, and then use
extension of scalars along α_h. The forward map sends b ⊗ x to b α_h(x).
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”;
the explicit regular-module construction is step 2 of the node proof
(blueprint: lem-sfb-scalar-matrix-inverse-image). -/
noncomputable def scalarMatrixRegularPullbackIso :
    (CondensedRing.upperStar Λ h).obj (Mod.regular (condensedRingObj Λ U)) ≅
      Mod.regular (condensedRingObj Λ V) :=
  (Mod.extendScalars (condensedPullbackHom Λ h)).mapIso
      ((upperStar Ab.{u + 1} h).mapModUnitIso (R := condensedRingObj Λ U)).symm ≪≫
    Mod.regularExtensionIso (condensedPullbackHom Λ h)

/-- The canonical finite-coproduct extension of the regular-module comparison.
This definition also includes rank zero, using the empty biproduct comparison.
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”;
the finite-coproduct construction is step 3 of the node proof
(blueprint: lem-sfb-scalar-matrix-inverse-image). -/
noncomputable def scalarMatrixFreePullbackIso (r : ℕ) :
    (CondensedRing.upperStar Λ h).obj (Mod.finiteFree (condensedRingObj Λ U) r) ≅
      Mod.finiteFree (condensedRingObj Λ V) r :=
  (CondensedRing.upperStar Λ h).mapBiproduct
      (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) ≪≫
    biproduct.mapIso (fun _ ↦ scalarMatrixRegularPullbackIso Λ h)

/-- Pullback preserves matrices of the same condensed scalars and their cokernels.
The entries are maps ℤ → Λ(*), equivalently elements of the scalar ring Λ(*).
As in `scalarMatrix`, the first index is the source column and the second the target row.
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”,
local coefficient models on strata (blueprint: lem-sfb-scalar-matrix-inverse-image).

Proof in words (the six steps of the node proof):
1. Naturality of `upperStarFromPointComp` at multiplication by a scalar, together with
   the transported unit and multiplication of the coefficient ring, identifies the
   inverse images of the canonical scalar endomorphisms. This uses the scalar maps of
   `det-def-sfb-constructible-local-model`, rather than arbitrary coefficient sections.
2. Transport identifies the inverse image of the regular module with the regular module
   over the inverse-image ring. The mixed-bimodule right unitor identifies its extension
   along α_h with Λ_V, by b ⊗ x ↦ b α_h(x), with inverse b ↦ b ⊗ 1.
3. The module adjunction makes pullback preserve finite coproducts and coequalizers.
   Its zero-object comparison gives preservation of zero maps. Extending the regular
   comparison to biproducts gives the displayed finite-free comparisons, compatible
   with injections and projections, including the empty biproduct.
4. Precompose the two regular-module scalar endomorphism composites with the balancing
   coequalizer projection. Step 1 and associativity and commutativity of multiplication
   identify them; uniqueness of coequalizer descent proves equality.
5. Precompose with each transported input injection and postcompose with each output
   projection. The matrix entries reduce the square to step 4. The coproduct and product
   universal properties give the matrix equation, also when either rank is zero.
6. Pullback preserves the cokernel, a coequalizer of the matrix and zero. The matrix
   square induces maps in both directions between the two cokernels. Their defining
   projection equations make both composites identities by cokernel uniqueness. The
   forward projection equation is exactly the compatibility stated below. -/
theorem scalarMatrix_inverseImage {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
        (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A ∧
    ∃ e : (CondensedRing.upperStar Λ h).obj (cokernel (scalarMatrix Λ U A)) ≅
        cokernel (scalarMatrix Λ V A),
      (CondensedRing.upperStar Λ h).map (cokernel.π (scalarMatrix Λ U A)) ≫ e.hom =
        (scalarMatrixFreePullbackIso Λ h n).hom ≫ cokernel.π (scalarMatrix Λ V A) := by
  sorry

end AlgebraicGeometry.ProEtale
