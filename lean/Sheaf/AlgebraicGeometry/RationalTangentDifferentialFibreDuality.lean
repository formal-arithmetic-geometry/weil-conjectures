/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification

/-!
# Rational tangent vectors and the dual differential fibre

Source: Stacks Project, Varieties, Tags 0B2D and 0B2E; Sheaves, Tag 0098
(blueprint: lem-sfb-rational-tangent-differential-fibre-duality).

The coefficient formula on differential germs specifies the canonical equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The structural map from the base field to the residue field at a point.
Source: Stacks Project, Tag 0B2D
(blueprint: lem-sfb-rational-tangent-differential-fibre-duality). -/
def rationalTangentStructuralResidueMap
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) (z : X) :
    K →+* X.residueField z :=
  (StructureSheaf.toStalk K (f z) ≫ f.stalkMap z ≫ X.residue z).hom

/-- Global sections of the ordinary tensor pullback of the differential sheaf.
Source: Stacks Project, Tags 0B2D and 0098
(blueprint: lem-sfb-rational-tangent-differential-fibre-duality). -/
def rationalTangentDifferentialFibre
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K))
    (x : Spec (.of K) ⟶ X) : ModuleCat K :=
  (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
    ((Scheme.Modules.tensorPullback x).obj f.relativeDifferentials)

/-- At a rational point the dual-number tangent space is canonically the linear dual of
`Γ(Spec K, x* Ω¹)`. Scalars on the existing tangent space are restricted along the structural
residue map. The equality of germs identifies a global section `m` with the pulled-back
local differential `da`; the coefficient identity therefore specifies the canonical pairing.
The last clause exhibits the constant vector, transported from `K` to the residue field,
and says that its image is zero. No finiteness or smoothness assumption is imposed.

Source: Stacks Project, Varieties, Tags 0B2D and 0B2E; Sheaves, Tag 0098
(blueprint: lem-sfb-rational-tangent-differential-fibre-duality).

Proof:
1. Write A for the local ring at x and c for its residue map to K. Rationality identifies
   the residue field with K. By lem-sfb-relative-differentials-stalk and
   lem-weil-pbc-module-stalk-pullback, the displayed global sections identify with
   K tensor_A Ω[A/K]. The unit germ sends da to 1 tensor da. Spec K is a one-point space,
   so its global sections are its stalk.
2. Apply lem-pur-conormal-sequence-smooth-immersion to Spec K inside Spec A over K;
   only the source Spec K is smooth. The local-spectrum germ identification from
   lem-weil-pbc-morphism-from-spec-local-ring identifies its conormal space with m/m².
   Since Ω[K/K] is zero, this gives m/m² isomorphic to K tensor_A Ω[A/K], taking the
   class of a to 1 tensor da. This does not require X to be smooth or of finite type.
3. Compose the dual of this comparison with the epsilon-coefficient equivalence of
   lem-sc-rational-point-tangent-derivation-identification. For arbitrary a in A,
   subtract its structural residue: a₀ = a - s(c(a)) lies in m, da₀ = da, and D(a₀) = D(a).
   The pairing formula thus holds on every differential germ, which generates the fibre.
4. The constant tangent vector has stalk homomorphism a ↦ c(a) + 0ε. Its coefficient
   derivation is zero, hence the corresponding functional is zero, including when the
   differential fibre vanishes. -/
theorem exists_rationalTangent_differentialFibre_linearEquiv
    (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K))
    (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    letI : Module K (schemeTangentSpace K X f (x (IsLocalRing.closedPoint K))) :=
      Module.compHom (schemeTangentSpace K X f (x (IsLocalRing.closedPoint K)))
        (rationalTangentStructuralResidueMap K X f (x (IsLocalRing.closedPoint K)))
    ∃ e : schemeTangentSpace K X f (x (IsLocalRing.closedPoint K)) ≃ₗ[K]
        (rationalTangentDifferentialFibre K X f x →ₗ[K] K),
      (∀ θ : schemeTangentSpace K X f (x (IsLocalRing.closedPoint K)),
        ∃ hθ : θ.val (IsLocalRing.closedPoint
            (DualNumber (X.residueField (x (IsLocalRing.closedPoint K))))) =
              x (IsLocalRing.closedPoint K),
          ∀ (U : X.Opens) (hU : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U))
            (m : rationalTangentDifferentialFibre K X f x),
            TopCat.Presheaf.germ
                ((Scheme.Modules.tensorPullback x).obj f.relativeDifferentials).presheaf
                ⊤ (IsLocalRing.closedPoint K) (Set.mem_univ _) m =
              TopCat.Presheaf.germ
                ((Scheme.Modules.tensorPullback x).obj f.relativeDifferentials).presheaf
                (x ⁻¹ᵁ U) (IsLocalRing.closedPoint K) hU
                (Scheme.Modules.tensorPullbackSection x f.relativeDifferentials U
                  (f.relativeDifferentialsDerivation.d (X := op U) a)) →
            rationalTangentStructuralResidueMap K X f (x (IsLocalRing.closedPoint K))
                (e θ m) =
              TrivSqZeroExt.snd
                ((eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hθ.symm) ≫
                  Scheme.stalkClosedPointTo θ.val).hom
                  (X.presheaf.germ U (x (IsLocalRing.closedPoint K)) hU a))) ∧
      (∃ θ₀ : schemeTangentSpace K X f (x (IsLocalRing.closedPoint K)),
        θ₀.val =
          Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
            (rationalTangentStructuralResidueMap K X f (x (IsLocalRing.closedPoint K))))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K)) ≫ x ∧ e θ₀ = 0) := by
  sorry

end AlgebraicGeometry
