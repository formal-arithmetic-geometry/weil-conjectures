/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! # Scalar adjunction transport for arbitrary finite coefficient families -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

/-- Scalar adjuncts transport through the section-normalized realization, preserving
invertibility and coherent transitions for arbitrary families of objects.
Source: current blueprint lem-coef-finite-dualizing.proof.md, final sentence;
lem-coef-dualizing-site-mates, normalized scalar transport
(blueprint: lem-coef-dualizing-scalar-realization).

Proof: the comparison-site restriction square is induced by ordinary scalar
restriction on sections. The intrinsic restriction comparison is uniquely fixed on
those same sections. Their identity and composition squares therefore agree before
localization. Exact localization preserves these squares, including the canonical
mapDerivedCategory identity and composition constraints. Transpose the resulting
restriction square under the two scalar adjunctions. On the comparison-site part
this is the published pbcComparisonReductionMap; on the intrinsic part conjugation
through the intrinsic equivalences gives an isomorphism of scalar extensions.
Consequently the intrinsic transpose of t is conjugate to the realized v by this
isomorphism and the two endpoint isomorphisms e. Thus it is invertible when v is.
For the identity law, transpose the normalized scalar unit: its adjunct followed by
the restriction unit is identity, by the triangle identity. Conjugate by e and
cancel e.inv followed by e.hom. For composition, transpose the assumed scalar
cocycle using the two scalar adjunctions. Naturality of their units and the defining
leftAdjointCompIso equation give the semilinear restriction cocycle. Transport
through the coherent realization restriction square, move the endpoint maps by
naturality, and cancel the two middle e factors. This gives exactly the displayed
normalizedDVRResComp equation. No exceptional functor, counit of compact support,
constructibility, or arbitrary ambient pro-etale exceptional adjunction enters. -/
theorem finiteDualizing_scalar_realization
    (K : ∀ n : ℕ, Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X)
    (L : ∀ n : ℕ, normalizedDVRDerived l E X n)
    (e : ∀ n : ℕ, (finiteDualizingRealization l E X n).obj (K n) ≅ L n)
    (v : ∀ {m n : ℕ} (h : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj (K m) ⟶ K n)
    (hv : ∀ {m n : ℕ} (h : n ≤ m), IsIso (v h))
    (hunit : ∀ n : ℕ, v (le_refl n) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app (K n))
    (hcomp : ∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) X).map (v hrm) ≫ v hmn =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app (K r) ≫ v (hmn.trans hrm)) :
    let t := fun {m n : ℕ} (h : n ≤ m) ↦
      (e m).inv ≫ (finiteDualizingRealization l E X m).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l E h))).homEquiv _ _ (v h)) ≫
      (finiteDualizingRealizationRestriction l E X h).inv.app (K n) ≫
      (normalizedDVRRes l E X h).map (e n).hom
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
        (t h))) ∧
    (∀ n : ℕ, t (le_refl n) ≫ (normalizedDVRResUnit l E X n).hom.app (L n) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      t (hmn.trans hrm) ≫ (normalizedDVRResComp l E X hrm hmn).inv.app (L n) =
        t hrm ≫ (normalizedDVRRes l E X hrm).map (t hmn)) := by sorry

end WeilConjectures
