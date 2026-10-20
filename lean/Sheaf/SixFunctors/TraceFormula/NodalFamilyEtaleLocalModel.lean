/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.FormalLocalStructureNodalFamily
import Sheaf.TraceFormula.NodalFamilyNoetherianApproximation
import Sheaf.TraceFormula.RelativeCompletionEtaleApproximation
import WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField

/-! # Étale local model of an at-worst-nodal family

Source: Stacks Project, curves.tex, Tag 0CBY (blueprint:
`lem-trf-nodal-family-etale-local-model`).

The auxiliary quotient ring and its canonical map to `ℤ[a]` encode
`Spec ℤ[u,v,a]/(uv-a) → Spec ℤ[a]` in every scheme universe.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The integers `ℤ`, lifted to universe `u` so that the universal chart lives in every
scheme universe.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
abbrev nodalInteger : Type u := ULift.{u} ℤ

/-- The coordinate ring `ℤ[a]` of the base of the universal nodal chart.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
abbrev nodalBaseRing : Type u := Polynomial (nodalInteger)

/-- The polynomial ring `ℤ[a][u,v]`, with `u = X 0` and `v = X 1`.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
abbrev nodalPolynomialRing : Type u :=
  MvPolynomial (Fin 2) (nodalBaseRing)

/-- The relation `uv-a` in the universal nodal chart.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalRelation : nodalPolynomialRing :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C Polynomial.X

/-- The coordinate ring `ℤ[u,v,a]/(uv-a)` of the universal nodal chart.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalModelRing : Type u :=
  nodalPolynomialRing ⧸
    Ideal.span ({nodalRelation} : Set (nodalPolynomialRing))

noncomputable instance : CommRing (nodalModelRing) :=
  Ideal.Quotient.commRing _

/-- The base `Spec ℤ[a]` of the universal nodal chart.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalBase : Scheme.{u} :=
  Spec (.of (nodalBaseRing))

/-- The universal affine nodal chart `Spec ℤ[u,v,a]/(uv-a)`.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalModel : Scheme.{u} :=
  Spec (.of (nodalModelRing))

/-- The structural morphism of the universal nodal chart.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalModelBaseMap : nodalModel ⟶ nodalBase :=
  Spec.map (CommRingCat.ofHom <|
    (Ideal.Quotient.mk _).comp (MvPolynomial.C))

/-- The coefficient map from the lifted integers to a commutative ring.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
def nodalIntegerMap (R : Type u) [CommRing R] :
    nodalInteger →+* R :=
  (Int.castRingHom R).comp ULift.ringEquiv.toRingHom

/-- The map `ℤ[a] → Γ(V, 𝒪_V)` sending `a` to a global function `h`.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalPolynomialMap {V : Scheme.{u}} (h : Γ(V, ⊤)) :
    nodalBaseRing →+* Γ(V, ⊤) :=
  Polynomial.eval₂RingHom (nodalIntegerMap (Γ(V, ⊤))) h

/-- The morphism `V → Spec ℤ[a]` induced by `a ↦ h`.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalBaseMap {V : Scheme.{u}} (h : Γ(V, ⊤)) :
    V ⟶ nodalBase :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (nodalPolynomialMap h))

/-- A completed local ring used in the nodal-fibre hypothesis.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalCompletedLocalRing {F : Scheme.{u}} (z : F) : Type u :=
  let A : Type u := (F.presheaf.stalk z : Type u)
  AdicCompletion (IsLocalRing.maximalIdeal A) A

noncomputable instance {F : Scheme.{u}} (z : F) :
    CommRing (nodalCompletedLocalRing z) := by
  dsimp [nodalCompletedLocalRing]
  infer_instance

/-- The completed nodal fibre ring `Ω[[u,v]]/(uv)`.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def nodalPowerSeriesQuotient (Ω : Type u) [CommRing Ω] : Type u :=
  (MvPowerSeries (Fin 2) Ω) ⧸
    Ideal.span ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1} :
      Set (MvPowerSeries (Fin 2) Ω))

noncomputable instance (Ω : Type u) [CommRing Ω] :
    CommRing (nodalPowerSeriesQuotient Ω) :=
  Ideal.Quotient.commRing _

/-- Projection of a geometric fibre to its algebraically closed base field.
Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
noncomputable def geometricFiberProjection {X S : Scheme.{u}}
    (f : X ⟶ S) (Ω : Type u) [Field Ω] (g : Spec (.of Ω) ⟶ S) :
    pullback (C := Scheme) f g ⟶ Spec (.of Ω) :=
  pullback.snd f g

/-- Étale local equation `uv=h` at a nonsmooth point of a flat family of curves.
Source: Stacks Project, curves.tex, Tag 0CBY, lemma-etale-local-structure-nodal-family
(hypothesis: at-worst-nodal of relative dimension 1, Tags 0C5A / 0C59 (1)).

Proof (Tag 0CBY, first proof, as in the DAG node):
1. By `lem-trf-nodal-family-noetherian-approximation` at `x`, get affine opens
   `X°, S°`, `X° = X₀ ×_{S₀} S°` with `f₀ : X₀ → S₀` flat, finitely presented, between
   schemes of finite type over `ℤ`, with the same fibre condition; the image `x₀` of
   `x` is nonsmooth for `f₀`. It suffices to build the chart for `(f₀, x₀)`.
2. Let `s₀ = f₀ x₀`, `k = κ(s₀)`, `C = (X₀)_{s₀}`, of finite type over `k`. By
   `lem-trf-nodal-family-fitting-singular`, `x₀` is nonsmooth on `C`; by
   `lem-trf-nodal-point-finite-separable-splitting` there are a finite separable `K/k`
   and a `K`-rational split node `x_K ∈ C_K` over `x₀`.
3. By `lem-weil-pbc-etale-neighbourhood-prescribed-residue-field`, get an étale
   `(V₁, v₁) → (S₀, s₀)` with `κ(v₁) = K`; `x_K` gives a `K`-rational `x₁` of
   `X₁ = X₀ ×_{S₀} V₁`. Shrink `V₁` to an affine of finite type over `ℤ`; `X₁ → V₁` is
   flat and locally finitely presented (base change).
4. `A = 𝒪_{V₁,v₁}` is Noetherian; `x₁` is closed in its fibre (it is `K`-rational).
   By `lem-trf-formal-local-structure-nodal-family`, `𝒪̂_{X₁,x₁} ≅ Â[[u,v]]/(uv - ĥ)`
   as `Â`-algebras, with `ĥ ∈ 𝔪_A Â`.
5. With `T = Spec ℤ[a]`, `Y = Spec ℤ[u,v,a]/(uv - a)` and `σ : 𝒪_{T,t} → Â`,
   `a ↦ ĥ`, the base change `Y_σ` is the formal model and the completions agree.
6. By `lem-trf-relative-completion-etale-approximation` (Tag 0GDX), get an étale
   `(V₂, v₂) → (V₁, v₁)`, `τ : V₂ → T`, an étale `(U₀, u₀) → (X₁, x₁)` and an étale
   `V₂`-map `U₀ → Y ×_{T,τ} V₂ = Spec_{V₂} 𝒪[u,v]/(uv - h₂)`, with `h₂ = τ^* a`.
7. `X₁ → X₀` is étale by base change, so `U₀ → X₀` and `V₂ → S₀` are étale composites
   and both triangles commute: the chart for `f₀` with `u₀` over `x₀`.
8. Pull back along `S° → S₀`: `V = V₂ ×_{S₀} S°`, `U = U₀ ×_{X₀} X°`, `h` the pullback of
   `h₂`; étaleness is stable under base change and composition with the open
   immersions `X° → X`, `S° → S`, and `W = Y ×_T V = Spec_V 𝒪_V[u,v]/(uv - h)`.
9. Base-changing the surjection `Spec κ(u₀) → Spec κ(x₀)` along `Spec κ(x) → Spec κ(x₀)`
   (`lem-weil-pbc-surjective-base-change`) gives a point of `U` over `x`.
(blueprint: lem-trf-nodal-family-etale-local-model) -/
theorem exists_etale_nodal_local_model
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f]
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ S),
      IsEmpty (pullback (C := Scheme) f g) ∨
        (Scheme.IsPureDimension (pullback (C := Scheme) f g) 1 ∧
          ∀ z : pullback (C := Scheme) f g,
            ¬ ((geometricFiberProjection f Ω g).stalkMap z).hom.FormallySmooth →
              Nonempty
                (nodalCompletedLocalRing z ≃+* nodalPowerSeriesQuotient Ω)))
    (x : X) (hx : x ∉ f.smoothLocus) :
    ∃ (V U : Scheme.{u}) (h : Γ(V, ⊤)) (v : V ⟶ S) (uMap : U ⟶ X)
      (w : U ⟶ V)
      (m : U ⟶ pullback (nodalModelBaseMap) (nodalBaseMap h)),
      Etale v ∧ Etale uMap ∧ Etale m ∧
        w ≫ v = uMap ≫ f ∧
        m ≫ pullback.snd (nodalModelBaseMap) (nodalBaseMap h) = w ∧
        ∃ z : U, uMap z = x := by
  sorry

end AlgebraicGeometry
