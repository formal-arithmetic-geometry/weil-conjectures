module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.TraceFormula.FormalLocalStructureNodalFamily
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel

import Sheaf.TraceFormula.FiniteResiduePointClosedInFibre
import Sheaf.TraceFormula.RelativeCompletionEtaleApproximation
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Algebraizing a rational split node over a finite-type integer base

Source: Stacks Project, curves.tex, Tag 0CBY, first proof, third paragraph;
Tag 0CBX; more-morphisms.tex, Tag 0GDX.
(blueprint: lem-trf-split-node-algebraization-finite-type)

The universal model and the section-induced base map are the existing constructions
registered by `def-trf-universal-nodal-model`. The displayed pullback is the chosen
construction of `Spec_V(𝒪_V[u,v]/(uv-h))`: on each affine open its coordinate algebra
is the polynomial quotient by `uv-h`, with the constants and both variables fixed.
The last conjunct states this affine-local canonical identification explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A rational split node in a flat locally finitely presented family over an affine
finite-type integer base admits elementary étale neighbourhoods and an étale chart `uv=h`.
Here `b` is written `g z`, and `τ` is written `nodalBaseMap h`: polynomial evaluation and
`ΓSpec.adjunction` identify maps to `Spec ℤ[a]` with global sections, with `h = τ* a`.
The target is the base change of the universal family and hence canonically the relative
spectrum `Spec_V(𝒪_V[u,v]/(uv-h))`, using the same constants and coordinates on affine opens.

Source: Stacks Project, Tag 0CBY, first proof, third paragraph; Tags 0CBX and 0GDX.
(blueprint: lem-trf-split-node-algebraization-finite-type)

Proof (the five DAG steps):
1. Locally finite presentation implies locally finite type by the affine-pair criteria
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` and `lem-weil-pbc-lft-affine-pairs`.
   The finite-type integer base is Noetherian by `lem-weil-pbc-finite-type-over-noetherian`.
   Its stalk is Noetherian by `lem-weil-pbc-affine-open-stalk-localization` and
   `lem-weil-pbc-localization-noetherian`. The residue-field isomorphism makes the point
   closed in its fibre by `lem-trf-finite-residue-point-closed-in-fibre`.
2. Apply `lem-trf-formal-local-structure-nodal-family` to get a completed parameter H in
   the completed maximal ideal, and the completed polynomial nodal model at its origin.
3. Send a to H. By `lem-weil-pbc-local-completion-local-ring`, inverse image of the completed
   maximal ideal defines t in Spec ℤ[a]; the map extends to a local map at t. The affine
   base-change description `lem-weil-pbc-fibre-product-affine-spectra` identifies the base
   change of the universal model with the completed-base model, preserving its origin.
4. Apply `lem-trf-relative-completion-etale-approximation` to this scalar-compatible
   completed-local isomorphism. Both bases are finite type over ℤ, and both families locally
   finite type. Its pointed elementary étale span gives U, V, both residue isomorphisms,
   and the two commuting triangles, including w(q)=v.
5. Put h=τ* a, using `lem-weil-pbc-morphism-into-affine-scheme`. On every affine open Spec C
   of V, `lem-weil-pbc-fibre-product-affine-spectra` identifies the target algebra with
   (ℤ[a][u,v]/(uv-a)) ⊗[ℤ[a]] C = C[u,v]/(uv-h). The maps fix C,u,v, hence commute with
   restriction. `lem-weil-pbc-affine-morphism-relative-spec` identifies their gluing with
   the stated relative spectrum. -/
theorem split_node_algebraization_finite_type
    {Z B : Scheme.{u}} (g : Z ⟶ B) [Flat g] [LocallyOfFinitePresentation g]
    [IsAffine B] (bZ : B ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType bZ] [QuasiCompact bZ]
    (z : Z) (hκ : Function.Bijective (g.residueFieldMap z).hom)
    (hsplit : Nonempty (@AlgEquiv (B.residueField (g z))
      (formalNodalCompletedStalk (g.fiber (g z)) (g.asFiber z))
      (formalNodalPowerSeriesQuotient (B.residueField (g z)) 0) _ _ _
      (formalNodalFiberCompletionAlgebra g z) inferInstance)) :
    ∃ (V U : Scheme.{u}) (v : V) (q : U) (h : Γ(V, ⊤))
      (e : V ⟶ B) (p : U ⟶ Z) (w : U ⟶ V)
      (m : U ⟶ pullback nodalModelBaseMap (nodalBaseMap h)),
      e v = g z ∧ p q = z ∧ w q = v ∧
        Etale e ∧ Etale p ∧ Etale m ∧
        w ≫ e = p ≫ g ∧ m ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h) = w ∧
        IsIso (e.residueFieldMap v) ∧ IsIso (p.residueFieldMap q) ∧
        ∀ A : V.Opens, IsAffineOpen A →
          IsAffineOpen ((pullback.snd nodalModelBaseMap (nodalBaseMap h)) ⁻¹ᵁ A) ∧
          ∃ φ : Γ(pullback nodalModelBaseMap (nodalBaseMap h),
              (pullback.snd nodalModelBaseMap (nodalBaseMap h)) ⁻¹ᵁ A) ≃+*
            formalNodalModelRing Γ(V, A)
              (V.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op h),
            (∀ c : Γ(V, A),
              φ (((pullback.snd nodalModelBaseMap (nodalBaseMap h)).app A).hom c) =
                algebraMap Γ(V, A) _ c) ∧
            ∀ k : Fin 2,
              φ (((pullback.fst nodalModelBaseMap (nodalBaseMap h)).appLE ⊤
                  ((pullback.snd nodalModelBaseMap (nodalBaseMap h)) ⁻¹ᵁ A) le_top).hom
                ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
                  (Ideal.Quotient.mk _ (MvPolynomial.X k)))) =
                Ideal.Quotient.mk _ (MvPolynomial.X k) := by
  sorry

end AlgebraicGeometry
