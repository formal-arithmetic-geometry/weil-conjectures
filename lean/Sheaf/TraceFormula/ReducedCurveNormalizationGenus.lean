/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Irreducible
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Normalization formula for the arithmetic genus of a reduced proper curve

Source: Temkin, *Stable Modification of Relative Curves*, Appendix B, Lemma B.1,
printed p. 57 (blueprint: lem-trf-reduced-curve-normalization-genus).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a nonempty proper reduced one-dimensional scheme over an algebraically closed field,
the finite componentwise normalization has smooth proper connected components and the
normalization quotient is supported at finitely many closed points; its Euler characteristic
is the sum of the component genera and the stalk dimensions.

The stalks of the quotient are finite-dimensional over `k`, so its support is
`{y | δ y ≠ 0}`; this set is finite and consists of closed points.

Proof (blueprint: lem-trf-reduced-curve-normalization-genus):
1. Properness gives finite type and Noetherianity; reduced algebraic normalization gives the
   finite component family, finite surjective normalization, and the dense normal locus.
2. Each reduced irreducible component is integral, proper and one-dimensional; normalization
   properties over a perfect algebraically closed field give a smooth proper connected curve.
3. The structure-sheaf map into the finite normalization pushforward is injective by the
   reduced-induced component structure and the integral-closure construction, giving the
   normalization quotient.
4. Finite pushforward and coherent kernel/cokernel results make the quotient coherent and
   give closed support.
5. The normal locus misses only a zero-dimensional closed subset, hence finitely many closed
   points; the finite-support sheaf-gluing argument identifies global sections with the direct
   sum of stalks.
6. Zero-dimensional coherent cohomology computes its Euler characteristic as the sum of stalk
   dimensions. Cohomology of each normalized proper curve gives Euler characteristic one minus
   its genus, and finite affine pushforward plus additivity sums these terms.
7. Additivity for the normalization exact sequence and `p_a = 1 - chi` yield the displayed
   formula. No connectedness or nodality of the original curve is used.
-/
theorem reduced_curve_normalization_genus
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsReduced X] [Nonempty X]
    (hPure : Scheme.IsPureDimension X 1) :
    ∃ (v : ℕ) (e : Fin v ≃ {Z : Set X // Z ∈ irreducibleComponents X}),
      ∃ (hI : ∀ i : Fin v,
          IsIntegral
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subscheme),
        (∀ i : Fin v,
          Smooth
            (@Scheme.fromNormalization _ (hI i) ≫
              (Scheme.IdealSheafData.vanishingIdeal
                ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
                ≫ (X ↘ Spec (.of k))) ∧
          IsProper
            (@Scheme.fromNormalization _ (hI i) ≫
              (Scheme.IdealSheafData.vanishingIdeal
                ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
                ≫ (X ↘ Spec (.of k))) ∧
          IsConnectedCurve
            (@Scheme.fromNormalization _ (hI i) ≫
              (Scheme.IdealSheafData.vanishingIdeal
                ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
                ≫ (X ↘ Spec (.of k)))) ∧
        IsFinite
          (Limits.Sigma.desc (fun i : Fin v ↦
            @Scheme.fromNormalization _ (hI i) ≫
              (Scheme.IdealSheafData.vanishingIdeal
                ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι) ) ∧
        ∃ (F : X.Modules) (δ : X → ℕ),
          F = cokernel (SheafOfModules.unitToPushforwardObjUnit
            (Limits.Sigma.desc (fun i : Fin v ↦
              @Scheme.fromNormalization _ (hI i) ≫
                (Scheme.IdealSheafData.vanishingIdeal
                  ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
                )).toRingCatSheafHom) ∧
          δ = (fun y ↦ Module.finrank k ((ModuleCat.restrictScalars
            ((X.presheaf.germ ⊤ y trivial).hom.comp
              (@algebraMap k Γ(X, ⊤) _ _ ((X ↘ Spec (.of k)).ΓAlgebra)))).obj
            (ModuleCat.of (X.presheaf.stalk y)
              ((F.presheaf.stalk y : AddCommGrpCat) : Type u)))) ∧
          (∀ y : X, Module.Finite k ((ModuleCat.restrictScalars
            ((X.presheaf.germ ⊤ y trivial).hom.comp
              (@algebraMap k Γ(X, ⊤) _ _ ((X ↘ Spec (.of k)).ΓAlgebra)))).obj
            (ModuleCat.of (X.presheaf.stalk y)
              ((F.presheaf.stalk y : AddCommGrpCat) : Type u)))) ∧
          Set.Finite {y : X | δ y ≠ 0} ∧
          (∀ y : X, δ y ≠ 0 → IsClosed ({y} : Set X)) ∧
          1 - Scheme.Modules.eulerChar k (Scheme.Modules.unit X) =
            (1 : ℤ) - v +
              ∑ i : Fin v,
                (Scheme.Hom.genus
                  (@Scheme.fromNormalization _ (hI i) ≫
                    (Scheme.IdealSheafData.vanishingIdeal
                      ⟨(e i).1, isClosed_of_mem_irreducibleComponents _ (e i).2⟩).subschemeι
                      ≫ (X ↘ Spec (.of k))) : ℤ) +
              ∑ᶠ y : {y : X // IsClosed ({y} : Set X)}, (δ y.1 : ℤ) := by
  sorry

end AlgebraicGeometry
