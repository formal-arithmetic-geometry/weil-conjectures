/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CompositionTrace
import WeilConjectures.SecSmoothPurity.FiniteNormalizedCompositionTrace
import WeilConjectures.SecSmoothPurity.IntegralNormalizedCompositionTrace


/-! # Finite and integral normalized smooth counit transitivity

Source: current blueprint sk-prop-sp-composition.proof.md, finite orientations,
finite tensor maps, and whole-tower realization; parent DAG Steps 3--5.
(blueprint: lem-pur-finite-integral-composition-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Finite and integral composition for the normalized smooth counits themselves.
Source: current blueprint sk-prop-sp-composition.proof.md, the finite and tower
paragraphs, and sk-prop-sp-composition, proof Steps 3--5.
(blueprint: lem-pur-finite-integral-composition-trace).

Proof in words. For a finite ring, compare the specified diagonal orientation of
the composite with the ordered product of the two diagonal orientations, using
composition-factors. Its tensor-transpose identity identifies the tensor maps
under the counit-preserving exceptional compositor. The finite-native tensor
comparison transports this equality through the actual section-action encoding
and the ordinary etale origin of every finite-Tor object. The finite-native Tate
comparison identifies the source word with root pullback, ordered tensor-power
concatenation and even-shift reassociation. These comparisons concern the actual
normalized finite counits: the five properties of existsUniqueNormalizedFamily
give affine integration, iteration on affine space and etale chart descent;
common-refinement descent identifies the maps for the given compactifications.
Apply the composite support functor to the resulting purity equation, then the
composite exceptional counit. Naturality of the first purity map moves the second
purity map past it; its counit equation leaves exactly the two smooth counits.
For integral coefficients, perform the orientation and tensor-transpose arguments
in the whole normalized tower category, and apply total derived limit to their
morphism equality. NativeIntegralCompositorRealization identifies support and
source compositors. Integral counit realization identifies the realized traces
with the specified normalized family's counits. This also identifies their
compactification changes: the normalized proper/open refinements commute with
the realized counits, so the equation holds for arbitrary ch and the H.compositor.
The integer coefficient presentation is the base-field integral presentation,
transported through its canonical coefficient identification. Dimensions zero,
empty schemes, zero finite rings and ramified integral coefficients are included.
No faithfulness of evaluation of a derived tower is used. -/
theorem finiteIntegralCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    (∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hA : (ell ^ (n + 1) : A) = 0),
      NormalizedCompositionTrace ell D hEll (.finite A fin n hA)) ∧
    NormalizedCompositionTrace ell D hEll .integers ∧
    ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      NormalizedCompositionTrace ell D hEll (.integral E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A fin n hA
    exact finiteNormalizedCompositionTrace ell D hEll A fin n hA
  · exact (integralNormalizedCompositionTrace ell D hEll).1
  · intro E
    exact (integralNormalizedCompositionTrace ell D hEll).2 E

end AlgebraicGeometry.ProEtale.PurityTransport
