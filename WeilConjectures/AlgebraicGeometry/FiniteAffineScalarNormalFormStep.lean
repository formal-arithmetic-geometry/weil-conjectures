/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! # Scalar coherence for one part of the affine normal-form argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Scalar coherence for adjoining one coordinate to an arbitrary old normal form.
This does not assume or mention the recursively assembled old coordinate exchange.
Source: Charts, retained Step 4 of reduction-exceptional
(blueprint: lem-sp-finite-affine-scalar-normal-form-step).

Proof:
1. Expand the old normal form by finiteAffineExpandOrderedIso. In positive dimension
   this is the identity. At zero, scalar/pullback identity normalization, the scalar
   tensor-unit law and zero-shift naturality give compatibility with this expansion.
   Consequently the old conjugated arrow is also the conjugate of the direct normal
   scalar arrow by the expanded old normal forms.
2. Expand orderedAffineRightIso at the successor using towerENormalForm. Naturality
   of the new line normal form moves the old conjugated arrow through its input.
   Identify the actual coordinate scalar map with VectorTraceScalar.lineSource.
   Root inclusion and the coefficient-one generator identify the projective-line
   and ordered-Tate transports. The root scalar/pullback square and binary
   scalar/pullback tensor law give scalar compatibility of lineENormalForm.
3. Move the old shifted Tate tensor through the new affine projection using
   tensorEPullback. Its scalar square follows from the scalar/pullback tensor law,
   shift naturality and the old Tate-power pullback square. For the latter, transpose
   the ordinary comparison: both maps send a pure ordered root tensor with
   coefficients a,b to the same pulled roots with coefficient phi(a)b. Root
   normalization proves the degree-one case; the unit and ordered tensor recursions
   prove all powers. Sheafification preserves the resulting equality. Flatness of
   the Tate sheaf identifies this ordinary square with its derived single square.
4. The normalized scalar tensorator preserves the tensor associator. The proved
   positive ordered Tate product square appends the new root factor; at old power
   zero use the scalar tensor-unit normalization instead. The integer tensor/shift
   coherence combines shifts 2d and 2 into 2(d+1) in their original order, so no
   permutation or additional Koszul sign occurs.
5. The scalar/pullback composition law combines the new affine projection with the
   old one. The resulting factors are exactly the direct successor normal scalar
   map. Cancel the expanded old normal forms and their inverses to obtain the
   displayed equation. This argument is natural in every derived input K. -/
theorem finiteAffineScalarNormalForm_step
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S d) N hA hB
        (affineTraceInvertible N S hS d) ((affineTraceRight A N hA S d).obj K)).hom ≫
        (affineTraceLineRight B N hB (affineTraceTower S d)).map
          ((scalarExtension φ (affineTraceTower S d)).map
              ((orderedAffineRightIso A N hN hA S hS d).hom.app K) ≫
            finiteAffineOrderedScalarMap φ N hA hB S d K ≫
            (orderedAffineRightIso B N hN hB S hS d).inv.app
              ((scalarExtension φ S).obj K)) ≫
        (orderedAffineRightIso B N hN hB S hS (d + 1)).hom.app
          ((scalarExtension φ S).obj K) =
      (scalarExtension φ (affineTraceTower S (d + 1))).map
          ((orderedAffineRightIso A N hN hA S hS (d + 1)).hom.app K) ≫
        finiteAffineOrderedScalarMap φ N hA hB S (d + 1) K := by
  sorry

end AlgebraicGeometry.Etale
