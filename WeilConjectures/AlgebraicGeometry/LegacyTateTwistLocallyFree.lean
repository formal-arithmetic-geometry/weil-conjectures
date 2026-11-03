/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import all WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.SmoothPurity.Integral.IntegralObjectPullbackLine
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherence
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Historical Tate-twist proof, retained for legacy callers

This archive preserves the old completed/common-stage theorem under the explicit
`tateTwist_locallyFree_legacy` name. The current native theorem is in
`Sheaf.Paper.TateTwistLocallyFree`; this archive is not a dependency of that theorem.

## Original documentation

Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3)
(blueprint: det-def-sp-tate-twist-locally-free).

The helpers specialize the recorded constant sheaf, root module, scalar extension,
signed line and tensor functors. All positive root levels are indexed by `n + 1`.
The theorem includes one common cover, normalized generators, canonical Kummer
independence, signed invertible lines and equivalences with the negative twists.

The finite clauses and the definitions they use are in
`Sheaf.Paper.TateTwistFiniteLocallyFree` (`tateTwist_finite_locallyFree`), the integral and
rational twist functors, signed-line predicates and local calculations in
`Sheaf.Paper.TateTwistIntegralLines`; both are imported publicly.

## Main statements

* `tateTwist_locallyFree` states all three source clauses for all four coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall
  tateDerived

/-- One common covering trivializes the compatible root generators and all coefficient
lines; Kummer transitions induce the canonical A-linear isomorphisms; every signed twist
is a line, with positive and negative twist functors inverse on the specified categories.

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, all three clauses
(blueprint: det-def-sp-tate-twist-locally-free).

Proof:
1. The compatible root-tower local model supplies one pro-etale cover, compatible
   sections at every positive root level, and unit-to-root basis isomorphisms.
   Their naturality gives the displayed transition and slice formulas.
2. Annihilation supplies the quotient map from Z/ell^(r+1) to A. Form the
   scalar-extension adjunct of the specified root transition. Its value on a
   pure tensor is the prescribed Kummer formula. On the root cover it carries
   the chosen generator to the chosen generator, so it is locally and globally
   an isomorphism. Signed-line tensor equivalences give all finite signed powers
   and their two inverse functors on unbounded complexes.
3. Extend the same integral root basis to every finite coefficient field E.
   The completed integral local model identifies this extension with the actual
   integral Tate line. Signed powers and internal duals remain trivial on the
   same cover. The finite scalar reductions are the finite Tate lines already
   constructed, so coherent reduction and reconstruction give the two inverse
   intrinsic integral twist functors.
4. Identify the actual integral right-tensor functor with its completed line
   model. Prove its additivity and scalar linearity. Localize the two inverse
   natural isomorphisms; induction on pure Hom scalar tensors identifies these
   localized functors with the intrinsic rational twist functors.
5. For each signed integral line, the completed pullback calculation for a
   supplied slice basis identifies its actual derived inverse image with the
   regular line. Rational pullback then gives the required rational local
   trivializations. Transport these from the least finite coefficient stage
   to obtain the algebraically closed local trivializations.
6. Compute opposite integral Tate object products using a flat single-complex
   representative, completeness, the ordinary-to-completed comparison and the
   signed evaluation isomorphism. Localize this product to rational
   coefficients and identify the common-stage product on objects from one stage.
7. Natural fixed-right tensor associativity and the specified regular unit in
   the common-stage category combine with the opposite object products (and
   braiding for the reversed product) to give both inverse composites of the
   actual algebraically closed twist functors. Assemble all clauses using the
   original common root cover.
-/
theorem tateTwist_locallyFree_legacy
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  classical
  have _ := ι
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hr⟩ := tateRootCover X ℓ
  let hi (F : Type u) [Field F] [Algebra (Padic ℓ) F]
      [FiniteDimensional (Padic ℓ) F] (i : I) :
      Nonempty ((purTwistIntegralModule X ℓ F).over (U i) ≅
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted ℓ F X)).over (U i)) :=
    tateIntegralTrivial X ℓ F (U i) (hr i).some
  refine ⟨I, U, f, ζ, e, hc, hζ, he,
    tateFiniteClause X ℓ U f hc ζ e hζ he,
    tateSignedLine_of_trivial X (completedIntegralCommRingSheafUnrestricted ℓ E X)
      (purTwistIntegralModule X ℓ E) U (hi E), ?_⟩
  intro D hD
  have hE := tateRationalSigned D ℓ hD E X U (hi E)
  let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} ℓ Ω
    (Padic.finiteCoefficientBase ℓ Ω)
  have hΩ := tateQbarSigned_of_rational D ℓ hD X Ω U
    (tateRationalSigned D ℓ hD E₀ X U (hi E₀))
  refine ⟨hE, hΩ, fun n ↦ ⟨?_, ?_, ?_⟩⟩
  · exact tateIntegralInverse D ℓ hD E X (tateIntegralFiniteReductions X ℓ E) n
  · exact tateRationalInverse D ℓ hD E X n
  · exact tateQbarInverse D ℓ hD X Ω n (hΩ.2 n).some

end AlgebraicGeometry.Scheme
