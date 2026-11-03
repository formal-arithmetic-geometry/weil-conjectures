/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement

/-! # Finiteness of signed Tate tensor and finite coefficient extension

Source: latest blueprint, Tate compatibility, final restriction paragraph.
(blueprint: lem-wf-tate-finiteness)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
open PurityTransport

/-- Signed Tate tensor and finite field extension preserve the recorded finite
constant-model bounded constructibility condition and finite Tor amplitude.
Source: latest blueprint, lem-wf-tate-twist-compatibility.proof.md, scalar extension
and the restriction to Dctf (blueprint: lem-wf-tate-finiteness).
Proof: the compatible primitive-root cover trivializes the integral Tate line;
coefficient extension, positive tensor powers and evaluation duals trivialize all
signed lines on the same cover. Tensoring the finite scalar presentations on each
stratum with this rank-one free module preserves those presentations. The line is
flat, so its degree-zero complex is K-flat and the exact tensor homology formula
preserves the cohomological bounds. Tensor associativity with an arbitrary module
in degree zero preserves each Tor interval. For E contained in F the pulled-back
coefficient module F_X is finite free over E_X. Its extension functor is exact,
commutes with homology, and extends finite presentation matrices on each of the
original strata. The scalar tensor associator identifies extension followed by
tensor with a test F_X-module with the original tensor against its restriction;
this proves the same Tor bounds. These arguments apply to arbitrary schemes,
without any finite-type or Noetherian hypothesis, and include the empty scheme,
the zero coefficient ring, m=0, negative powers and E=F. -/
theorem tate_finiteness (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] :
    (∀ (c : Coefficient ell) (m : ℤ) (K : c.derived ell X),
      (constantModelBoundedConstructible (c.obj ell) X K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible (c.obj ell) X (K ⊗ derivedTateLine ell c X m) ∧
        DerivedCategory.finiteTorAmplitude _ (K ⊗ derivedTateLine ell c X m)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (K : (Coefficient.rational E).derived ell X),
      (constantModelBoundedConstructible ((Coefficient.rational E).obj ell) X K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible ((Coefficient.rational F).obj ell) X
        ((finiteCoefficientDerivedExtension X ell h).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((finiteCoefficientDerivedExtension X ell h).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
