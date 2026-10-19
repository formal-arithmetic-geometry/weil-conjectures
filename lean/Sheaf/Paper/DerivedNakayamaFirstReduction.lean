/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.Paper.DerivedNakayamaFirstReductionVanishing
import Sheaf.Paper.DerivedNakayamaFirstReductionTriangles
import Sheaf.Paper.DerivedNakayamaFirstReductionShifts
import Sheaf.Paper.DerivedNakayamaFirstReductionIsIso

/-!
# Derived Nakayama from the first reduction

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction).

The canonical reduction functor at index n is reduction modulo pi^(n+1).
The four conjuncts express vanishing, closure under cones, closure under all integer
shifts, and detection of isomorphisms by the first reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

/-- Derived complete complexes vanish if their first reduction vanishes, are closed under
cones and shifts, and have isomorphisms detected by their first reduction.

Source: blueprint main-20261015, first-reduction lemma, Vanishing, Cones and Isomorphisms
paragraphs (blueprint: det-pe-derived-nakayama-first-reduction).

Proof. The four helper theorems prove the four conjuncts separately.
1. Compare finite scalar extension followed by restriction with integral derived tensor.
   The successive coefficient triangles give vanishing of every reduction by induction.
   Faithful exact restriction detects the vanishing used in this argument. The specified
   Roos derived-limit triangle then gives vanishing of a complete complex.
2. On cochain complexes, the specified Roos construction is an additive functor with a
   natural augmentation. Evaluation and tensor products carry the splitting operators of
   any degreewise split short exact sequence to splitting operators after applying Roos.
   The derived triangles of these two short exact sequences and the two-isomorphism
   criterion transfer invertibility of the endpoint augmentations to the middle one.
3. A signed chain comparison identifies roos(P[r]) with roos(P)[r], carrying the specified
   augmentation to its shift. Shifts preserve K-flatness and quasi-isomorphisms, hence
   preserve completeness. The signed chain comparison is proved explicitly.
4. Represent the first arrow of a distinguished triangle by a right fraction between
   K-flat representatives, then resolve the source of the fraction by a K-flat complex W.
   The standard sequence B -> cone(W -> B) -> W[1] is degreewise split. Steps 2 and 3
   make its middle augmentation invertible. K-flatness is closed under cones. The given
   distinguished triangle is isomorphic to this cone triangle on its first two vertices,
   which supplies a complete representative of its third vertex.
5. Apply cone closure to a morphism of complete objects. Derived reduction is triangulated;
   if the first reduction of the morphism is invertible, the first reduction of its cone
   is zero. Step 1 makes the complete cone zero, so the original morphism is invertible.

There is no boundedness assumption, no restriction on X, and no invertibility hypothesis
on l on X. The dependency indexes positive coefficient powers by n+1, so index zero is K_1. -/
theorem derived_nakayama_first_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj K) →
        (∀ n : ℕ, IsZero ((AdicCompletion.derivedReduction l E X n).obj K)) ∧ IsZero K) ∧
    (∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
      IsDerivedComplete l E X T.obj₁ → IsDerivedComplete l E X T.obj₂ →
        IsDerivedComplete l E X T.obj₃) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K → ∀ r : ℤ, IsDerivedComplete l E X (K⟦r⟧)) ∧
    (∀ (K L : DerivedCategory (AdicCompletion.Modules l E X)) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((AdicCompletion.derivedReduction l E X 0).map f) → IsIso f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact derived_nakayama_first_reduction_vanishing l E X
  · exact derived_nakayama_first_reduction_triangles l E X
  · exact derived_nakayama_first_reduction_shifts l E X
  · exact derived_nakayama_first_reduction_isIso l E X

end AlgebraicGeometry.ProEtale
