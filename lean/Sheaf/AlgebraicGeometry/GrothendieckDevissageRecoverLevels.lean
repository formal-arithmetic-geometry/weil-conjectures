/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import Sheaf.RingTheory.FormalGlueingComplexExact
import Sheaf.Topology.GlueSheavesOfModules

/-! # Recovering the original levels after second-ideal algebraization

Source: Stacks Project, Tag 088A, final paragraph
(blueprint: lem-weil-pbc-devissage-recover-levels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Reduction of a torsion-controlled K-algebraization recovers the original I-levels.
Here sigma is an isomorphism of doubly indexed diagrams, theta is the canonical quotient
interchange, and the comparison square relates the maps to H. No completion equivalence
on a thickening is assumed at this stage: that work is encoded in the supplied diagram.

Source: Stacks Project, Tag 088A, final paragraph, and Tag 0889, part (1), uniqueness
(blueprint: lem-weil-pbc-devissage-recover-levels).

Proof:
Fix a positive I-level n. Evaluation of sigma identifies the K-completion of M_n with
the I^n-quotient of N. Reduce beta modulo I^n and commute the two quotient operations,
using their universal cokernel descriptions. The canonical theta and the comparison
square identify the resulting completion map with the completion of alpha_n.
Thus F/I^n F, the reduction of a, and this comparison form an algebraization triple
for alpha_n completed along K. Reduction of the torsion-controlled map a has kernel
and cokernel killed by K^(2s), by the reduction lemma in Remark 0888. The given bound
on alpha_n makes M_n with alpha_n another torsion-controlled triple for the same map.
Uniqueness in the torsion-controlled version of Tag 0889 gives the desired level
isomorphism. For a transition from a later I-level to an earlier one, both composites
have the same comparison to H and the same K-completion. Full faithfulness for maps
between torsion-controlled triples (the formal-gluing uniqueness argument of 0889)
identifies the composites. Hence the level isomorphisms are natural in n.
The torsion conditions are on the actual coherent maps; completion alone would not
control components away from V(K). All levels remain positive.
-/
theorem grothendieckDevissage_recoverLevels
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (H : CoherentModules X)
    (α : M ⟶ (completion X I).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n)))))
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅ (M.obj ⋙ formalCompletionFunctor K).flip)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (hθ : ∀ e n : ℕ,
      formalModuleQuotientπ K (e + 1) H.obj ≫
        formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
        (θ.hom.app (op e)).app (op n) =
      formalModuleQuotientπ I (n + 1) H.obj ≫
        formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj))
    (hsquare : ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
        formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
      formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
        (θ.hom.app (op e)).app (op n))
    (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X K).obj F)
    (hβ : δ = β.hom ≫ (completion X K).map a)
    (ha : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel a.hom))) :
    ∃ φ : ∀ n : ℕᵒᵖ, ((completion X I).obj F).obj.obj n ≅ M.obj.obj n,
      ∀ (n m : ℕᵒᵖ) (f : n ⟶ m),
        ((completion X I).obj F).obj.map f ≫ (φ m).hom =
          (φ n).hom ≫ M.obj.map f := by
  sorry

end AlgebraicGeometry
