/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence

/-! # Compatible algebraization before the torsion estimate

Source: Stacks Project, Tag 088A, construction of G_e and its comparison maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraize the second-ideal quotient systems and their comparison map.
This construction does not require any torsion hypothesis on α.
Source: Stacks Project, Tag 088A (lemma-existence-tricky), first part of the proof.
https://stacks.math.columbia.edu/tag/088A
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift).

Proof: Fix e and put Z_e = V(K^(e+1)). The system of quotients
M_n/K^(e+1)M_n is coherent and I-adic: coherence follows on affine opens from
finite generation, and its transition quotient identities follow by taking
successive quotients in either order. Its terms are killed by K^(e+1).
The closed-immersion formal equivalence descends it to Z_e. Apply a quasi-inverse
of the assumed completion equivalence on Z_e, and push forward, obtaining a
coherent module G_e with a natural isomorphism between its I-completion and the
quotient system. This is an algebraization through an equivalence, hence is
specified up to unique isomorphism together with its comparison.

At level e+1, reduce G_(e+1) by K^(e+1). Completion identifies this quotient with
the level-e quotient system, because the two successive K-quotients equal the
smaller quotient. Full faithfulness on Z_e gives an isomorphism from this
quotient to G_e. Compose with the quotient projection to define the transition.
Define all longer transitions by composition. Faithfulness proves their
compatibility with the completion comparisons. The annihilation and quotient
identities just established show that these modules form N in Coh(X,K).
The completion comparisons assemble into σ; naturality in the second index
holds for each chosen comparison, and naturality in e is the transition identity.

Reduce α_n by K^(e+1), then compose with θ_(e,n) inverse. Naturality makes
these maps a morphism of I-adic systems. Both source and target are supported
on Z_e, so full faithfulness of completion there lifts it to
δ_e : G_e → H/K^(e+1)H. Faithfulness proves that the δ_e commute with the
transitions, since their completions do so by naturality of α, θ and σ.
Thus they assemble into δ. The defining equations for the lifts are exactly
the displayed comparison square. The projection identity hθ identifies its
chosen quotient interchange with the canonical reduction of H. No torsion
claim is used or produced by this construction. -/
theorem grothendieckDevissage_secondAdicSystem_lift
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (hθ : ∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H.obj ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H.obj ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj)) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅
        (M.obj ⋙ formalCompletionFunctor K).flip),
      ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by sorry

end AlgebraicGeometry
