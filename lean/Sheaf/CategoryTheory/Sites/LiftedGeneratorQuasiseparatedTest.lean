/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentToposRepair

/-!
# Finite lifted generator covers and the quasi-separatedness test

Source: literature/stacks-project/sites.tex, Tag 0D07 and Tags 0GMP, 0GMQ;
auxiliary extracted from steps 3--5 and 7 of lem-trf-coherent-epimorphic-quotient
(blueprint: lem-trf-lifted-generator-quasiseparated-test).
-/

@[expose] public section

set_option autoImplicit false

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite covers by a fixed coherent generating family retain lifts through any
 epimorphism onto a quasi-compact object. Quasi-separatedness can be tested on pairs
 of these generators mapping through an arbitrary fixed epimorphism.

Source: Stacks, Sites, Tag 0D07 (definition-quasi-compact-topos), Tags 0GMP and 0GMQ;
agent auxiliary from lem-trf-coherent-epimorphic-quotient, steps 3--5 and 7
(blueprint: lem-trf-lifted-generator-quasiseparated-test).

The family `obj` describes the objects of the full generating subcategory; its
replete object property expresses closure under finite limits. All coproduct
families use the containing universe `w` of def-weil-size-convention. Joint
 epimorphy is `Epi (Sigma.desc ...)`, with `Epi` meaning right cancellation.

Proof:
1. Cover the domain Y of e by the generating family. The composites with e are
   jointly epimorphic: equality after every composite implies equality after the
   generating coproduct map, then cancellation of that map and e gives equality.
   Quasi-compactness of X selects a finite subfamily of composites. Keep their
   original arrows to Y as the lifts v; write their composites as u. Apply this
   to the identity of X for the particular assertion. The finite family may be empty.
2. If A is quasi-separated, each pair of coherent generators is quasi-compact;
   the definition applied to k followed by p and l followed by p gives the test.
3. Conversely fix quasi-compact B,C over A. Pull p back to B and C. The resulting
   maps are epimorphisms by lem-trf-topos-finite-cover-calculus, clause (1).
   Step 1 supplies finite generator covers of B,C lifting to these pullbacks.
   Their projections to P give maps k_i,l_j with the required composites to A.
4. The assumed test makes each generator fibre product K_i ×_A L_j quasi-compact.
   Clause (1) of lem-trf-topos-finite-cover-calculus says their product family
   covers B ×_A C. Clause (3) makes its target quasi-compact, including when either
   finite cover is empty. This proves quasi-separatedness of A by definition.
No quasi-compactness or quasi-separatedness of P or A is assumed.
-/
theorem finite_lifted_generator_covers_and_quasiSeparated_test
    {E : Type u} [Category.{v} E] [HasCoproducts.{w} E] [HasFiniteLimits E]
    (_hE : CoherentToposRepair.IsCoherentTopos.{w} E)
    (G : Type w) (obj : G → E)
    (_hcoherent : ∀ i : G, IsCoherentObject.{w} (obj i))
    (_hgenerating : ∀ X : E,
      ∃ (I : Type w) (ι : I → G) (f : ∀ i, obj (ι i) ⟶ X), Epi (Sigma.desc f))
    (_hlimits : ∀ (J : Type) [SmallCategory J] [FinCategory J],
      ObjectProperty.IsClosedUnderLimitsOfShape
        ((fun X : E ↦ ∃ i : G, Nonempty (X ≅ obj i)) : ObjectProperty E) J) :
    (∀ (Y X : E) (e : Y ⟶ X), Epi e → IsQuasiCompactObject.{w} X →
      ∃ (I : Type w) (_ : Finite I) (ι : I → G)
        (u : ∀ i, obj (ι i) ⟶ X) (v : ∀ i, obj (ι i) ⟶ Y),
        (∀ i, v i ≫ e = u i) ∧ Epi (Sigma.desc u)) ∧
    (∀ X : E, IsQuasiCompactObject.{w} X →
      ∃ (I : Type w) (_ : Finite I) (ι : I → G)
        (u : ∀ i, obj (ι i) ⟶ X), Epi (Sigma.desc u)) ∧
    (∀ (P A : E) (p : P ⟶ A), Epi p →
      (IsQuasiSeparatedObject.{w} A ↔
        ∀ (i j : G) (k : obj i ⟶ P) (l : obj j ⟶ P),
          IsQuasiCompactObject.{w} (pullback (k ≫ p) (l ≫ p)))) := by
  sorry

end CategoryTheory
