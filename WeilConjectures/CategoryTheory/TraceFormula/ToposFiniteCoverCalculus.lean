/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TraceFormula.CoherentTopos
public import WeilConjectures.AlgebraicGeometry.OrientedNearbyCycles.OrientedNearbyCycles
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Epimorphic families and finite quasi-compact cover calculus

Source: Stacks Project, `sites.tex`, Tags 00WN, 00W2, 00WK, 0GMP and 0GMQ;
the agent expansion of the local-lifting and finite-cover arguments
(blueprint: lem-trf-topos-finite-cover-calculus).

The site and all section and index sets lie in the common containing universe
`max u v w`, following `def-weil-size-convention`. Covering sieves express local
lifting independently of the choice of a precoverage presenting the topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Joint epimorphy is equivalent to local lifting through individual family members,
and is stable under pullback and fibre products of families. Epimorphic images and
finite coproducts preserve quasi-compactness, including the empty coproduct. Hence a
finite jointly epimorphic family of quasi-compact objects has quasi-compact target.

Source: Stacks Project, `sites.tex`, Tags 00WN, 00W2, 00WK, 0GMP and 0GMQ,
with the agent expansion recorded in the node
(blueprint: lem-trf-topos-finite-cover-calculus).

Proof:
1. Form the objectwise disjoint union presheaf of a family. Its sheafification is
   the coproduct of sheaves by the adjunction in `def-weil-pbc-sheafification`:
   maps from that presheaf to a sheaf are exactly families of maps from its summands.
   This also constructs the coproduct of an empty family.
2. By `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, the coproduct map is
   epic exactly when sections locally lift to this sheafification. By
   `lem-weil-pbc-site-sheafification-sections-local`, refine so each lift belongs to
   one actual presheaf summand. Compose covers using `def-weil-pbc-sites-and-cohomology`.
   Conversely, summand lifts give coproduct lifts, so the same epimorphism criterion
   applies. The member index may vary on the covering.
3. For a map Z to Y, lift the image of a section of Z locally to some X_i. By
   `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, the pair is a section of the
   pullback and lifts the original section of Z. Step 2 gives joint epimorphy of
   the pullback family, including singleton families. For two families over A,
   first lift the B component locally and then the C component on a further cover.
   The images in A agree, so the pair is a section of X_i ×_A Y_j. Compose covers
   and apply step 2 to obtain the fibre-product-family assertion.
4. Pull a jointly epic family over Y back along an epimorphism X to Y. If X is
   quasi-compact, choose finitely many members covering X by `def-trf-coherent-topos`.
   Any two maps out of Y agreeing on the selected original members agree after the
   selected pullbacks, hence after X, hence on Y: cancel the selected coproduct map
   and then X to Y. The selected original family is thus jointly epic.
5. Given a finite family of quasi-compact X_i, pull any jointly epic family over
   their coproduct back to each X_i and choose a finite subfamily there. The union
   of these finitely many finite sets is finite. Agreement on its members implies
   agreement on each X_i by cancellation and thus on the coproduct by its universal
   property. For the empty family take the empty selection: maps from the initial
   object agree uniquely. No pointwise emptiness of the initial sheaf is assumed.
6. A finite jointly epic family of quasi-compact objects gives an epimorphism from
   a quasi-compact coproduct by step 5. Step 4 makes its target quasi-compact. This
   argument also includes the empty family.
-/
theorem topos_finite_cover_calculus
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∀ (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y),
      Epi (Sigma.desc f) ↔
        ∀ (U : C) (y : Y.obj.obj (op U)),
          ∃ S : Sieve U, S ∈ J U ∧
            ∀ (V : C) (a : V ⟶ U), S a →
              ∃ (i : I) (x : (X i).obj.obj (op V)),
                (f i).hom.app (op V) x = Y.obj.map a.op y) ∧
    (∀ (I : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y Z : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y),
      Epi (Sigma.desc f) → Epi (Sigma.desc (fun i ↦ pullback.snd (f i) g))) ∧
    (∀ (X Y Z : Sheaf J (Type (max u v w))) (e : X ⟶ Y) (g : Z ⟶ Y),
      Epi e → Epi (pullback.snd e g)) ∧
    (∀ (I K : Type (max u v w)) (X : I → Sheaf J (Type (max u v w)))
      (Y : K → Sheaf J (Type (max u v w))) (A B D : Sheaf J (Type (max u v w)))
      (f : ∀ i, X i ⟶ B) (g : ∀ k, Y k ⟶ D) (b : B ⟶ A) (d : D ⟶ A),
      Epi (Sigma.desc f) → Epi (Sigma.desc g) →
        Epi (Sigma.desc (fun p : I × K ↦
          pullback.map (f p.1 ≫ b) (g p.2 ≫ d) b d (f p.1) (g p.2) (𝟙 A)
            (Category.comp_id _) (Category.comp_id _)))) ∧
    (∀ (X Y : Sheaf J (Type (max u v w))) (e : X ⟶ Y),
      Epi e → IsQuasiCompactObject.{max u v w} X →
        IsQuasiCompactObject.{max u v w} Y) ∧
    (∀ (I : Type (max u v w)) [Finite I] (X : I → Sheaf J (Type (max u v w))),
      (∀ i, IsQuasiCompactObject.{max u v w} (X i)) →
        IsQuasiCompactObject.{max u v w} (∐ X)) ∧
    (∀ (I : Type (max u v w)) [Finite I] (X : I → Sheaf J (Type (max u v w)))
      (Y : Sheaf J (Type (max u v w))) (f : ∀ i, X i ⟶ Y),
      (∀ i, IsQuasiCompactObject.{max u v w} (X i)) → Epi (Sigma.desc f) →
        IsQuasiCompactObject.{max u v w} Y) := by
  sorry

end CategoryTheory
