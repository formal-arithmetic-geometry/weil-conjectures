/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Counits, transposes and composition under adjoint-equivalence conjugation

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-purity-transport/prop-pur-adic-reconstruction-trace-coherence.proof.md,
sole paragraph, abstract counit transport and coherence calculations; Stacks 0037 and 0DV0
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus).

An equivalence `E : C ≌ N` packages the specified `R ⊣ L`, with `R = E.functor`,
`L = E.inverse`, unit `E.unitIso.hom` and counit `E.counitIso.hom`.
Conversely, `Adjunction.toEquivalence` packages any adjunction with invertible unit and
counit without changing those maps. The reverse adjunction is `E.symm.toAdjunction`:
its unit is `E.counitIso.inv` and its counit is `E.unitIso.inv`.

The conjugate of `F` is `E₁.functor ⋙ F ⋙ E₂.inverse`; the conjugate of `α` is
`Functor.whiskerRight (Functor.whiskerLeft E₁.functor α) E₂.inverse`.
The comparison `c_F` is the existing natural isomorphism
`E₁.invFunIdAssoc (F ⋙ E₂.inverse)`. Its components are `L₂(F(e₁))` by
`Equivalence.invFunIdAssoc_hom_app`. Thus its naturality in object maps and its
invertibility are part of its type, including for `G` with the two equivalences exchanged.
The compositor is `Functor.isoWhiskerLeft (E₁.functor ⋙ F) (E₂.invFunIdAssoc (H ⋙ E₃.inverse))`;
its components are `L₃(H(e₂))`, by the same existing component formula.

## Main statements

- `conjugation_counit`: counit of the specified composite adjunction.
- `conjugation_transpose`: transpose of the transported map.
- `conjugation_comparison_naturality`: comparison naturality in functor transformations.
- `conjugation_compositor_naturality`: compositor naturality in both transformations.
-/

@[expose] public section

universe u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃ z₁ z₂ z₃

namespace CategoryTheory.AdjointEquivalenceConjugation

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {N₁ : Type w₁} {N₂ : Type w₂} {N₃ : Type w₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{z₁} N₁] [Category.{z₂} N₂] [Category.{z₃} N₃]

/-- Counit of the adjunction obtained by the three specified compositions.
Source: blueprint reconstruction-trace-coherence proof, counit transport; Stacks 0037, 0DV0.
Proof: Step 2 of the node identifies the reverse adjunction, using the inverse triangle
identities. Step 3 applies `Adjunction.comp_counit_app` twice to
`E₁.toAdjunction`, `adj`, `E₂.symm.toAdjunction`. The result is
`L₂(ε ≫ F(e₁)) ≫ u₂⁻¹`; expand `L₂.map_comp` to obtain the displayed formula.
These are exactly the composite adjunctions of def-weil-pbc-composite-adjunction.
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus). -/
theorem conjugation_counit (E₁ : C₁ ≌ N₁) (E₂ : C₂ ≌ N₂)
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₁} (adj : F ⊣ G) (K : C₂) :
    ((E₁.toAdjunction.comp adj).comp E₂.symm.toAdjunction).counit.app K =
      E₂.inverse.map (F.map (E₁.counitIso.hom.app (G.obj (E₂.functor.obj K)))) ≫
        E₂.inverse.map (adj.counit.app (E₂.functor.obj K)) ≫ E₂.unitIso.inv.app K := by
  simp [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]

/-- The transpose of `L₁(a) ≫ c_G⁻¹` under the specified composite adjunction.
Source: blueprint reconstruction-trace-coherence proof, abstract transpose calculation;
Stacks 0037 and 0DV0.
Proof: Step 1 writes the inverse Hom bijection as `t ↦ F(t) ≫ ε`.
Step 4 identifies the comparison and its inverse with the images of `e` and `e⁻¹`.
Step 5 applies the three inverse Hom bijections of def-weil-pbc-composite-adjunction
successively. Naturality of `e₁` gives `e₁ ≫ a ≫ G(e₂⁻¹)` after the first;
naturality of `ε` gives `F(e₁) ≫ F(a) ≫ ε ≫ e₂⁻¹` after the second.
Step 6 applies `L₂` and then `u₂⁻¹`. The reverse triangle from Step 2 cancels
`L₂(e₂⁻¹) ≫ u₂⁻¹`, leaving `c_F ≫ L₂(F(a) ≫ ε)` as asserted.
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus). -/
theorem conjugation_transpose (E₁ : C₁ ≌ N₁) (E₂ : C₂ ≌ N₂)
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₁} (adj : F ⊣ G)
    (P : N₁) (N : N₂) (a : P ⟶ G.obj N) :
    (((E₁.toAdjunction.comp adj).comp E₂.symm.toAdjunction).homEquiv
      (E₁.inverse.obj P) (E₂.inverse.obj N)).symm
        (E₁.inverse.map a ≫ (E₂.invFunIdAssoc (G ⋙ E₁.inverse)).inv.app N) =
      (E₁.invFunIdAssoc (F ⋙ E₂.inverse)).hom.app P ≫
        E₂.inverse.map (F.map a ≫ adj.counit.app N) := by
  simp only [Adjunction.homEquiv_symm_apply, conjugation_counit,
    Functor.comp_map, Equivalence.invFunIdAssoc_inv_app,
    Equivalence.invFunIdAssoc_hom_app]
  simp only [Equivalence.symm_functor, Functor.comp_obj, Equivalence.symm_inverse,
    Functor.id_obj, Functor.map_comp, Equivalence.fun_inv_map, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hu : E₂.unitIso.inv.app (E₂.inverse.obj N) =
      E₂.inverse.map (E₂.counitIso.hom.app N) := E₂.unitInv_app_inverse N
  rw [hu]
  simp only [← E₂.inverse.map_comp]
  congr 1
  simp only [← Category.assoc, ← F.map_comp]
  simp only [Category.assoc, E₁.counitIso.inv_hom_id_app]
  dsimp only [Functor.id_obj]
  simp only [Functor.map_id, Category.id_comp, F.map_comp, Category.assoc]
  have hε := adj.counit.naturality (E₂.counitIso.inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map,
    Functor.id_obj] at hε
  have hε' := congrArg (fun f => f ≫ E₂.counitIso.hom.app N) hε
  simp only [Category.assoc, E₂.counitIso.inv_hom_id_app] at hε'
  dsimp only [Functor.id_obj] at hε'
  simpa only [Category.comp_id] using
    congrArg (fun f => F.map (E₁.counitIso.hom.app P) ≫ F.map a ≫ f) hε'

/-- The comparison is natural in transformations of functors. Its object-map naturality,
including that of its inverse, is already supplied by `Equivalence.invFunIdAssoc`.
Source: blueprint reconstruction-trace-coherence proof, coherence; Stacks 0037 and 0DV0.
Proof: Step 4 applies naturality of `α` at `e₁,P` and then applies `L₂`.
Functoriality identifies the result with the two paths below. The same calculation with
`E₁,E₂` exchanged gives the assertion for `G`; inversion gives inverse-comparison naturality.
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus). -/
theorem conjugation_comparison_naturality (E₁ : C₁ ≌ N₁) (E₂ : C₂ ≌ N₂)
    {F F' : N₁ ⥤ N₂} (α : F ⟶ F') :
    (E₁.invFunIdAssoc (F ⋙ E₂.inverse)).hom ≫ Functor.whiskerRight α E₂.inverse =
      Functor.whiskerLeft E₁.inverse
        (Functor.whiskerRight (Functor.whiskerLeft E₁.functor α) E₂.inverse) ≫
          (E₁.invFunIdAssoc (F' ⋙ E₂.inverse)).hom := by
  ext P
  simp only [NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map]
  rw [← E₂.inverse.map_comp, ← E₂.inverse.map_comp]
  simpa only [Functor.comp_obj, Functor.id_obj] using
    congrArg E₂.inverse.map (α.naturality (E₁.counit.app P))

/-- The compositor, with component `L₃(H(e₂,F(R₁ K)))`, is natural in both functors.
It is a natural isomorphism in `K` because it is the whiskering of `invFunIdAssoc`.
Source: blueprint reconstruction-trace-coherence proof, coherence; Stacks 0037 and 0DV0.
Proof: Step 7 applies `L₃ H` to `e₂` and its inverse. Functoriality proves the inverse
identities and naturality in `K`. These are precisely the existing whiskered natural iso.
Step 8 fixes `K`, puts `x = α_(R₁ K)`, and first uses naturality of `e₂` at `x`, then
naturality of `β` at `e₂,F'(R₁ K)`. Apply `L₃` to the resulting equality. The two sides
are the two paths in the displayed square; natural-transformation extensionality finishes.
Only category axioms and the given equivalence data enter, so empty categories are allowed.
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus). -/
theorem conjugation_compositor_naturality
    (E₁ : C₁ ≌ N₁) (E₂ : C₂ ≌ N₂) (E₃ : C₃ ≌ N₃)
    {F F' : N₁ ⥤ N₂} {H H' : N₂ ⥤ N₃} (α : F ⟶ F') (β : H ⟶ H') :
    (Functor.isoWhiskerLeft (E₁.functor ⋙ F) (E₂.invFunIdAssoc (H ⋙ E₃.inverse))).hom ≫
        Functor.whiskerRight (Functor.whiskerLeft E₁.functor (α ◫ β)) E₃.inverse =
      (Functor.whiskerRight (Functor.whiskerLeft E₁.functor α) E₂.inverse ◫
        Functor.whiskerRight (Functor.whiskerLeft E₂.functor β) E₃.inverse) ≫
          (Functor.isoWhiskerLeft (E₁.functor ⋙ F')
            (E₂.invFunIdAssoc (H' ⋙ E₃.inverse))).hom := by
  ext K
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Equivalence.invFunIdAssoc_hom_app, Functor.comp_map, NatTrans.hcomp_app,
    Functor.map_comp]
  simp only [← E₃.inverse.map_comp]
  congr 1
  have hβ := β.naturality (E₂.counit.app (F.obj (E₁.functor.obj K)))
  have he := E₂.counit.naturality (α.app (E₁.functor.obj K))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
    Functor.id_map] at hβ he ⊢
  rw [← Category.assoc, hβ, Category.assoc, ← H'.map_comp,
    Category.assoc, ← H'.map_comp, ← he]

end CategoryTheory.AdjointEquivalenceConjugation
