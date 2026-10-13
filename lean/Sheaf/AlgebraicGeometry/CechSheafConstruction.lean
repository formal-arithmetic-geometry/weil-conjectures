/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.CechModuleSheafComparison
import Sheaf.AlgebraicGeometry.CechModuleSheafTerms
/-! # Construction of the augmented module-sheaf Čech complex

Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
(blueprint: lem-pc-cech-sheaf-construction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The augmented Čech complex and its sectionwise descriptions exist for every family
of opens, whether or not the family covers the scheme.
Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
(blueprint: lem-pc-cech-sheaf-construction)

Proof: for an open W, form the genuine module sheaf P(W) = j_W,*(F restricted to W).
Its sections on V are F(W intersection V), with O_X(V)-action through restriction.
For W contained in Z, restrict sections from Z intersection V to W intersection V.
These maps commute with restriction in V and respect O_X(V)-scalars; they give
P : X.Opens opposite -> X.Modules. Identity and composition follow from those of F.
Apply cechComplexFunctor U to P. Its degree-p object is the product of P applied to
the categorical products of the p+1 chosen opens. These categorical products are
canonically isomorphic to their intersections, giving the last family of isomorphisms.
The forgetful functor to presheaves of global modules preserves products: on each V,
restriction of scalars preserves products and module-sheaf products are computed on
sections. Apply these product comparison isomorphisms in every degree to obtain e.
Both face maps are restrictions on intersections, so e intertwines every coface and
hence their alternating sums, giving the differential identity. In degree zero take
the product of F -> P(U_i) restriction maps. Its composite with the first differential
is zero because the two restrictions to every double intersection agree. The universal
property of single_0 therefore gives epsilon. The product projection equations give
the displayed coordinate formula. No cover, finiteness or affine hypothesis enters
this construction. Empty families use empty products, including degree zero, and the
unique augmentation. All products and restrictions here are actual constructions;
this theorem asserts existence, and is not used to define an arbitrary witness. -/
theorem exists_augmented_cech_sheaf_complex
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) :
    ∃ (D : CochainComplex X.Modules ℕ)
      (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
      (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p),
      (∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1)) ∧
      (∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) ∧
      (∀ p : ℕ, Nonempty (D.X p ≅ ∏ᶜ fun y : Fin (p + 1) → ι =>
        (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj (F.restrict (⨅ l, U (y l)).ι))) := by
  obtain ⟨e, hd, ha⟩ := exists_cechModuleSheafComparison U F
  let ε := (CochainComplex.fromSingle₀Equiv (cechModuleSheafComplex U F) F).symm
    ⟨cechModuleSheafAugmentation₀ U F, cechModuleSheafAugmentation₀_comp_d U F⟩
  refine ⟨cechModuleSheafComplex U F, ε, e, hd, ?_,
    cechModuleSheafComplex_term_iso U F⟩
  intro y V
  have hε : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫
      ε.f 0 = cechModuleSheafAugmentation₀ U F := by
    dsimp [ε]
    rw [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    simp
  rw [hε]
  exact ha y V

end AlgebraicGeometry
