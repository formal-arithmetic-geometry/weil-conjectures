/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Scalar-compatible construction of the augmented Čech sheaf complex

Source: blueprint lem-pc-cech-resolution, displayed complex and proof paragraph 1;
Stacks Project, Tag 02FU, construction before the exactness argument.
(blueprint: lem-pc-linear-cech-sheaf-construction).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- A scalar-compatible augmented Čech complex exists for any family of opens.
Source: blueprint lem-pc-cech-resolution, displayed complex and proof paragraph 1;
Stacks Project, Tag 02FU, construction before the exactness argument.
(blueprint: lem-pc-linear-cech-sheaf-construction)

Proof: For each open W use the module sheaf obtained by pushing F.over W along
Over.star W, with ring morphism given by restriction along prod.snd. Its sections
on B are F(W product B), and its O_X(B)-action is restriction along prod.snd.
For W contained in Z, restriction along W product B -> Z product B is O_X(B)-linear
by functoriality of the structure-sheaf restrictions. These restrictions are natural
in B and give a functor P on opposite opens. Apply cechComplexFunctor U to P.
The forgetful functor to presheaves of global modules preserves products, since
products of module sheaves are computed on sections and restriction of scalars
preserves products. The resulting product comparisons give e. The comparison
commutes with each face restriction, hence its signed sum and the differentials.
In degree zero, the product of restrictions F -> P(U_i) has zero composite with
the differential: both restrictions to every double intersection agree. It gives
the augmentation from single_0. Its projections give the augmentation equation.
Identify each categorical product of opens with the infimum of the opens and use
the equivalence between sheaves on Over W and on the open subscheme W to obtain
the term isomorphisms with open direct images. Finally every coordinate of e is
precisely a module-sheaf product projection followed by the section identification
of P(W); the former is O_X(B)-linear and the latter restricts scalars along prod.snd.
This gives the displayed scalar formula. No covering, affine, nonempty, or finite
hypothesis is used. Empty families use empty products, and the restriction maps
and all displayed equations are still defined. The assertion only constructs the
augmented complex; it asserts no local or global exactness. -/
theorem exists_augmented_linear_cech_sheaf_complex
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
        (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj (F.restrict (⨅ l, U (y l)).ι))) ∧
      (∀ (p : ℕ) (y : Fin (p + 1) → ι) (B : X.Opens),
        let c : Γ(D.X p, B) → Γ(F, (∏ᶜ fun l ↦ U (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ι ↦
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ U (y l)))) y).app (op B) s
        ∀ (a : Γ(X, B)) (s : Γ(D.X p, B)),
          c (a • s) = X.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ U (y l)) ⨯ B ⟶ B).op a • c s) := by sorry

end AlgebraicGeometry
