/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
/-! # Local exactness of the augmented module-sheaf Čech complex

Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
(blueprint: lem-pc-cech-sheaf-local-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Any augmented complex with the usual Čech sections and restriction augmentation
is a quasi-isomorphism after restricting to one member of the family of opens.
Source: blueprint `lem-pc-cech-resolution`, proof paragraph 1 (insertion homotopy).
(blueprint: lem-pc-cech-sheaf-local-quasi-iso)

Proof: fix i and work on the open subscheme U_i. On an open V of U_i, the chosen
member U_i covers V entirely. For a degree-p section, the degree-(p-1) homotopy
has coordinate indexed by y equal to the coordinate indexed by the tuple with i
inserted first, using the identification V intersection U_i = V. In degree zero,
project to the coordinate i to obtain the homotopy to F. These maps are A-linear
and natural in V because all structure maps are restrictions. Forget to abelian sheaves
before transporting them through e; e need not respect the full O_X(V)-action. Compute d h + h d:
the coface deleting the inserted first index gives the identity; each other coface
pairs with the term obtained by first deleting its shifted index and then inserting
i, with opposite signs. Thus all remaining terms cancel. The augmentation equation
supplies the same identity at degree zero, and projection onto i followed by the
augmentation is the identity of F restricted to U_i. These equations give a chain
homotopy inverse of the restricted augmentation on underlying abelian sheaves. Thus
its abelian-sheaf homology maps are isomorphisms. Forgetting module sheaves to abelian
sheaves is exact and reflects isomorphisms: kernels are computed on sections and
cokernels are the associated sheaves of the sectionwise cokernels. It therefore
reflects quasi-isomorphisms, proving the module-sheaf assertion. This proof concerns
one member only and needs no covering hypothesis. If U_i is empty all terms and
homology objects are zero; if the index type is empty the parameter i has no values.
The zero module is covered by the same identities. It uses no assertion that boundary
stalks of open direct images vanish, and no assertion that stalks commute with infinite
products. -/
theorem augmented_cech_sheaf_quasiIso_restrict
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (hε : ∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) (i : ι) :
    QuasiIso (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε) := by sorry

end AlgebraicGeometry
