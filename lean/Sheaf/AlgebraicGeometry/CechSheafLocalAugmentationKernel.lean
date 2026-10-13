/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
/-! # The degree-zero kernel of a locally restricted Cech augmentation

Source: blueprint `lem-pc-cech-resolution`, proof paragraph 1.
(blueprint: lem-pc-cech-local-augmentation-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The restricted augmentation is the kernel of the first differential.
Source: blueprint `lem-pc-cech-resolution`, proof paragraph 1.
(blueprint: lem-pc-cech-local-augmentation-kernel)

Proof: On an open V contained in U_i, identify the singleton i coordinate with F(V).
Project a zero cocycle to that coordinate. The pair (i,j) coordinate of d^0 says that
its j coordinate is the restriction of this section. Thus every zero cocycle is
uniquely the restriction augmentation of a section of F(V). The specified augmentation
formula identifies this map with the given augmentation, and hd in degree zero identifies
zero cocycles through e. All these bijections commute with restriction. Their inverses
are linear over the local structure ring: the augmentation is a module-sheaf morphism,
and an inverse to a bijective linear map is linear. Consequently they define a kernel
universal property in module sheaves on U_i. The single-complex degree-zero object is
canonically F restricted to U_i. On the empty open all sections are zero, so the same
argument applies. Neither a covering hypothesis nor any positive-degree exactness is
used. -/
theorem augmented_cech_sheaf_restrict_kernel
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
    Nonempty (IsLimit (KernelFork.ofι
      ((((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε).f 0)
      (show (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε).f 0 ≫
          (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).d 0 1 = 0 by
        rw [HomologicalComplex.Hom.comm]
        simp))) := by sorry

end AlgebraicGeometry
