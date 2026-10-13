/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.CechSheafConstruction
import Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso

/-! # Čech sheaf resolution with local scalar compatibility

Source: blueprint lem-pc-cech-resolution, displayed complex and proof paragraph 1;
Stacks Project, Tags 01EO and 01FJ.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- The section identifications of the Čech resolution respect scalars on every open.
This refines the global-ring-linear presheaf description without changing its complex,
differential, augmentation, or termwise open-direct-image description.
Source: blueprint lem-pc-cech-resolution, displayed complex and proof paragraph 1;
Stacks Project, Tags 01EO and 01FJ.
(blueprint: lem-pc-linear-cech-sheaf-resolution).

Proof: Construct P(Z) = j_Z,*(F|Z) as an actual module sheaf on X, with sections
on B equal to F(Z intersect B), and scalar action through O_X(B) -> O_X(Z intersect B).
Restrictions in Z define P on opposite opens. Apply the usual Čech complex functor
and augment by the restrictions of F. The product projections identify each term,
its signed differential, and its augmentation with the stated presheaf descriptions,
as in exists_cech_sheaf_resolution. These projections are morphisms of module sheaves:
in the y coordinate on B, multiplication by a is multiplication by the restriction
of a along the second product projection. This proves precisely the extra scalar
formula, including on nonaffine B. The term isomorphisms are those induced by the
identification of categorical products of opens with intersections. On each cover
member insertion of its index contracts the augmented complex; hence its augmentation
is locally a quasi-isomorphism and therefore a quasi-isomorphism on X. Empty covers
force X empty and give zero terms. No witness is used to define data; the witnesses
are consumed only inside proofs. The additional scalar formula cannot be inferred
from an arbitrary global-ring-linear presheaf isomorphism alone. -/
theorem exists_linear_cech_sheaf_resolution
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
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
            (∏ᶜ fun l ↦ U (y l)) ⨯ B ⟶ B).op a • c s) ∧
      QuasiIso ε := by sorry

end AlgebraicGeometry
