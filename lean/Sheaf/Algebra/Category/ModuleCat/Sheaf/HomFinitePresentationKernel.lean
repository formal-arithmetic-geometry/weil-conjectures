/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Sites.Spaces
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Internal Hom and a finite free presentation

Source: Stacks Project, Modules, Lemma 01CO (1), and the proofs of Lemmas 01CQ and 0GMV
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-kernel).

## Main statements

* `SheafOfModules.homObj_precomposition_exact`: internal Hom is left exact in its first argument.
* `SheafOfModules.homObj_finitePresentation_kernel`: the coordinate form for a finite presentation.

Finite sums are represented by finite products, whose evaluations are the componentwise
modules of tuples. Their projections specify both coordinate formulas without choosing
an additional model of the internal Hom or the finite sum.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped ZeroObject

namespace SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with a right exact sequence gives a left exact internal Hom sequence.
Source: Stacks Project, Modules, Lemma 01CO (1)
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-kernel).

Proof: Install the existing symmetric monoidal closed structure on module sheaves.
The contravariant internal Hom functor preserves limits by Mathlib's parametrized
adjunction theorem. Its comparison with `homFunctor R` is componentwise the identity;
`SheafOfModules.pre_app` verifies naturality. The last short complex of the hypothesis
makes `b` epi, and the first short complex is exact. Take the opposite of the latter
complex, whose first map is now mono, and apply the kernel-preserving internal Hom
functor. This gives the exact pair of precomposition maps. Its first map is mono
because it remains a kernel inclusion. Adjoin the initial zero and combine the two
short exactness assertions using `ComposableArrows.exact_of_δ₀`.
-/
theorem homObj_precomposition_exact
    {E₂ E₁ E : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)}
    (a : E₂ ⟶ E₁) (b : E₁ ⟶ E)
    (h : (ComposableArrows.mk₃ a b
      (0 : E ⟶ (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)))).Exact)
    (M : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (ComposableArrows.mk₃
      (0 : (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) ⟶ homObj (R := R) E M)
      (homObjMap (R := R) b (𝟙 M)) (homObjMap (R := R) a (𝟙 M))).Exact := by
  let := monoidalCategory (R := R)
  let := symmetricCategory (R := R)
  let := monoidalClosed (R := R)
  let F := (homFunctor R).flip.obj M
  let G := MonoidalClosed.internalHom.flip.obj M
  let e : G ≅ F := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by
      change (MonoidalClosed.pre f.unop).app M ≫ 𝟙 _ =
        𝟙 _ ≫ homObjMap (R := R) f.unop (𝟙 M)
      simpa only [Category.comp_id, Category.id_comp] using (pre_app (R := R) f.unop M))
  have : PreservesLimitsOfShape WalkingParallelPair F :=
    preservesLimitsOfShape_of_natIso e
  have leftExact {C : Type (u + 1)} [Category.{u} C] [Abelian C]
      (F : Cᵒᵖ ⥤ C) [F.PreservesZeroMorphisms]
      [PreservesLimitsOfShape WalkingParallelPair F]
      {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
      (h : (ComposableArrows.mk₃ a b (0 : D ⟶ (0 : C))).Exact) :
      (ComposableArrows.mk₃ (0 : (0 : C) ⟶ F.obj (op D))
        (F.map b.op) (F.map a.op)).Exact := by
    have : Epi b := (h.exact 1).epi_f rfl
    have hab : a ≫ b = 0 := h.toIsComplex.zero 0
    let S := ShortComplex.mk a b hab
    have hs : S.Exact := h.exact 0
    have : Mono S.op.f := by
      change Mono b.op
      infer_instance
    have hm := hs.op.map_of_mono_of_preservesKernel F inferInstance inferInstance
    have hk := KernelFork.mapIsLimit _ hs.op.fIsKernel F
    have : Mono (F.map b.op) := Fork.IsLimit.mono hk
    apply ComposableArrows.exact_of_δ₀
    · apply ComposableArrows.exact₂_mk _ (by simp)
      apply (ShortComplex.exact_iff_mono _ rfl).2
      change Mono (F.map b.op)
      infer_instance
    · exact hm.exact_toComposableArrows
  exact leftExact F a b h

/-- The coordinate kernel sequence attached to a finite free presentation.
Source: Stacks Project, Modules, proofs of Lemmas 01CQ and 0GMV, using Lemma 01CO (1)
(blueprint: lem-weil-pbc-sheaf-hom-finite-presentation-kernel).

The coefficient `c i k` is the coefficient of the `i`-th basis section in `a(e_k)`.
The projection of `β` is evaluation at `b(e_i)` on every open, and the `k`-th projection
of `α` is the sum of the restricted coefficients times the input coordinates.

Proof (steps 5--7 of the node, following steps 1--4 above):
5. By def-weil-pbc-module-finite-type-presentation, maps from the finite free module
   are uniquely determined by the images of its basis sections. On each open this gives
   a linear bijection `Hom(O^n,M) ≃ M^n`. These bijections commute with restriction,
   hence give isomorphisms of module sheaves (def-pur-sheaf-hom).
6. In these coordinates precomposition with `a` sends `(x_i)` to
   `(∑ i, c i k |_U • x_i)_k`, by linearity and the coefficient identity. Precomposition
   with `b` sends `ψ` to `(ψ_U(b_U(e_i|_U)))_i`. Thus both formulas define module maps.
7. Apply `homObj_precomposition_exact` to the presentation and transport its
   categorical exactness along the coordinate isomorphisms of step 5, using
   `ComposableArrows.exact_of_iso`. This includes the initial zero and requires
   no further local-lifting argument.
-/
theorem homObj_finitePresentation_kernel (m n : ℕ)
    (H : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (a : free (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
        (ULift.{u} (Fin m)) ⟶ free (ULift.{u} (Fin n)))
    (b : free (ULift.{u} (Fin n)) ⟶ H)
    (h : (ComposableArrows.mk₃ a b
      (0 : H ⟶ (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)))).Exact)
    (c : Fin n → Fin m → R.obj.obj (op (⊤ : Opens X)))
    (hc : ∀ k : Fin m,
      (a.val.app (op (⊤ : Opens X))).hom
          ((freeSection (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
            (ULift.up k)).eval (op ⊤)) =
        ∑ i : Fin n, c i k •
          ((freeSection (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
            (ULift.up i)).eval (op ⊤)))
    (M : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    ∃ (β : homObj (R := R) H M ⟶ ∏ᶜ (fun _ : Fin n => M))
      (α : (∏ᶜ (fun _ : Fin n => M)) ⟶ ∏ᶜ (fun _ : Fin m => M)),
      (∀ (U : Opens X) (ψ : (homObj (R := R) H M).val.obj (op U)) (i : Fin n),
        ((β ≫ Pi.π (fun _ : Fin n => M) i).val.app (op U)).hom ψ =
          (ψ.app (op (Over.mk (𝟙 U)))).hom
            ((b.val.app (op U)).hom
              ((freeSection
                (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
                (ULift.up i)).eval (op U)))) ∧
      (∀ (U : Opens X) (x : (∏ᶜ (fun _ : Fin n => M)).val.obj (op U)) (k : Fin m),
        ((α ≫ Pi.π (fun _ : Fin m => M) k).val.app (op U)).hom x =
          ∑ i : Fin n, R.obj.map (homOfLE (le_top : U ≤ ⊤)).op (c i k) •
            ((Pi.π (fun _ : Fin n => M) i).val.app (op U)).hom x) ∧
      (ComposableArrows.mk₃ (0 : (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) ⟶ homObj (R := R) H M)
        β α).Exact := by
  sorry

end SheafOfModules
