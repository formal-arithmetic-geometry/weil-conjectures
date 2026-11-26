/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Algebra.LimitFinitePresentation
import WeilConjectures.RingTheory.FinitePresentationModuleDiagram
import WeilConjectures.RingTheory.ModuleBaseChangeAcrossPushout

/-!
# Finite-presentation approximation of modules

A finitely presented algebra over a filtered colimit of rings, together with a finitely
presented module over it, is the colimit of finite-type algebras and finite modules over the
stages, compatibly with base change.

## Implementation details

The ring systems come from the algebra case (Stacks 00R0). The finitely many entries of a
presentation matrix of the module lift to one stage; on the cofinal tail above it, the stage
modules are the cokernels of the lifted matrices. Right exactness of the tensor product
identifies their base changes with the later cokernels and with the module, and a
directed-colimit criterion for base change gives the colimit assertion. The proof follows the
non-local version of the proof of Stacks 00QX.

## References

* [Stacks, Tags 00R1, 00R0, 00QX]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

private theorem tensorEquivOfPushout
    {A B C E : CommRingCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (k : B ⟶ E) (l : C ⟶ E) (h : CategoryTheory.IsPushout f g k l) :
    let := f.hom.toAlgebra
    let := g.hom.toAlgebra
    ∃ e : B ⊗[A] C ≃+* E,
      ∀ (x : B) (y : C), e (x ⊗ₜ[A] y) = k.hom x * l.hom y := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct A B C
  let e := (ht.isoIsPushout _ _ h).commRingCatIsoToRingEquiv
  refine ⟨e, fun x y ↦ ?_⟩
  have hx : e (x ⊗ₜ[A] (1 : C)) = k.hom x := by
    exact ConcreteCategory.congr_hom (ht.inl_isoIsPushout_hom _ _ h) x
  have hy : e ((1 : B) ⊗ₜ[A] y) = l.hom y := by
    exact ConcreteCategory.congr_hom (ht.inr_isoIsPushout_hom _ _ h) y
  rw [← hx, ← hy, ← map_mul]
  simp

/-- Simultaneous finite-type approximation of a finitely presented algebra and module.
The three colimits are colimit cocones over the directed set `Λ` (in `CommRingCat` and
`AddCommGrpCat`); scalar-extension maps are specified on pure tensors, and the module
tensors put the new scalar ring first (tensor symmetry matches the source).
-/
theorem limitModuleFinitePresentation
    (R S : Type u) (M : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : ∀ i : Λ, Module (B.obj i) (D.obj i)),
      -- (1) the three colimits, compatible with `R → S` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, Algebra.FiniteType ℤ (A.obj i)) ∧
      (∀ i, letI := (η.app i).hom.toAlgebra; Algebra.FiniteType (A.obj i) (B.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
      -- (3) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (η.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
          ∀ (x : B.obj i) (y : A.obj j),
            e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (4) base changes to the limit
      (∀ i,
        letI := (η.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] R ≃+* S,
          ∀ (x : B.obj i) (y : R),
            e (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * algebraMap R S y) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ e : S ⊗[B.obj i] D.obj i ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
        letI : Module R M := Module.compHom M (algebraMap R S)
        ∃ e : R ⊗[A.obj i] D.obj i ≃ₗ[R] M,
          ∀ (y : R) (x : D.obj i),
            e (y ⊗ₜ[A.obj i] x) =
              algebraMap R S y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) := by
  classical
  have hφ : RingHom.FinitePresentation (algebraMap R S) :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨I, hpo, hne, hdir, A, B, η, cR, cS, hR, hS, hcompat, hft,
      hAft, hpush, hfinal, hcolR, hcolS⟩ :=
    exists_limit_finite_presentation (algebraMap R S) hφ
  let := hne
  let := hdir
  rcases cR with ⟨r, π⟩
  rcases cS with ⟨s, κ⟩
  dsimp only at hR hS
  subst r
  subst s
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hcompat hfinal
  have hBft (i : I) : Algebra.FiniteType ℤ (B.obj i) := by
    let := (η.app i).hom.toAlgebra
    have : Algebra.FiniteType (A.obj i) (B.obj i) :=
      RingHom.finiteType_algebraMap.mp (hft i)
    have : Algebra.FiniteType ℤ (A.obj i) :=
      RingHom.finiteType_algebraMap.mp (hAft i)
    exact Algebra.FiniteType.trans (R := ℤ) (S := A.obj i) (A := B.obj i)
      inferInstance inferInstance
  obtain ⟨J, hpoJ, hneJ, hdirJ, F, hF, D, ν, hmod, hcolD, hsem,
      hν, hDft, hDtrans, hDfinal⟩ :=
    Module.exists_finitePresentation_module_diagram B S κ hcolS hBft M
  let := hneJ
  let := hdirJ
  let := hF
  let := hmod
  let π' := (Cocone.mk (CommRingCat.of R) π).whisker F
  let κ' := (Cocone.mk (CommRingCat.of S) κ).whisker F
  refine ⟨J, hpoJ, hneJ, hdirJ, F ⋙ A, F ⋙ B, Functor.whiskerLeft F η,
    π'.ι, κ'.ι, D, ν, hmod, ?_, ?_, hcolD, ?_, hsem, hν, ?_, ?_, hDft,
    ?_, hDtrans, ?_, hDfinal, ?_⟩
  · exact ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm hcolR.some⟩
  · exact ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm hcolS.some⟩
  · intro j
    exact hcompat (F.obj j) trivial trivial
  · intro j
    exact RingHom.finiteType_algebraMap.mp (hAft (F.obj j))
  · intro j
    let := ((Functor.whiskerLeft F η).app j).hom.toAlgebra
    exact RingHom.finiteType_algebraMap.mp (hft (F.obj j))
  · intro i j hij
    exact tensorEquivOfPushout (η.app (F.obj i)) (A.map (F.map (homOfLE hij)))
      (B.map (F.map (homOfLE hij))) (η.app (F.obj j))
      (hpush (F.obj i) (F.obj j) (leOfHom (F.map (homOfLE hij)))).some
  · intro j
    exact tensorEquivOfPushout (η.app (F.obj j)) (π.app (F.obj j))
      (κ.app (F.obj j)) (CommRingCat.ofHom (algebraMap R S))
      (hfinal (F.obj j) trivial trivial).some
  · intro j
    apply TensorProduct.moduleBaseChangeAcrossPushout
      (A.obj (F.obj j)) (B.obj (F.obj j)) R S (D.obj j) M
      (η.app (F.obj j)).hom (π.app (F.obj j)).hom (κ.app (F.obj j)).hom
      (ν.app j).hom
    · exact tensorEquivOfPushout (η.app (F.obj j)) (π.app (F.obj j))
        (κ.app (F.obj j)) (CommRingCat.ofHom (algebraMap R S))
        (hfinal (F.obj j) trivial trivial).some
    · exact hDfinal j

end Algebra
