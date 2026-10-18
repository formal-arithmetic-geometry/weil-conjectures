/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.LinearAlgebra.FreeModule.Basic

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Sheaf.RingTheory.LimitModuleFinitePresentation
import Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness

/-!
# Generic freeness for finitely presented algebra-module pairs

Source: Stacks Project, Algebra, Tag 051S, Lemma generic-flatness-finitely-presented
(blueprint: lem-pur-fp-algebra-module-generic-freeness).
-/

@[expose] public section

universe u v w

namespace Module

open TensorProduct in
open scoped TensorProduct in
private theorem free_localized_baseChange
    {S R N L : Type*} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup N] [Module S N] [AddCommGroup L] [Module R L]
    (e : R ⊗[S] N ≃ₗ[R] L) (a : S)
    [Free (Localization.Away a) (LocalizedModule.Away a N)] :
    Free (Localization.Away (algebraMap S R a))
      (LocalizedModule.Away (algebraMap S R a) L) := by
  let T := Localization.Away (algebraMap S R a)
  let U := Localization.Away a
  have hu : IsUnit (algebraMap S T a) := by
    change IsUnit (algebraMap R T (algebraMap S R a))
    exact IsLocalization.Away.algebraMap_isUnit _
  let : Algebra U T := (IsLocalization.Away.lift a hu).toAlgebra
  have : IsScalarTower S U T := .of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq a hu x).symm
  let d := LocalizedModule.equivTensorProduct (Submonoid.powers a) N
  have : Free U (U ⊗[S] N) := .of_equiv d
  have : Free T (T ⊗[U] (U ⊗[S] N)) :=
    (TensorProduct.isBaseChange U (U ⊗[S] N) T).free
  have : Free T (T ⊗[S] N) :=
    .of_equiv (AlgebraTensorModule.cancelBaseChange S U T T N)
  let c := AlgebraTensorModule.cancelBaseChange S R T T N
  have : Free T (T ⊗[R] (R ⊗[S] N)) := .of_equiv c.symm
  have : Free T (T ⊗[R] L) := .of_equiv (e.baseChange R T _ _)
  exact .of_equiv
    (LocalizedModule.equivTensorProduct (Submonoid.powers (algebraMap S R a)) L).symm

open TensorProduct in
open scoped TensorProduct in
private theorem exists_free_away_of_noetherian_model
    {S R B N L : Type*} [CommRing S] [IsNoetherianRing S]
    [CommRing R] [IsDomain R] [Algebra S R]
    [CommRing B] [Algebra S B] [Algebra.FiniteType S B]
    [AddCommGroup N] [Module B N] [Module S N] [IsScalarTower S B N]
    [Module.Finite B N] [AddCommGroup L] [Module R L]
    (e : R ⊗[S] N ≃ₗ[R] L) :
    ∃ a : R, a ≠ 0 ∧ Free (Localization.Away a) (LocalizedModule.Away a L) := by
  let f := algebraMap S R
  let S₀ := f.range
  let : Algebra S S₀ := f.rangeRestrict.toAlgebra
  let : Algebra S₀ R := S₀.subtype.toAlgebra
  have : IsScalarTower S S₀ R := .of_algebraMap_eq' rfl
  have : IsNoetherianRing S₀ :=
    isNoetherianRing_of_surjective S S₀ f.rangeRestrict f.rangeRestrict_surjective
  let B₀ := S₀ ⊗[S] B
  let : Algebra B B₀ := Algebra.TensorProduct.rightAlgebra
  let N₀ := B₀ ⊗[B] N
  let c : N₀ ≃ₗ[S₀] S₀ ⊗[S] N :=
    Algebra.IsPushout.cancelBaseChange S S₀ B B₀ N
  have : Algebra.FiniteType S₀ B₀ := inferInstance
  have : Module.Finite B₀ N₀ := inferInstance
  obtain ⟨a, ha, hfree⟩ := noetherian_algebra_module_generic_freeness S₀ B₀ N₀
  let d : R ⊗[S₀] N₀ ≃ₗ[R] L :=
    (c.baseChange S₀ R _ _).trans
      ((AlgebraTensorModule.cancelBaseChange S S₀ R R N).trans e)
  let := hfree
  refine ⟨algebraMap S₀ R a, ?_, free_localized_baseChange d a⟩
  exact fun h ↦ ha (S₀.subtype_injective (by simpa using h))

open TensorProduct in
open scoped TensorProduct in
private theorem exists_free_away_same_universe
    (R A : Type u) (L : Type w)
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [AddCommGroup L] [Module A L]
    [Module R L] [IsScalarTower R A L] [Module.FinitePresentation A L] :
    ∃ a : R, a ≠ 0 ∧ Free (Localization.Away a) (LocalizedModule.Away a L) := by
  classical
  obtain ⟨I, hpo, hne, hdir, P, Q, η, π, κ, D, ν, hmod, hmodel⟩ :=
    Algebra.limitModuleFinitePresentation R A L
  let := hne
  let := hmod
  rcases hmodel with ⟨_, _, _, _, _, _, hPft, hQft, hDfin, _, _, _, _, hfinal⟩
  let i : I := Classical.arbitrary I
  let : Algebra (P.obj i) (Q.obj i) := (η.app i).hom.toAlgebra
  let : Algebra (P.obj i) R := (π.app i).hom.toAlgebra
  let : Module (P.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
  have : IsScalarTower (P.obj i) (Q.obj i) (D.obj i) :=
    IsScalarTower.of_compHom _ _ _
  have : Algebra.FiniteType ℤ (P.obj i) := hPft i
  have : IsNoetherianRing (P.obj i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Algebra.FiniteType (P.obj i) (Q.obj i) := hQft i
  have : Module.Finite (Q.obj i) (D.obj i) := hDfin i
  obtain ⟨e, _⟩ := hfinal i
  let eAdd : (R ⊗[P.obj i] D.obj i) ≃+ L := by
    letI : Module R L := Module.compHom L (algebraMap R A)
    exact e.toAddEquiv
  have he (r : R) (x : R ⊗[P.obj i] D.obj i) :
      eAdd (r • x) = algebraMap R A r • eAdd x := by
    let : Module R L := Module.compHom L (algebraMap R A)
    exact e.map_smul r x
  let e' : R ⊗[P.obj i] D.obj i ≃ₗ[R] L :=
    AddEquiv.toLinearEquiv eAdd fun r x ↦
      (he r x).trans (IsScalarTower.algebraMap_smul A r _)
  exact exists_free_away_of_noetherian_model (B := Q.obj i) e'

/-- A finitely presented module over a finitely presented algebra over a domain becomes
free over the localized base after inverting one nonzero base element. The basis need not
be finite, and the base need not be Noetherian.

Source: Stacks Project, Algebra, Tag 051S, Lemma generic-flatness-finitely-presented.
(blueprint: lem-pur-fp-algebra-module-generic-freeness)

Proof:
1. Shrink the finite-type R-algebra A to the universe of R, transporting its module action
   and finite presentation along the algebra equivalence. Apply finite-presentation
   approximation (Stacks Tag 00R1) to obtain a finite-type integer algebra S, a finite-type
   S-algebra B, a finite B-module N and R ⊗[S] N ≃ₗ[R] L. The ring S is Noetherian.
2. Replace S by the image S₀ of S → R. It is a Noetherian quotient of S and a domain
   because it is a subring of R. Put B₀ = S₀ ⊗[S] B and N₀ = B₀ ⊗[B] N. Base change
   preserves the two finiteness properties. Tensor cancellation identifies N₀ with
   S₀ ⊗[S] N, hence R ⊗[S₀] N₀ with L, without any flatness assumption.
3. Apply Noetherian generic freeness to S₀, B₀, N₀. Obtain nonzero a ∈ S₀ such that
   (N₀)ₐ is free over (S₀)ₐ. The image of a in R remains nonzero.
4. Put T = Rₐ and U = (S₀)ₐ. The localization universal property gives U → T.
   The localization-tensor equivalence and preservation of freeness under base change
   show that T ⊗[U] (U ⊗[S₀] N₀) is free. Tensor cancellation identifies it with
   T ⊗[S₀] N₀ and then with T ⊗[R] L, which is Lₐ.
Only finite support is needed for preservation of a basis, not finite rank. -/
theorem exists_free_away_of_finitePresentation
    (R : Type u) (A : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [AddCommGroup L] [Module A L]
    [Module R L] [IsScalarTower R A L] [Module.FinitePresentation A L] :
    ∃ a : R, a ≠ 0 ∧ Free (Localization.Away a) (LocalizedModule.Away a L) := by
  classical
  have : Small.{u} A := Algebra.FiniteType.small (R := R) (S := A)
  let A' := Shrink.{u} A
  let α : A' ≃ₐ[R] A := Shrink.algEquiv R A
  let : Algebra A' A := α.toRingHom.toAlgebra
  let : Module A' L := Module.compHom L α.toRingHom
  have : IsScalarTower A' A L := IsScalarTower.of_compHom _ _ _
  have : IsScalarTower R A' A := .of_algebraMap_eq fun r ↦ (α.commutes r).symm
  have : IsScalarTower R A' L := .of_algebraMap_smul fun r x ↦ by
    change α (algebraMap R A' r) • x = r • x
    rw [α.commutes, IsScalarTower.algebraMap_smul A]
  have : Algebra.FinitePresentation R A' := Algebra.FinitePresentation.equiv α.symm
  let d : A' ≃ₗ[A'] A :=
    { α.toAddEquiv with map_smul' := fun _ _ ↦ α.map_mul _ _ }
  have : Module.FinitePresentation A' A := Module.FinitePresentation.of_equiv d
  have : Module.FinitePresentation A' L := Module.FinitePresentation.trans A' L A
  exact exists_free_away_same_universe R A' L

end Module
