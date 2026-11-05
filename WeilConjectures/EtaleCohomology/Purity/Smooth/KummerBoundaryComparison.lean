/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator

/-!
# Kummer classes with coefficients and the classical Kummer boundary

For a sheaf `A` of `Λ`-modules on `X_ét` with a class `ι : ℤ_X ⟶ A` through which `A` corepresents
the global sections, `Extⁿ(A, N) ⟶ Hⁿ(X, N)` (apply the forgetful functor, precompose with `ι`)
is bijective on a quasi-compact quasi-separated scheme
(`AlgebraicGeometry.Etale.bijective_extToSheafHOf`). For `A = Λ ⊗ ℤ_X` and its unit class this
identifies the Kummer class `κ(u)` with coefficients in `Λ` with the image of the classical
Kummer boundary `δ(u) ∈ H¹(X, μₙ)` under `μₙ ⟶ μₙ ⊗ Λ`
(`AlgebraicGeometry.Etale.kummerClassOf_eq_extToSheafHOf_symm`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Comparison

variable {X : Scheme.{u}} {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  (ι : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (forget₂Sheaf Λ X).obj A)

/-- The comparison `Extⁿ(A, N) ⟶ Hⁿ(X, N)` along a class `ι ∈ H⁰(X, A)`: apply the exact
forgetful functor and precompose with `ι`. -/
noncomputable def extToSheafHOf (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Abelian.Ext.{u + 1} A N n →+ Sheaf.H ((forget₂Sheaf Λ X).obj N) n :=
  ((Abelian.Ext.mk₀ ι).precomp _ (zero_add n)).comp ((forget₂Sheaf Λ X).mapExtAddHom _ N n)

lemma extToSheafHOf_apply (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (x : Abelian.Ext.{u + 1} A N n) :
    extToSheafHOf Λ ι N n x =
      (Abelian.Ext.mk₀ ι).comp (x.mapExactFunctor (forget₂Sheaf Λ X)) (zero_add n) :=
  rfl

lemma extToSheafHOf_comp_mk₀ {N N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : N ⟶ N') (n : ℕ) (x : Abelian.Ext.{u + 1} A N n) :
    extToSheafHOf Λ ι N' n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((forget₂Sheaf Λ X).map g) n (extToSheafHOf Λ ι N n x) := by
  rw [extToSheafHOf_apply, extToSheafHOf_apply, Sheaf.H.map_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

lemma extToSheafHOf_comp_extClass
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (n : ℕ) (y : Abelian.Ext.{u + 1} A S.X₃ n) :
    extToSheafHOf Λ ι S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (extToSheafHOf Λ ι S.X₃ n y).comp (hS.map_of_exact (forget₂Sheaf Λ X)).extClass rfl := by
  rw [extToSheafHOf_apply, extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/-- On a quasi-compact quasi-separated scheme, `Extⁿ(A, N) ⟶ Hⁿ(X, N)` is bijective as soon as
`A` corepresents the sections over `X` through `ι`: both sides are universal δ-functors which
agree in degree zero. -/
theorem bijective_extToSheafHOf [CompactSpace X] [QuasiSeparatedSpace X]
    (hι : ∀ N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Function.Bijective (fun f : A ⟶ N ↦ ι ≫ (forget₂Sheaf Λ X).map f)) (n : ℕ)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (extToSheafHOf Λ ι N n) := by
  induction n generalizing N with
  | zero =>
    have hc : (extToSheafHOf Λ ι N 0) ∘ Abelian.Ext.mk₀ =
        Abelian.Ext.mk₀ ∘ (fun f : A ⟶ N ↦ ι ≫ (forget₂Sheaf Λ X).map f) := by
      funext f
      simp only [Function.comp_apply, extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_mk₀,
        Abelian.Ext.mk₀_comp_mk₀]
    refine (Function.Bijective.of_comp_iff _ (Abelian.Ext.mk₀_bijective _ _)).1 ?_
    rw [hc]
    exact (Abelian.Ext.mk₀_bijective _ _).comp (hι N)
  | succ n ih =>
    let I : InjectivePresentation N := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map (forget₂Sheaf Λ X)).ShortExact := hT.map_of_exact _
    have hI := subsingleton_H_forget₂_succ_of_injective Λ X I.J n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ T.g).postcomp _ (add_zero n)) (hT.extClass.postcomp _ rfl)
      ((Abelian.Ext.mk₀ ((forget₂Sheaf Λ X).map T.g)).postcomp _ (add_zero n))
      (hS.extClass.postcomp _ rfl)
      (extToSheafHOf Λ ι I.J n) (extToSheafHOf Λ ι T.X₃ n)
      (extToSheafHOf Λ ι N (n + 1))
      (AddMonoidHom.ext fun x ↦ (extToSheafHOf_comp_mk₀ Λ ι T.g n x).symm)
      (AddMonoidHom.ext fun y ↦ (extToSheafHOf_comp_extClass Λ ι hT n y).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hT n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      (ih I.J).2 (ih T.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hT x
        (Abelian.Ext.eq_zero_of_injective _) rfl)
      (fun y ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS y (@Subsingleton.elim _ hI _ _) rfl)

end Comparison

section Kummer

variable (X : Scheme.{u})

variable [HasInvertibleExponent Λ X] [NeZero (ringChar Λ)]

end Kummer

end AlgebraicGeometry.Etale
