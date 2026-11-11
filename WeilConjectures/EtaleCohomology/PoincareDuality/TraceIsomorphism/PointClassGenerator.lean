/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism

/-!
# The class of a point generates the top cohomology

Let `k` be an algebraically closed field, `Λ` a self-injective finite coefficient ring whose
exponent is invertible in `k`, and `a : X ⟶ Spec k` smooth, proper and geometrically connected
of pure relative dimension `d`. For a `k`-point `x` of `X`, the class
`[x ⊂ X] ∈ H^{2d}(X, Λ(d)) = H^{2d}_c(X, Λ(d))` (`AlgebraicGeometry.Etale.pointClass`) generates
`H^{2d}(X, Λ(d))` over `Λ = End(Λ_k)`: the map `Λ ⟶ H^{2d}(X, Λ(d))`, `λ ↦ λ · [x]`, is
bijective (`AlgebraicGeometry.Etale.bijective_comp_pointClass`).

The proof is that of the blueprint: for the normalized orientation the trace sends `[x]` to `1`
(`AlgebraicGeometry.Etale.exists_tateOrientation_traceMap_pointClass`), so `λ ↦ λ · [x]` is a
section of the trace, which is bijective
(`AlgebraicGeometry.Etale.TateOrientation.bijective_traceMap`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a] [GeometricallyConnected a]
  [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]

/-- Blueprint `lemma-class-of-point--2`: the class `[x ⊂ X]` of a `k`-point `x` generates
`H^{2d}(X, Λ(d)) = H^{2d}_c(X, Λ(d))` over `Λ = End(Λ_k)`, in the strong sense that
`End(Λ_k) ⟶ H^{2d}_c(X, Λ(d))`, `λ ↦ λ · [x]`, is bijective. For the normalized orientation the
trace map sends `[x]` to `1`, so `λ ↦ λ · [x]` is a section of the trace, which is bijective. -/
theorem bijective_comp_pointClass [Module.Injective Λ Λ] (x : Spec (.of k) ⟶ X)
    [IsRegularImmersion d x] (hx : x ≫ a = 𝟙 _) :
    Function.Bijective (fun f : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _ ↦
      f ≫ pointClass (Λ := Λ) (d := d) a x) := by
  obtain ⟨γ, hγ⟩ := exists_tateOrientation_traceMap_pointClass (Λ := Λ) (d := d) a
  have ht (f : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ 𝟙_ _) :
      γ.traceMap (f ≫ pointClass a x) = f := by
    change (f ≫ pointClass a x) ≫ _ = f
    rw [Category.assoc]
    change f ≫ γ.traceMap (pointClass a x) = f
    rw [hγ x hx, Category.comp_id]
  refine ⟨Function.LeftInverse.injective ht, fun c ↦ ⟨γ.traceMap c, ?_⟩⟩
  exact (TateOrientation.bijective_traceMap a γ).1 (ht _)

end Etale

end AlgebraicGeometry
