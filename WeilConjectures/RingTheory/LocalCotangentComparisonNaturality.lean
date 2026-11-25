/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Naturality of the residue H₁-to-conormal comparison

A local algebra map induces a scalar-extended map of conormal modules `m/m²`, compatible with
the canonical maps from residue-field `H₁`.

## Implementation details

The canonical `H₁`-to-conormal maps factor as presentation `H₁` maps followed by kernel
inclusions (`h1CotangentEquivCotangent_comp_map`); the two composite presentation morphisms
induce the same `H₁` map (`map_eq`), so the square commutes on pure tensors. No geometric
regularity or coordinate basis is required.

## References

* [Stacks, Tag 07E6]
* [Stacks, Tag 00S2]
-/

@[expose] public section

set_option autoImplicit false
universe u v w
open scoped TensorProduct
namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- A local algebra map induces the natural scalar-extended conormal comparison,
compatible with the canonical maps from residue-field H₁. -/
theorem exists_localCotangentComparison_naturality
    (k : Type u) (B : Type v) (A : Type w)
    [CommRing k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra B A] [Algebra k A] [IsScalarTower k B A]
    [IsLocalRing B] [IsLocalRing A] [IsLocalHom (algebraMap B A)] :
    let K₀ := IsLocalRing.ResidueField B
    let K := IsLocalRing.ResidueField A
    let P₀ := Extension.ofSurjective (Algebra.ofId B K₀) IsLocalRing.residue_surjective
    let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
    let c₀ := P₀.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k B K₀ K₀)
    let c := P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)
    ∃ μ : K ⊗[K₀] P₀.Cotangent →ₗ[K] P.Cotangent,
      (∀ (r : K) (x : P₀.ker),
        μ (r ⊗ₜ[K₀] Extension.Cotangent.mk x) =
        r • Extension.Cotangent.mk (P := P) ⟨algebraMap B A x.val, by
          change IsLocalRing.residue A (algebraMap B A x.val) = 0
          rw [← IsLocalRing.ResidueField.algebraMap_residue]
          have hx : IsLocalRing.residue B x.val = 0 := x.2
          rw [hx, map_zero]⟩) ∧
      μ.comp (c₀.baseChange K) =
        c.comp ((H1Cotangent.map k k K₀ K).liftBaseChange K) := by
  classical
  dsimp only
  let K₀ := IsLocalRing.ResidueField B
  let K := IsLocalRing.ResidueField A
  let P₀ := Extension.ofSurjective (Algebra.ofId B K₀) IsLocalRing.residue_surjective
  let P := Extension.ofSurjective (Algebra.ofId A K) IsLocalRing.residue_surjective
  let f : P₀.Hom P :=
    { toRingHom := algebraMap B A
      toRingHom_algebraMap := fun x ↦ by
        change algebraMap B A x = algebraMap B A x
        rfl
      algebraMap_toRingHom := fun x ↦ by
        change IsLocalRing.residue A (algebraMap B A x) =
          algebraMap K₀ K (IsLocalRing.residue B x)
        rw [IsLocalRing.ResidueField.algebraMap_residue] }
  let μ := (Extension.Cotangent.map f).liftBaseChange K
  refine ⟨μ, ?_, ?_⟩
  · intro r x
    change r • Extension.Cotangent.map f (Extension.Cotangent.mk x) = _
    rw [Extension.Cotangent.map_mk]
    rfl
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r h =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearMap.liftBaseChange_tmul, map_smul]
      let Q₀ := Extension.ofSurjective (IsScalarTower.toAlgHom k B K₀)
        IsLocalRing.residue_surjective
      let Q := Extension.ofSurjective (IsScalarTower.toAlgHom k A K)
        IsLocalRing.residue_surjective
      let g : Q₀.Hom Q :=
        { toRingHom := algebraMap B A
          toRingHom_algebraMap := fun x ↦ by
            change algebraMap B A (algebraMap k B x) = algebraMap k A x
            exact (IsScalarTower.algebraMap_apply k B A x).symm
          algebraMap_toRingHom := fun x ↦ by
            change IsLocalRing.residue A (algebraMap B A x) =
              algebraMap K₀ K (IsLocalRing.residue B x)
            rw [IsLocalRing.ResidueField.algebraMap_residue] }
      have e₀ := Q₀.h1CotangentEquivCotangent_comp_map
      have e := Q.h1CotangentEquivCotangent_comp_map
      have e₀' := LinearMap.congr_fun e₀ h
      have e' := LinearMap.congr_fun e ((H1Cotangent.map k k K₀ K) h)
      change r • Extension.Cotangent.map f
          (P₀.h1CotangentEquivCotangent ((H1Cotangent.map k B K₀ K₀) h)) = _
      have hp₀ : P₀.h1CotangentEquivCotangent ((H1Cotangent.map k B K₀ K₀) h) =
          Q₀.h1CotangentEquivCotangent ((H1Cotangent.map k B K₀ K₀) h) := by rfl
      rw [hp₀]
      rw [show Q₀.h1CotangentEquivCotangent ((H1Cotangent.map k B K₀ K₀) h) =
        Q₀.h1Cotangentι (Extension.H1Cotangent.map Q₀.defaultHom h) from e₀']
      change r • Extension.Cotangent.map g
        (Q₀.h1Cotangentι (Extension.H1Cotangent.map Q₀.defaultHom h)) = _
      have he : Extension.Cotangent.map g
          (Q₀.h1Cotangentι (Extension.H1Cotangent.map Q₀.defaultHom h)) =
          Q.h1Cotangentι (Extension.H1Cotangent.map g
            (Extension.H1Cotangent.map Q₀.defaultHom h)) := rfl
      rw [he, ← Extension.H1Cotangent.map_comp_apply]
      let t := (Generators.defaultHom (Generators.self k K₀)
        (Generators.self k K)).toExtensionHom
      have hm : Extension.H1Cotangent.map (g.comp Q₀.defaultHom) =
          Extension.H1Cotangent.map (Q.defaultHom.comp t) :=
        Extension.H1Cotangent.map_eq _ _
      rw [hm, Extension.H1Cotangent.map_comp_apply]
      change r • Q.h1Cotangentι (Extension.H1Cotangent.map Q.defaultHom
        ((H1Cotangent.map k k K₀ K) h)) = _
      have he' : Q.h1Cotangentι (Extension.H1Cotangent.map Q.defaultHom
          ((H1Cotangent.map k k K₀ K) h)) =
          P.h1CotangentEquivCotangent ((H1Cotangent.map k A K K)
            ((H1Cotangent.map k k K₀ K) h)) := e'.symm
      exact congrArg (r • ·) he'

end Algebra
