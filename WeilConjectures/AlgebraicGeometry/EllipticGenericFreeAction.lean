/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.EllipticTateGaloisData
import WeilConjectures.AlgebraicGeometry.EllipticMultiplicationTowerStabilizer
import WeilConjectures.SixFunctors.PadicCharacterFreeSubgroup
import WeilConjectures.SixFunctors.TateModuleLinearTopology
import WeilConjectures.AlgebraicGeometry.GenericPointSepWeaklyContractible

/-!
# The elliptic generic-point free action

This file proves the elliptic-curve generic-point construction used in the
full cohomological-dimension counterexample.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`,
counterexample paragraph; Stacks 0BFH, 0BFG and 098F.
(blueprint: lem-sf-elliptic-generic-free-action)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The geometric generic point composed with the structure morphism to the ground field.

Source: the counterexample paragraph of
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-elliptic-generic-free-action) -/
noncomputable def ellipticGenericOver {k : Type u} [Field k]
    (E : Over (Spec (.of k))) [IsAbelianVariety E] : Over (Spec (.of k)) :=
  (Over.map E.hom).obj ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))

/-- The inverse-limit topology on the existing Tate module, induced by its coordinates in
its discrete group of geometric points. The torsion-coordinate subgroups are finite and
carry their discrete topology, as in the profinite inverse limit.

Source: the Tate quotient in the counterexample paragraph of
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-elliptic-generic-free-action) -/
noncomputable instance ellipticTateTopology {k : Type u} [Field k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (r : ℕ) [Fact r.Prime] : TopologicalSpace (IsAbelianVariety.tateModule r E) :=
  TopologicalSpace.induced
    (fun t : IsAbelianVariety.tateModule r E ↦
      (t : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E)))
    (@Pi.topologicalSpace ℕ (fun _ ↦ Additive (Scheme.specAlgebraicClosure k ⟶ E))
      (fun _ ↦ ⊥))

/-- Blueprint `lem-sf-elliptic-generic-free-action`.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`,
counterexample paragraph.  The statement includes the generic-point sieve property, the
surjective character from the multiplication-by-`r` tower, the rank-two Tate-module
identification, and the countable free subgroup whose action on every affine weakly
contractible object is free.  Its proof follows the six source steps: generic-point
weak contractibility; finite multiplication covers and their torsor fibres; the compatible
finite-level Galois characters; compactness and the Tate-rank identification; the free
subgroup in the pro-`r` factor; and the lifting argument for the free action.

Proof plan:
1. The function-field generic point and its separable closure are weakly etale. Covering
   sieves contain the identity. A sheaf epimorphism onto its representable is locally
   surjective, and the identity therefore lifts; this proves weak contractibility.
2. Multiplication by `r ^ m` is finite etale surjective of degree `r ^ (2 * m)`. The source
   is integral, so its generic fibre is a field: localize an affine domain at the nonzero
   elements of the base and use its finite dimension. Translation by the rational torsion
   points acts simply transitively on the separable generic fibre.
3. The absolute Galois action on each finite fibre is transitive and continuous. Choose
   compatible points `x m`, using surjectivity of multiplication on torsion and the inverse
   limit of nonempty finite sets. The identity `σ(x m) = x m + ρ_m(σ)` defines continuous
   surjective homomorphisms, compatible with multiplication by `r`.
4. The compatible characters define `ρ`. Each prescribed compatible fibre is a nested
   family of nonempty closed subsets of the compact Galois group, hence has a point.
   Thus `ρ` is surjective. Tate rank gives the topological rank-two identification `e`;
   its first coordinate defines the continuous surjection `χ`.
5. Choose `g` above `1`. The pro-`r` factor of the closure of its integral powers maps
   isomorphically onto the `r`-adic integers; `j` is its inverse followed by inclusion.
   Countably many independent `r`-adic integers give the homomorphism `φ` with injective
   composite `χ ∘ φ`. Its range is the required abstract countable free subgroup.
6. Pull a multiplication cover back to an affine weakly contractible `W`. Its map of
   representable sheaves is an epimorphism, hence splits. A map from the generic point to
   `W` consequently lifts to each multiplication cover. An element fixing that map fixes
   these lifts, so all its finite characters vanish. Thus its `χ` value vanishes and
   injectivity of `χ ∘ φ` forces the element to be the identity.
(blueprint: lem-sf-elliptic-generic-free-action)
-/
theorem ellipticGenericFreeAction
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (hDim : IsAbelianVariety.dim E = 1)
    (r : ℕ) [Fact r.Prime] (hrp : r ≠ p) :
    IsAffine (Scheme.ProEt.genericPointSep E.left).left ∧
      (Scheme.ProEt.topology E.left).IsWeaklyContractible.{u + 1}
        (Scheme.ProEt.genericPointSep E.left) ∧
      (∀ (S : Sieve (Scheme.ProEt.genericPointSep E.left)),
        S ∈ Scheme.ProEt.topology E.left (Scheme.ProEt.genericPointSep E.left) →
          S (𝟙 _)) ∧
      (∀ m : ℕ, IsFinite (𝟙 E ^ (r ^ m)).left ∧
        Etale (𝟙 E ^ (r ^ m)).left ∧ Surjective (𝟙 E ^ (r ^ m)).left) ∧
      (∃ (ρ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
          SeparableClosure E.left.functionField) →*
            Multiplicative (IsAbelianVariety.tateModule r E))
        (e : IsAbelianVariety.tateModule r E ≃ₗ[ℤ_[r]] (Fin 2 → ℤ_[r]))
        (χ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
          SeparableClosure E.left.functionField) →ₜ* Multiplicative ℤ_[r]),
        Continuous ρ ∧ Function.Surjective ρ ∧ Continuous e ∧ Continuous e.symm ∧
          (∀ σ, χ σ = Multiplicative.ofAdd (e (ρ σ).toAdd 0)) ∧
          Function.Surjective χ ∧
          (∃ x : ℕ → (ellipticGenericOver E ⟶ E),
            (∀ m, x m ≫ (𝟙 E ^ (r ^ m)) =
              Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl) ∧
            (∀ m, x (m + 1) ≫ (𝟙 E ^ r) = x m) ∧
            ∀ σ m,
              ((Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
                (Scheme.ProEt.genericPointSepAut E.left σ))) ≫ x m =
                x m * (toUnit (ellipticGenericOver E) ≫
                  inv (toUnit (Scheme.specAlgebraicClosure k)) ≫
                  (((ρ σ).toAdd : ℕ → Additive (Scheme.specAlgebraicClosure k ⟶ E))
                    m).toMul)) ∧
          ∃ g : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
            SeparableClosure E.left.functionField), χ g = Multiplicative.ofAdd 1 ∧
          ∃ (j : Multiplicative ℤ_[r] →ₜ*
              (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
                SeparableClosure E.left.functionField))
            (φ : Multiplicative (ULift.{u + 1} ℕ →₀ ℤ) →*
              (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
                SeparableClosure E.left.functionField)),
            (∀ z, j z ∈ (Subgroup.zpowers g).topologicalClosure) ∧
              (∀ z, χ (j z) = z) ∧
              (∀ h, φ h ∈ Set.range j) ∧
              Function.Injective (χ.toMonoidHom.comp φ) ∧
              (∀ (W : E.left.ProEt),
                IsAffine W.left →
                  (Scheme.ProEt.topology E.left).IsWeaklyContractible.{u + 1} W →
                  ∀ (h : Multiplicative (ULift.{u + 1} ℕ →₀ ℤ))
                    (t : Scheme.ProEt.genericPointSep E.left ⟶ W),
                    (Scheme.ProEt.genericPointSepAction E.left φ h).unop ≫ t = t → h = 1)) := by
  classical
  have hcovers : ∀ m : ℕ, IsFinite (𝟙 E ^ (r ^ m)).left ∧
      Etale (𝟙 E ^ (r ^ m)).left ∧ Surjective (𝟙 E ^ (r ^ m)).left := by
    intro m
    have hm : 0 < r ^ m := pow_pos (Fact.out : Nat.Prime r).pos _
    have hnp : ¬ p ∣ r ^ m := by
      intro h
      rcases CharP.char_is_prime_or_zero k p with hp' | hp'
      · have hpr : p ∣ r := hp'.dvd_of_dvd_pow h
        exact hrp ((Nat.prime_dvd_prime_iff_eq hp' (Fact.out : Nat.Prime r)).mp hpr).symm
      · subst p
        rcases h with ⟨c, hc⟩
        simp at hc
        omega
    exact ⟨isFinite_npow_id E (r ^ m) hm, etale_npow_id p E (r ^ m) hm hnp,
      surjective_npow_id E (r ^ m) hm⟩
  refine ⟨?_, ?_, ?_, hcovers, ?_⟩
  · rw [Scheme.ProEt.genericPointSep_left]
    infer_instance
  · exact genericPointSepWeaklyContractible
  · intro S hS
    exact Scheme.ProEt.id_mem_genericPointSep E.left hS
  · obtain ⟨ρ, hρ, hρsurj, x, hx0, hx1, hx2⟩ :=
      ellipticTateGaloisData k p hp E hDim r hrp
    have hne : Nonempty
        (IsAbelianVariety.tateModule r E ≃ₗ[ℤ_[r]] (Fin 2 → ℤ_[r])) := by
      have hn := IsAbelianVariety.nonempty_linearEquiv_tateModule r E p hrp
      rw [hDim, Nat.mul_one] at hn
      exact hn
    let e := Classical.choice hne
    obtain ⟨he, hei⟩ := tateModuleLinearTopology r
      (Additive (Scheme.specAlgebraicClosure k ⟶ E)) 2 e
    let : TopologicalSpace
        (AddCommGroup.tateModule r (Additive (Scheme.specAlgebraicClosure k ⟶ E))) :=
      ellipticTateTopology E r
    let c : IsAbelianVariety.tateModule r E →ₗ[ℤ_[r]] ℤ_[r] :=
      (LinearMap.proj 0).comp e.toLinearMap
    let χ : (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
        SeparableClosure E.left.functionField) →ₜ* Multiplicative ℤ_[r] :=
      ⟨c.toAddMonoidHom.toMultiplicative.comp ρ,
        continuous_ofAdd.comp ((continuous_apply 0).comp
          (he.comp (continuous_toAdd.comp hρ)))⟩
    have hχ (σ) : χ σ = Multiplicative.ofAdd (e (ρ σ).toAdd 0) := rfl
    have hχsurj : Function.Surjective χ := by
      intro z
      obtain ⟨σ, hσ⟩ := hρsurj (Multiplicative.ofAdd (e.symm (fun _ ↦ z.toAdd)))
      refine ⟨σ, ?_⟩
      rw [hχ, hσ]
      simp
    obtain ⟨g, hg⟩ := hχsurj (Multiplicative.ofAdd 1)
    obtain ⟨j, φ, hj0, hj1, hj2, hj3⟩ := padicCharacterFreeSubgroup r χ g hg
    refine ⟨ρ, e, χ, hρ, hρsurj, he, hei, hχ, hχsurj, ⟨x, hx0, hx1, hx2⟩,
      g, hg, j, φ, hj0, hj1, hj2, hj3, ?_⟩
    intro W hWa hW h t ht
    have hρh : ρ (φ h) = 1 :=
      ellipticMultiplicationTowerStabilizer k E r hcovers ρ x hx0 hx2 W hWa hW
        (φ h) t ht
    apply hj3
    change χ (φ h) = χ (φ 1)
    rw [map_one, map_one, hχ, hρh]
    change Multiplicative.ofAdd (e 0 0) = 1
    simp

end AlgebraicGeometry
