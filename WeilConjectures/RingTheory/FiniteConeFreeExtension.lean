/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.RingTheory.FiniteConeCycleAttachment

/-!
# One descending finite free extension

A bounded complex of finite free modules mapping to `C`, whose cone is acyclic in degrees `≥ n`
and has finitely generated cohomology in degree `n - 1`, extends by one finite free term in
degree `n - 1` so that the new cone is acyclic in degrees `≥ n - 1`.

## Implementation details

Lift finitely many generators of `H^(n-1)(mappingCone f)` to cycles `(a, c)` with
`a ∈ F^n` and `c ∈ C^(n-1)`, and adjoin a finite free module on them in degree `n - 1` with
differential `a` and map `-c` to `C`. The finite free carrier is built on `Shrink R` so that it
lives in the module universe. The bound `n ≤ b + 1` keeps the new term below `b`.

## References

* [Stacks, Tag 064U]
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Extend a bounded finite free approximation by one degree using generators of its
finite obstruction module. -/
theorem exists_finiteFree_cone_extension (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C F : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ C) (b n : ℤ)
    (hn : n ≤ b + 1) (hlow : F.IsStrictlyGE n) (hupp : F.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hvan : ∀ i : ℤ, n ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f))))
    (hfinite : Module.Finite R
      ((homologyFunctor (ModuleCat.{v} R) (n - 1)).obj
        (Q.obj (CochainComplex.mappingCone f)))) :
    ∃ (G : CochainComplex (ModuleCat.{v} R) ℤ) (g : G ⟶ C) (j : F ⟶ G),
      G.IsStrictlyGE (n - 1) ∧ G.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (G.X i) ∧ Module.Finite R (G.X i)) ∧
      (∀ i : ℤ, n - 1 ≤ i → IsZero
        ((homologyFunctor (ModuleCat.{v} R) i).obj
          (Q.obj (CochainComplex.mappingCone g)))) ∧
      j ≫ g = f ∧ (∀ i : ℤ, n ≤ i → IsIso (j.f i)) := by
  classical
  let D := CochainComplex.mappingCone f
  let eH : ((homologyFunctor (ModuleCat.{v} R) (n - 1)).obj (Q.obj D)) ≅
      D.homology (n - 1) := (homologyFunctorFactors (ModuleCat.{v} R) (n - 1)).app D
  have : Module.Finite R ((homologyFunctor (ModuleCat.{v} R) (n - 1)).obj (Q.obj D)) :=
    hfinite
  have : Module.Finite R (D.homology (n - 1)) := Module.Finite.equiv eH.toLinearEquiv
  obtain ⟨k, p, hp⟩ := Module.Finite.exists_fin' R (D.homology (n - 1))
  let P := ModuleCat.of R (Shrink.{v} (Fin k → R))
  let e := Shrink.linearEquiv.{v} R (Fin k → R)
  let π : P ⟶ D.homology (n - 1) := ModuleCat.ofHom (p.comp e.toLinearMap)
  have : Epi π := (ModuleCat.epi_iff_surjective π).2 (hp.comp e.surjective)
  let q : P ⟶ D.cycles (n - 1) := Projective.factorThru π (D.homologyπ (n - 1))
  have hq : Epi (q ≫ D.homologyπ (n - 1)) := by
    rw [Projective.factorThru_comp]
    infer_instance
  exact exists_finiteFree_cone_cycle_attachment R C F f b n hn hlow hupp hfree hvan P q hq

end DerivedCategory
