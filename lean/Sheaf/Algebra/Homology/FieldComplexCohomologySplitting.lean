/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Projection
public import Sheaf.Paper.PointFdComplexes
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-! # Cohomology models and retracts over a field

Source: Weil conjectures blueprint, main-20261015, sec-trace-formula,
sk-thm-trace-transport, first sentence of prop-trf-karoubi-independence.proof.md;
Stacks Project Tags 09FN, 09FP, 05CF and 05RU
(blueprint: lem-trf-field-complex-cohomology-splitting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Complexes over a field have cohomology models, and finite cohomology models have
compatible image/kernel retracts.
Source: main-20261015, prop-trf-karoubi-independence.proof.md, first sentence;
Stacks Project Tags 09FN, 09FP, 05CF and 05RU
(blueprint: lem-trf-field-complex-cohomology-splitting).

Proof:
1. By vector-space projectivity (lem-weil-pbc-vector-space-projective), the maps
   from cycles onto cohomology and from terms onto boundaries have sections.
   Their images give complements V to boundaries in cycles and T to cycles in terms.
   The differential identifies T in degree n with boundaries in degree n+1.
2. For any such complements, include the chosen cohomology representatives V and
   project onto their cohomology classes. These are chain maps a and b with ba=1.
   Define h in degree n by the inverse differential on boundaries and zero on V+T.
   Then dh+hd=1-ab, giving the homotopy equivalence and the stated normalization.
3. Homotopic maps act equally on cohomology. The contractions show that any chain
   map f is homotopic to a_Q (b_Q f a_P) b_P: a homotopy is h_Q f+a_Q b_Q f h_P.
   Thus two maps with equal cohomology maps are homotopic.
4. For a quasi-isomorphism f, invert its degreewise cohomology maps and conjugate
   this inverse family by a and b. Step 3 makes the resulting map a homotopy inverse.
5. Quasi-isomorphisms are therefore already invertible in the homotopy category.
   The localization universal property (def-weil-abstract-derived-category) factors
   its identity through D(F). Applying that property again to natural transformations
   gives inverse equivalences between the homotopy category and D(F).
6. Maps between zero-differential complexes are arbitrary degreewise maps, and a
   homotopy between them forces equality. Steps 2 and 5 therefore give a bijection
   on Hom sets. The normalization in Step 2 identifies it with the canonical map
   induced by def-weil-derived-category-cohomology-functor.
7. For pointFiniteDimensional objects, the cohomology model is bounded and termwise
   finite-dimensional (def-weil-point-fd-complexes). Its terms are finitely generated
   (def-weil-finite-dimensional-subspace, def-weil-finitely-generated-module) and
   projective (lem-weil-pbc-vector-space-projective), so it is perfect by
   def-pc-perfect-ring-complex.
8. For an idempotent e, each cohomology space decomposes as image H(e) plus kernel
   H(e), via x ↦ (H(e)x, (1-H(e))x), with inverse addition. Both summands retain
   finite dimension and finite support.
9. Transport the inclusions and projections along the cohomology-model isomorphism.
   Step 6 proves their splitting identities. A commuting v preserves image and
   kernel, so ve has blocks rvi and zero; Step 6 gives the asserted equality in D(F).
10. For arbitrary splittings of the same e, the maps r'i and ri' compose to identities
    because ei=i, re=r, ei'=i' and r'e=r'. Using ve=ev in the same compositions
    gives the intertwining equation. These are formal category identities. -/
theorem field_complex_cohomology_splitting (F : Type u) [Field F] :
    (∀ P : CochainComplex (ModuleCat.{u} F) ℤ,
      (∃ V T : ∀ n : ℤ, Submodule F (P.X n),
        (∀ n : ℤ,
          Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
          LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
            LinearMap.ker (P.d n (n + 1)).hom ∧
          IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n))) ∧
      (∀ V T : ∀ n : ℤ, Submodule F (P.X n),
        (∀ n : ℤ,
          Disjoint (LinearMap.range (P.d (n - 1) n).hom) (V n) ∧
          LinearMap.range (P.d (n - 1) n).hom ⊔ V n =
            LinearMap.ker (P.d n (n + 1)).hom ∧
          IsCompl (LinearMap.ker (P.d n (n + 1)).hom) (T n)) →
        ∃ E : HomotopyEquiv
            ({ X := fun n ↦ P.homology n, d := fun _ _ ↦ 0 } :
              CochainComplex (ModuleCat.{u} F) ℤ) P,
          (∀ n : ℤ, LinearMap.range (E.hom.f n).hom = V n) ∧
          (∀ n : ℤ, LinearMap.ker (E.inv.f n).hom =
            LinearMap.range (P.d (n - 1) n).hom ⊔ T n) ∧
          (∀ (n : ℤ) (x : P.cycles n), E.inv.f n (P.iCycles n x) = P.homologyπ n x))) ∧
    (∀ (P Q : CochainComplex (ModuleCat.{u} F) ℤ) (f : P ⟶ Q),
      QuasiIso f → ∃ E : HomotopyEquiv P Q, E.hom = f) ∧
    (∀ P Q : DerivedCategory (ModuleCat.{u} F),
      Function.Bijective (fun f : P ⟶ Q ↦
        fun n : ℤ ↦ (homologyFunctor (ModuleCat.{u} F) n).map f)) ∧
    (∀ P : DerivedCategory (ModuleCat.{u} F), pointFiniteDimensional F P →
      (∃ (H : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ),
        (∀ n m : ℤ, H.d n m = 0) ∧
        (∀ n : ℤ, Nonempty (H.X n ≅ (homologyFunctor (ModuleCat.{u} F) n).obj P)) ∧
        H.IsStrictlyGE a ∧ H.IsStrictlyLE b ∧
        (∀ n : ℤ, FiniteDimensional F (H.X n)) ∧ Nonempty (P ≅ Q.obj H)) ∧
      IsPerfectRingComplex P) ∧
    (∀ (P : DerivedCategory (ModuleCat.{u} F)) (_hP : pointFiniteDimensional F P)
        (e : P ⟶ P), e ≫ e = e →
      (∃ S N : CochainComplex (ModuleCat.{u} F) ℤ,
        (∀ n m : ℤ, S.d n m = 0 ∧ N.d n m = 0) ∧
        (∀ n : ℤ,
          Nonempty (S.X n ≅ ModuleCat.of F
            (LinearMap.range ((homologyFunctor (ModuleCat.{u} F) n).map e).hom)) ∧
          Nonempty (N.X n ≅ ModuleCat.of F
            (LinearMap.ker ((homologyFunctor (ModuleCat.{u} F) n).map e).hom))) ∧
        ∃ (i : Q.obj S ⟶ P) (r : P ⟶ Q.obj S)
            (j : Q.obj N ⟶ P) (s : P ⟶ Q.obj N),
          i ≫ r = 𝟙 (Q.obj S) ∧ r ≫ i = e ∧
          j ≫ s = 𝟙 (Q.obj N) ∧ s ≫ j = 𝟙 P - e ∧
          ∃ α : P ≅ Q.obj S ⊞ Q.obj N,
            α.hom = biprod.lift r s ∧ α.inv = biprod.desc i j ∧
            ∀ v : P ⟶ P, v ≫ e = e ≫ v →
              α.inv ≫ (e ≫ v) ≫ α.hom = biprod.map (i ≫ v ≫ r) 0) ∧
      (∀ (v : P ⟶ P) (_hv : v ≫ e = e ≫ v)
          (S S' : DerivedCategory (ModuleCat.{u} F))
          (i : S ⟶ P) (r : P ⟶ S) (i' : S' ⟶ P) (r' : P ⟶ S'),
        i ≫ r = 𝟙 S → r ≫ i = e → i' ≫ r' = 𝟙 S' → r' ≫ i' = e →
          (i ≫ r') ≫ (i' ≫ r) = 𝟙 S ∧
          (i' ≫ r) ≫ (i ≫ r') = 𝟙 S' ∧
          (i ≫ v ≫ r) ≫ (i ≫ r') = (i ≫ r') ≫ (i' ≫ v ≫ r'))) := by
  sorry

end DerivedCategory
