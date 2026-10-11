/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Coproducts in the derived category

Let `C` be an abelian category with coproducts of shape `ι` and K-injective resolutions. For a
family `K : ι → CochainComplex C ℤ`, the image `Q(∐ K)` of the termwise coproduct is a coproduct
of the `Q(K i)` in `D(C)`: every object of `D(C)` is `Q L` for a K-injective `L`, morphisms
`Q M ⟶ Q L` are homotopy classes of morphisms `M ⟶ L`, and a morphism out of `∐ K` is
null-homotopic as soon as its restrictions to the summands are (homotopies glue termwise).

This is the first input of `lem-kun-0f11` (direct sums and finite cohomological dimension).

## Main statements

- `HomologicalComplex.nonempty_homotopy_zero_of_sigma`: homotopies glue along coproducts.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits CochainComplex.HomComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w} [HasCoproductsOfShape ι C]

/-- A morphism `f : ∐ K ⟶ L` of cochain complexes whose restriction to every summand is
null-homotopic is null-homotopic: the homotopies glue termwise. -/
theorem nonempty_homotopy_zero_of_sigma (K : ι → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f : ∐ K ⟶ L) (h : ∀ i, Nonempty (Homotopy (Sigma.ι K i ≫ f) 0)) :
    Nonempty (Homotopy f 0) := by
  let α (i : ι) := ((Cochain.equivHomotopy _ _) (h i).some).1
  have hα (i : ι) := ((Cochain.equivHomotopy _ _) (h i).some).2
  let hp (p : ℤ) := isColimitOfPreserves (eval C (ComplexShape.up ℤ) p)
    (colimit.isColimit (Discrete.functor K))
  let a : Cochain (∐ K) L (-1) := Cochain.mk fun p q _ ↦ (hp p).desc
    (Cocone.mk _ (Discrete.natTrans fun i ↦ (α i.as).v p q (by omega)))
  have ha (i : ι) (p q : ℤ) (hpq : p + (-1) = q) :
      (Sigma.ι K i).f p ≫ a.v p q hpq = (α i).v p q hpq := by
    simp only [a, Cochain.mk_v]
    exact (hp p).fac _ ⟨i⟩
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨a, ?_⟩⟩
  ext p
  refine (hp p).hom_ext fun ⟨i⟩ ↦ ?_
  have e := Cochain.congr_v (hα i) p p (add_zero p)
  simp only [Cochain.ofHom_v, Cochain.ofHom_zero, add_zero, comp_f] at e
  change (Sigma.ι K i).f p ≫ _ = (Sigma.ι K i).f p ≫ _
  simp only [Cochain.ofHom_v, Cochain.ofHom_zero, add_zero]
  rw [e]
  change (δ (-1) 0 (α i)).v p p _ = _
  rw [δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) (by omega) rfl,
    δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) (by omega) rfl]
  simp only [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ha, Hom.comm]
  simp only [Category.assoc, ha]

end HomologicalComplex
