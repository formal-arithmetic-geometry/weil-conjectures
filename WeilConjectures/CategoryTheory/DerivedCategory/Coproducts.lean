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

namespace DerivedCategory

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- For a K-injective complex `L`, every morphism `Q M ⟶ Q L` in the derived category is the
image of a morphism of complexes `M ⟶ L`. -/
lemma Q_map_surjective_of_isKInjective (M L : CochainComplex C ℤ) [L.IsKInjective]
    (φ : Q.obj M ⟶ Q.obj L) : ∃ g : M ⟶ L, Q.map g = φ := by
  let e := quotientCompQhIso C
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj M) L).2 (e.hom.app M ≫ φ ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
  refine ⟨g, ?_⟩
  have := e.hom.naturality g
  simp only [Functor.comp_map] at this hψ
  rw [← cancel_epi (e.hom.app M), ← this, hψ]
  simp

/-- For a K-injective complex `L`, a morphism of complexes `g : M ⟶ L` becomes zero in the
derived category only if it is null-homotopic. -/
lemma nonempty_homotopy_zero_of_Q_map_eq_zero {M L : CochainComplex C ℤ} [L.IsKInjective]
    (g : M ⟶ L) (hg : Q.map g = 0) : Nonempty (Homotopy g 0) := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff]
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj M) L).1
  have h2 : Qh.map ((HomotopyCategory.quotient _ _).map g) = 0 := by
    have := (quotientCompQhIso C).hom.naturality g
    rw [hg, comp_zero, Functor.comp_map] at this
    exact (cancel_mono ((quotientCompQhIso C).hom.app L)).1 (by simpa using this)
  rw [h2, Functor.map_zero]

lemma Q_map_eq_zero_of_homotopy {M L : CochainComplex C ℤ} (g : M ⟶ L) (h : Homotopy g 0) :
    Q.map g = 0 := by
  have := (quotientCompQhIso C).hom.naturality g
  rw [Functor.comp_map, HomotopyCategory.eq_of_homotopy _ _ h, Functor.map_zero,
    Functor.map_zero, zero_comp] at this
  exact (cancel_epi ((quotientCompQhIso C).hom.app M)).1 (by simpa using this.symm)

variable [HasKInjectiveResolutions C] {ι : Type w} [HasCoproductsOfShape ι C]
  (K : ι → CochainComplex C ℤ)

/-- The image under `Q` of the coproduct of a family of complexes, as a cofan in `D(C)`. -/
noncomputable abbrev sigmaCofan : Cofan fun i ↦ Q.obj (K i) :=
  Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)

variable {K} in
/-- The morphism `Q(∐ K) ⟶ M` induced by a family `Q(K i) ⟶ M`: write `M ≅ Q I` with `I`
K-injective, lift the components to morphisms of complexes `K i ⟶ I` and glue them. -/
noncomputable def sigmaCofanDesc {M : DerivedCategory C} (f : ∀ i, Q.obj (K i) ⟶ M) :
    Q.obj (∐ K) ⟶ M :=
  have : (exists_iso_Q_obj_of_isKInjective M).choose.IsKInjective :=
    (exists_iso_Q_obj_of_isKInjective M).choose_spec.choose
  Q.map (Sigma.desc fun i ↦ (Q_map_surjective_of_isKInjective (K i) _
    (f i ≫ (exists_iso_Q_obj_of_isKInjective M).choose_spec.choose_spec.some.hom)).choose) ≫
    (exists_iso_Q_obj_of_isKInjective M).choose_spec.choose_spec.some.inv

/-- The image `Q(∐ K)` of the termwise coproduct is a coproduct of the `Q(K i)` in `D(C)`. -/
noncomputable def isColimitSigmaCofan : IsColimit (sigmaCofan K) := by
  refine Cofan.IsColimit.mk _ (fun t ↦ sigmaCofanDesc t.inj) ?_ ?_
  · intro t i
    have : (exists_iso_Q_obj_of_isKInjective t.pt).choose.IsKInjective :=
      (exists_iso_Q_obj_of_isKInjective t.pt).choose_spec.choose
    dsimp [sigmaCofanDesc]
    rw [← Category.assoc, ← Q.map_comp, Sigma.ι_desc,
      (Q_map_surjective_of_isKInjective _ _ _).choose_spec]
    simp
  · intro t m hm
    have : (exists_iso_Q_obj_of_isKInjective t.pt).choose.IsKInjective :=
      (exists_iso_Q_obj_of_isKInjective t.pt).choose_spec.choose
    let e := (exists_iso_Q_obj_of_isKInjective t.pt).choose_spec.choose_spec.some
    have hg : ∀ i, Q.map (Q_map_surjective_of_isKInjective (K i) _ (t.inj i ≫ e.hom)).choose =
        t.inj i ≫ e.hom := fun i ↦ (Q_map_surjective_of_isKInjective (K i) _ _).choose_spec
    obtain ⟨g', hg'⟩ := Q_map_surjective_of_isKInjective (∐ K) _ (m ≫ e.hom)
    rw [← cancel_mono e.hom]
    dsimp only [sigmaCofanDesc]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← hg', ← sub_eq_zero, ← Q.map_sub]
    refine Q_map_eq_zero_of_homotopy _
      (HomologicalComplex.nonempty_homotopy_zero_of_sigma K _ fun i ↦ ?_).some
    refine nonempty_homotopy_zero_of_Q_map_eq_zero _ ?_
    rw [Preadditive.comp_sub, Q.map_sub, Sigma.ι_desc, hg, Q.map_comp, hg', ← Category.assoc]
    erw [hm]
    exact sub_self _

end DerivedCategory
