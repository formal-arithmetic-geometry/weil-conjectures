/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover
import WeilConjectures.RingTheory.PrincipalFreeAlgebraNorm
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Affine chart formula for the canonical polynomial norm

Source: Stacks Project, Exercises, Tags 02DU(1), 02DV(1),(3), and Groupoids Tag 03BJ,
second paragraph (blueprint: lem-a1-affine-groupoid-canonical-norm-charts).

The theorem isolates the comparison between the canonical determinant norm selected by
finite-local-freeness and the affine-open section norm used by the polynomial invariance
argument. Its proof transports principal localization bases through the canonical tensor
localization equivalence, then applies determinant invariance and the affine norm chart
construction. The comparison uses no groupoid hypotheses and applies to polynomial algebras.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem localizedModule_scalar_eq {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (a : A) :
    LocalizedModule.moduleOfIsLocalization (S := Submonoid.powers a) (M := B)
      (T := Localization.Away a) =
      (inferInstance : Module (Localization.Away a) (LocalizedModule.Away a B)) := by
  apply Module.ext'
  intro x z
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
  induction z using LocalizedModule.induction_on with
  | h b t =>
    rw [LocalizedModule.mk'_smul_mk, ← Localization.mk_eq_mk',
      LocalizedModule.mk_smul_mk]

private theorem canonicalNorm_spec {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (r : ℕ)
    (h : (Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) :
    Algebra.IsLocallyFreeDeterminantNorm φ (Algebra.finiteLocallyFreeDeterminantNorm φ r h) :=
  (Classical.choose_spec (Algebra.finiteLocallyFree_norm_characteristicPolynomial φ r h).2).1.1

private theorem canonicalNorm_eq_principalFreeNorm {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (h : (Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r)
    (m : ℕ) (f : Fin m → A) (hf : Ideal.span (Set.range f) = ⊤)
    (he : letI := φ.toAlgebra
      ∀ j : Fin m, ∃ _e : Module.Basis (Fin r) (Localization.Away (f j))
        (LocalizedModule.Away (f j) B), True) :
    letI := φ.toAlgebra
    Algebra.finiteLocallyFreeDeterminantNorm φ r h = Algebra.principalFreeNorm f hf he := by
  let := φ.toAlgebra
  apply (Algebra.principalFreeNorm_spec.{u, u, 0} f hf he).2.1
  intro a k e b
  let E := (LocalizedModule.isBaseChange (Submonoid.powers a) B).equiv
  have hN := canonicalNorm_spec φ r h a k (e.map E.symm) b
  rw [hN]
  congr 1

/-- Every canonical determinant norm on an affine finite locally free algebra is computed
by the glued affine-open norm on a finite free chart around each point.

Source: Stacks Project, Exercises, Tags 02DU(1), 02DV(1),(3), and Groupoids Tag 03BJ,
second paragraph (blueprint: lem-a1-affine-groupoid-canonical-norm-charts).

Proof: The principal basis cover theorem gives a finite family generating the unit ideal
and rank-r localized bases. Transport these through the canonical tensor/localization
linear equivalence. Multiplication matrices are unchanged by that transport, so uniqueness
identifies the canonical determinant norm with principalFreeNorm. At each point use the
finite-locally-free norm chart theorem to choose a free affine chart. Take a finite basis
of its section algebra. The affine-open formula for principalFreeNorm and
Algebra.norm_eq_matrix_det identify both values with the determinant of multiplication
by the restricted element. Zero rings, empty charts, and empty bases satisfy the same
formulas, so no nontriviality or positive-rank hypothesis is needed. -/
theorem affineGroupoid_canonicalNorm_chart_formula
    (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (h : (Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) (b : B) :
    ∀ x : Spec (CommRingCat.of A), ∃ V : (Spec (CommRingCat.of A)).Opens,
      x ∈ V ∧ IsAffineOpen V ∧
      (letI := ((Spec.map (CommRingCat.ofHom φ)).app V).hom.toAlgebra
       Module.Free Γ(Spec (CommRingCat.of A), V)
         Γ(Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ V) ∧
       Module.Finite Γ(Spec (CommRingCat.of A), V)
         Γ(Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ V) ∧
       (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op
           ((Scheme.ΓSpecIso (CommRingCat.of A)).inv
             (Algebra.finiteLocallyFreeDeterminantNorm φ r h b)) =
         Algebra.norm Γ(Spec (CommRingCat.of A), V)
           ((Spec (CommRingCat.of B)).presheaf.map
             (homOfLE (le_top : Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ V ≤ ⊤)).op
             ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) := by
  classical
  let := φ.toAlgebra
  let := h
  obtain ⟨hqc, -, -, m, f, hf, -, -, hb⟩ :=
    finiteLocallyFree_principalBasisCover A B r
  have he : ∀ j : Fin m, ∃ _e : Module.Basis (Fin r) (Localization.Away (f j))
      (LocalizedModule.Away (f j) B), True := by
    intro j
    have b := (hb j).choose
    change @Module.Basis _ _ _ _ _
      (LocalizedModule.moduleOfIsLocalization (S := Submonoid.powers (f j))
        (M := B) (T := Localization.Away (f j))) at b
    rw [localizedModule_scalar_eq] at b
    exact ⟨b, trivial⟩
  have hN := canonicalNorm_eq_principalFreeNorm φ r h m f hf he
  let s := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨_, hg⟩ := exists_finiteLocallyFree_norm_charts s ⊤
    ((Spec (CommRingCat.of B)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))
  intro x
  obtain ⟨V, -, hxV, hV, hfree, hfin, -⟩ := hg x trivial
  let := (s.app V).hom.toAlgebra
  let := hfree
  let := hfin
  let E := (Module.Free.chooseBasis Γ(Spec (CommRingCat.of A), V)
    Γ(Spec (CommRingCat.of B), s ⁻¹ᵁ V)).reindex (Fintype.equivFin _)
  refine ⟨V, hxV, hV, hfree, hfin, ?_⟩
  rw [hN]
  have hh := principalFreeNorm_affineOpen f hf he hqc ⟨V, hV⟩ _ E b
  rw [Algebra.norm_eq_matrix_det E]
  convert hh using 1
  · simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  · congr 1
    ext j k
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, id_eq, CommRingCat.Hom.hom]
    rfl

end AlgebraicGeometry
