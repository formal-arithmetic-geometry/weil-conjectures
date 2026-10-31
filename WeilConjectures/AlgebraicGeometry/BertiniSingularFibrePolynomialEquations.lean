/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BertiniUniversalFamily
public import WeilConjectures.AlgebraicGeometry.BertiniLocalFirstJets
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.BertiniSingularFibreJetTensor

/-!
# Polynomial value and differential equations on the singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`;
Algebra Tag 00T7 supplies the one-way smooth hypersurface criterion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem polynomial_relation_of_jet_tensor
    {K A V I : Type u} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [Fintype I]
    (q : MvPolynomial I K →ₐ[K] A) (v : I → V)
    (hv : (∑ i, q (MvPolynomial.X i) ⊗ₜ[K] v i : A ⊗[K] V) = 0)
    (φ : Module.Dual K V) :
    q (∑ i, MvPolynomial.C (φ (v i)) * MvPolynomial.X i) = 0 := by
  have h := congrArg ((TensorProduct.rid K A).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : A →ₗ[K] A) φ)) hv
  have hz : (∑ i, φ (v i) • q (MvPolynomial.X i)) = 0 := by
    simpa only [LinearMap.comp_apply, map_sum, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] using h
  simpa only [map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
    AlgHom.commutes, Algebra.smul_def] using hz

/-- The singular fibre has its actual polynomial coordinate quotient, and its local
value and differential equations vanish in that quotient. This statement requires
neither generation nor an immersive system, and makes no assertion about jet rank.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`,
and Algebra Tag 00T7, the nonzero differential criterion.
(blueprint: lem-zl-bertini-singular-fibre-polynomial-equations).

Proof: The universal zero scheme is closed in coefficient affine space times Y.
The reduced singular scheme is closed in that zero scheme. Restricting to U and
base changing the composite to Spec kappa(z) gives a closed immersion into affine
coefficient space over kappa(z). Thus its source is affine; let A be its actual
coordinate ring, with the induced kappa(z)-algebra structure. The closed immersion
induces the surjective polynomial quotient q, and the pullback projection identities
give the displayed compatibility with the original coefficient morphism.

To prove the equations, restrict further to W; this does not alter the fibre over z.
In the pulled-back frame e, the universal section is F = sum_i x_i a_i, where a_i
is the coefficient of s_i. Its differential relative to coefficient space is
sum_i x_i da_i. The ambient projection is smooth by base change. At any point of
the universal zero scheme where this differential is nonzero, the hypersurface
criterion gives a smooth open neighbourhood. Thus the differential vanishes at
every point of the nonsmooth subset. On a smaller neighbourhood of z, choose a
basis of the locally free relative differential sheaf. Each coordinate of dF
vanishes on the nonsmooth subset and belongs to its vanishing ideal; it is zero
on the reduced singular scheme and remains zero on the fibre. The equation F is
already zero on the universal zero scheme. Every residue-field linear functional
on the direct sum of values and differentials is a linear combination of the value
coordinate and these differential coordinates. Applying it gives the asserted
polynomial relation. No flatness of the universal hypersurface is used. Empty
fibres give the zero coordinate ring, in which all these relations still hold. -/
theorem bertini_singular_fibre_polynomial_equations
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤))
    (U : Y.Opens) (z : U) (W : Y.Opens) (hz : U.ι z ∈ W)
    (e : Γ(L, W)) (he : Scheme.Modules.IsFreeGenerator e) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ((U : Scheme).residueField z) A),
      ∃ (j : (bertiniSingularToSource f L s ∣_ U).fiber z ≅ Spec (.of A))
        (q : MvPolynomial I ((U : Scheme).residueField z) →ₐ[
          (U : Scheme).residueField z] A),
        Function.Surjective q ∧
        (∀ φ : Module.Dual ((U : Scheme).residueField z)
            ((U : Scheme).residueField z × bertiniCotangentFibre f U z),
          q (∑ i, MvPolynomial.C (φ (bertiniLocalFirstJet f U z W hz
            (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))))) *
            MvPolynomial.X i) = 0) ∧
        j.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
          ((algebraMap ((U : Scheme).residueField z) A).comp
            ((U.ι ≫ f).residueFieldAlgebraMap z))
          (fun i ↦ q (MvPolynomial.X i)))) =
            (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
              ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι ≫
              (bertiniSingularIdeal f L s).subschemeι ≫ bertiniUniversalProjection f L s := by
  classical
  let K := (U : Scheme).residueField z
  let T := (bertiniSingularToSource f L s ∣_ U).fiber z
  let A := Γ(T, ⊤)
  let ρ := bertiniSingularFibreRingMap f L s U z
  let : Algebra K A := (ρ.comp MvPolynomial.C).toAlgebra
  let q : MvPolynomial I K →ₐ[K] A :=
    { toRingHom := ρ, commutes' := fun _ ↦ rfl }
  have : IsClosedImmersion (bertiniSingularFibreCoordinates f L s U z) :=
    bertini_singular_fibre_coordinates_isClosedImmersion f L s U z
  have : IsAffine T :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      (bertiniSingularFibreCoordinates f L s U z)).1
  refine ⟨A, inferInstance, inferInstance, T.isoSpec, q,
    bertini_singular_fibre_ringMap_surjective f L s U z, ?_, ?_⟩
  · exact polynomial_relation_of_jet_tensor q
      (fun i ↦ bertiniLocalFirstJet f U z W hz
        (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))))
      (bertini_singular_fibre_jet_tensor f L s U z W hz e he)
  · have hpoly : MvPolynomial.eval₂Hom
        ((algebraMap K A).comp ((U.ι ≫ f).residueFieldAlgebraMap z))
        (fun i ↦ q (MvPolynomial.X i)) =
        ρ.comp (MvPolynomial.map ((U.ι ≫ f).residueFieldAlgebraMap z)) := by
      rw [MvPolynomial.map_eq_eval₂Hom_C_comp, MvPolynomial.comp_eval₂Hom]
      rfl
    rw [hpoly, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
    change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫ _ = _
    rw [bertini_singular_fibre_ringMap_spec, bertiniSingularFibreCoordinates_map]
    rfl

end AlgebraicGeometry
