/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsLe
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionCounitTransition

/-! Ordinary conjugate transport and inversion for coordinate-line exponents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

/-- The ordinary étale conjugate equation after the root-power transition.
Source: the ordinary Kummer-boundary calculation in the final paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-conjugate-exponents-ge).

Proof: put `N = ℓ^{r+1}`, `N' = ℓ^{r'+1}`, `M = max r r'` and
`τ = ρ_{M,r'} ∘ ρ_{M,r}⁻¹ : B_N → B_{N'}` on `P¹_T`. The claim is the image under
the exact site comparison of an equality of ordinary étale maps, which we prove.
1. Unfolding `coordinate_line_ordinary_source_transition`, `sourceCoordinates` and
   `rightCoordinates`, the composite of the transition with `sourceCoordinates r'`
   is `sourceCoordinates r` followed by the component at `Ke` of the natural
   isomorphism `right N ≅ right N'` induced by `τ` on the Kummer line (the
   `eqToIso` coordinate changes cancel by proof irrelevance). So it suffices that
   this isomorphism followed by `comparison N'` is `comparison N`.
2. Both comparisons are conjugates (`conjugateIsoEquiv`) of the adjunctions at
   levels `N` and `N'` against the same exceptional adjunction. By uniqueness of
   conjugates it suffices that the `τ`-induced isomorphism carries the counit at
   level `N'` to the counit at level `N`, i.e. that the integration maps satisfy
   `integration N' ∘ Rq_*(1 ⊗ τ) = integration N`.
3. Integration is `Rq_*` of the open counit followed by the normalized
   projective-line trace `t_q` (def-amb-p1-trace). The open counit and `Rq_*` are
   natural in the coefficient sheaf. The trace at level `N` is normalized by the
   class of `O(1)` in `H²(P¹, B_N)`, the Kummer boundary of the coordinate unit.
   `ρ_{M,a}` is the morphism of Kummer sequences that raises roots of unity to the
   power `ℓ^{M-a}` and is the identity on `G_m`, so it carries the class at level
   `M` to the class at level `a`. Hence `τ` carries the normalized class at level
   `N` to the one at level `N'`, and the two traces correspond. The trace datum
   is fixed by these normalizations, so the choice made at each level does not
   matter.
For `r = r'`, `τ` is the identity and both sides agree. -/
theorem coordinate_line_ordinary_conjugate_transport
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
        ((coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke).hom ≫
          (sourceCoordinates P T r' hA' Ke).hom ≫
          (comparison (Ring P) (P.coefficients.l ^ (r' + 1)) hA' T
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
            (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1))).hom.app Ke) =
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
        ((sourceCoordinates P T r hA Ke).hom ≫
          (comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
            (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).hom.app Ke) := by
  let A := Ring P
  let Nr := P.coefficients.l ^ (r + 1)
  let Ns := P.coefficients.l ^ (r' + 1)
  let hr : 0 < Nr := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let hs : 0 < Ns := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let hTr : IsUnit (Nr : Γ(T, ⊤)) := by
    simpa only [Nr, Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
  let hTs : IsUnit (Ns : Γ(T, ⊤)) := by
    simpa only [Ns, Nat.cast_pow] using (primeUnit P T aT).pow (r' + 1)
  let q := coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke
  let u : (right A Nr hA T).obj Ke ⟶ (right A Ns hA' T).obj Ke :=
    (sourceCoordinates P T r hA Ke).inv ≫ q.hom ≫
      (sourceCoordinates P T r' hA' Ke).hom
  have hu : q.hom ≫ (sourceCoordinates P T r' hA' Ke).hom =
      (sourceCoordinates P T r hA Ke).hom ≫ u := by
    simp only [u, Iso.hom_inv_id_assoc]
  have hc (N : ℕ) (hN : (N : A) = 0) (hpos : 0 < N)
      (hunit : IsUnit (N : Γ(T, ⊤))) :
      (Etale.affineTraceLineLeft A T).map
          ((comparison A N hN T hpos hunit).hom.app Ke) ≫
        (exceptionalAdjunction A T).counit.app Ke =
      (adjunction A N hN T hpos hunit).counit.app Ke := by
    unfold comparison
    simpa using conjugateEquiv_counit (adjunction A N hN T hpos hunit)
      (exceptionalAdjunction A T) (𝟙 _) Ke
  have hAdj := coordinate_line_adjunction_counit_transition P T aT r r' hA hA' Ke
  have hcomp : u ≫ (comparison A Ns hA' T hs hTs).hom.app Ke =
      (comparison A Nr hA T hr hTr).hom.app Ke := by
    apply ((exceptionalAdjunction A T).homEquiv _ Ke).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [Functor.map_comp]
    rw [Category.assoc, hc Ns hA' hs hTs, hAdj, ← hc Nr hA hr hTr]
  have hordinary : q.hom ≫ (sourceCoordinates P T r' hA' Ke).hom ≫
        (comparison A Ns hA' T hs hTs).hom.app Ke =
      (sourceCoordinates P T r hA Ke).hom ≫
        (comparison A Nr hA T hr hTr).hom.app Ke := by
    rw [← Category.assoc, hu, Category.assoc, hcomp]
  simpa only [Functor.map_comp, Category.assoc, A, Nr, Ns, hr, hs, hTr, hTs, q] using
    congrArg (fun z ↦
      (VectorIntegrationSite.comparison A (AffineSpace PUnit.{u + 1} T)).map z) hordinary

end AlgebraicGeometry.ProEtale.CoordinateLine
