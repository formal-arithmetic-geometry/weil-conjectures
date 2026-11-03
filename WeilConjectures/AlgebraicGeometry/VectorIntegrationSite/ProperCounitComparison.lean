/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectionIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProperCounitMateSquare
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProperCounitTensorTrace

/-!
# Proper projective-line counit comparison under site comparison

Source: blueprint `lem-route-line-proper-counit-comparison`, first paragraph of
`lem-amb-affine-space-top-trace.proof.md` (blueprint: lem-route-line-proper-counit-comparison).
The statement uses the canonical direct-image mate, tensor/pullback comparison,
and uniquely normalized projective proper counit already recorded by the dependency nodes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local instance 100000] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The normalized proper projective-line counit is carried to the ordinary counit
by the canonical etale-to-pro-etale direct-image mate and coefficient comparison.
Source: blueprint `lem-amb-affine-space-top-trace.proof.md`, first (d=1) paragraph,
lines 19--24; Stacks 0B65 and 099R (blueprint: lem-route-line-proper-counit-comparison).

Proof:
1. `q` is proper, so the etale and pro-etale direct images and their adjunctions exist;
   `D` gives the actual counit `ε^e_K`, `C` is exact and `a_q` is the canonical pull
   comparison (def-amb-p1-trace, def-asd-ordinary-finite-p1-data,
   def-sf-comparison-derived-pullback).
2. `q` is qcqs and `M_K` is bounded below, so the counit equation of the canonical
   mate gives `ε^p_{C_P M_K} ∘ Lq_p^*(β_{M_K}) ∘ a_{q,R_e M_K} = C_P(ε^{q,e}_{M_K})`
   (lem-weil-pbc-comparison-direct-image-canonical-mate).
3. By the tensorator and the pullback square, `ρ^0_K = (a_{q,K} ⊗ 1) ∘ t_P` is
   `projectiveRightComparison`; `ρ_K = ρ^0_K ≫ θ_K` with `θ_K = 1 ⊗ τ_P[2]`.
4. The etale/pro-etale projection comparison at `p = q`, `K := W_e`, `N := K`
   (lem-sfb-projection-comparison-etale-proetale), conjugated by the signed
   symmetries (lem-amb-proper-coproducts-projection,
   lem-pur-comparison-tensorator-signed-symmetry), gives the square
   `R_p(ρ^0_K) ∘ β_{M_K} ∘ C_T(π_e) = π_p ∘ (1 ⊗ β_{W_e}) ∘ t_T(K, R_e W_e)`.
5. Under `χ = C_P(D.chern)` the decompositions agree,
   `β_{W_e} ∘ C_T(b_q) = b^p ∘ σ_T` (lem-route-line-projective-decomposition-comparison);
   taking the second projection gives `t^p_q ∘ β_{W_e} = C_T(t_q)`.
6. Unfold `ε^p_K = π_p⁻¹ ≫ (1 ⊗ t^p_q) ≫ r^p` with `r^p = t_T⁻¹ ≫ C_T(r)` and
   `ε^e_K = π_e⁻¹ ≫ (1 ⊗ t_q) ≫ r`. Step 4 gives
   `β_{M_K} ≫ R_p(ρ^0_K) ≫ π_p⁻¹ = C_T(π_e)⁻¹ ≫ t_T ≫ (1 ⊗ β_{W_e})`; Step 5 and
   naturality of `t_T` turn the rest into `C_T(1 ⊗ t_q) ≫ C_T(r)`, which is
   `C_T(ε^e_K)`. The argument is natural in `K` and covers zero coefficients and
   the empty base.
-/
theorem proper_counit_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hχ : projectiveChern l E n T hT hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T)).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA T
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1))).chern)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    let A := Scheme.finiteTateCoefficient l E n
    let P := ProjectiveLine T
    let q : P ⟶ T := P ↘ T
    let M := (Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hA T).obj K.obj
    let D := Etale.projectiveLineTraceDatum (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hA T
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
    geoP1PushComparison A q M ≫
        (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
          (projectiveRightComparison l E n r hA T K.obj).hom ≫
        projectiveEpsilon l E n T hT hI r hA K =
      (comparison A T).map (D.adjunction.counit.app K.obj) := by
  dsimp only
  let A := Scheme.finiteTateCoefficient l E n
  let P := ProjectiveLine T
  let q : P ⟶ T := P ↘ T
  let M := (Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hA T).obj K.obj
  let D := Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) A hA T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
  letI : IsLocallyNoetherian (ProjectiveLine T) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine T ↘ T)
  letI : CompactSpace (ProjectiveLine T) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine T ↘ T)
  letI : IsProper (ProjectiveLine T ↘ T) :=
    ProjectiveSpace.instIsProper (ULift (Fin 2)) T
  letI : IsIso (Etale.ordinaryFiniteProjection A (ProjectiveLine T ↘ T)
      ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
      K.obj) :=
    Etale.isIso_proper_projection_formula_reordered A (ProjectiveLine T ↘ T)
      ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
      K.obj
  have hordinary : D.adjunction.counit.app K.obj =
      Etale.projectiveLineTraceEpsilon (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) A hA T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) K.obj := by
    apply (cancel_epi (Etale.ordinaryFiniteProjection A (ProjectiveLine T ↘ T)
      ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
      K.obj)).1
    change _ = Etale.ordinaryFiniteProjection A (ProjectiveLine T ↘ T)
      ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧) K.obj ≫
      (inv (Etale.ordinaryFiniteProjection A (ProjectiveLine T ↘ T)
        ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
        K.obj) ≫
      ((Etale.ordinaryFiniteTensor A T).obj K.obj).map D.trace ≫
        (Etale.derivedTensorSingleUnitIso K.obj).hom)
    rw [IsIso.hom_inv_id_assoc]
    exact D.counit_normalization K.obj
  rw [hordinary]
  apply (cancel_epi ((comparison A T).map (Etale.ordinaryFiniteProjection A
    (ProjectiveLine T ↘ T)
    ((Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧)
    K.obj))).1
  have hmate := proper_counit_mate_square l E n T r hA K
  have htrace := proper_counit_tensor_trace l E n T hT hI r hA hχ K
  dsimp only at hmate htrace
  rw [reassoc_of% hmate]
  simpa only [Category.assoc] using htrace
end AlgebraicGeometry.ProEtale.VectorIntegrationSite
