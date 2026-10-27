/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF, SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
import Sheaf.AlgebraicGeometry.NodalNormalizedChartUniqueness
import Sheaf.AlgebraicGeometry.NodalLocalAlgebraComparison
import Sheaf.AlgebraicGeometry.ReducedNormalizationLocalFiber
import Sheaf.AlgebraicGeometry.NodalGeometricBranchSquare
import Sheaf.AlgebraicGeometry.SeparableNodeQuadraticCompletion

/-!
# Tangent directions and normalization branches of a geometric node

Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU, and 0CBW.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- The tangent Proj of a geometric node is canonically its quadratic normalization
residue spectrum, with its scheme-normalization fibre and its two completed branches.

Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU, 0CBW
(blueprint: lem-sfb-nodal-local-tangent-normalization).

Proof:
1. The separable quadratic completion theorem supplies reducedness, Noetherianity,
   essential finite type, dimension one, and the nondegenerate quadratic presentation.
   Construct the canonical grading and its degree-zero residue isomorphism directly
   from the actual homogeneous direct-sum inclusions.
2. The local quadratic comparison supplies the normalized tangent isomorphism, a
   regular parameter generating the extended maximal ideal whose chart covers Proj,
   the split/separable-field alternative, and naturality. The normalized chart formula
   proves uniqueness and the square over the residue field: lift every homogeneous
   fraction to an ideal-power representative, and use the formula at degree zero.
3. Local Noetherianity allows the scheme-normalization local-fibre theorem. Its
   cartesian square gives the fibre isomorphism and both projection equations by the
   universal property of the pullback. Assemble these data into Comparison.
4. The geometric branch square compares the actual normalization residue algebra
   with the completed geometric normalization residue algebra. Transport the square
   along the inverse tangent isomorphism and use its pullback isomorphism. The first
   projection reduces by the inverse-hom identity; the second is the pullback equation.
   The supplied representative formulas and cardinality two give GeometricBranches.
-/
theorem tangent_normalization
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hpure : C.IsPureDimension 1)
    (x : C) (hx : x ∈ closedPoints C)
    (hfinite : (f.residueFieldAlgebraMap x).Finite)
    (hsep : @Algebra.IsSeparable k (C.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (xbar : pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    (hxbar : pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) xbar = x)
    (hnode : Nonempty (CompletedLocalRing
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) xbar ≃+*
      (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
        {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * MvPowerSeries.X 1}))) :
    ∃ (graded : GradedRing (tangentGrading (C.presheaf.stalk x))) (D : @Comparison C x graded),
      D.IsNatural ∧
        D.GeometricBranches
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) xbar hxbar := by
  let : Algebra k (C.presheaf.stalk x) := (stalkScalarMap f x).toAlgebra
  obtain ⟨hred, hnoeth, heft, hdim, σ, _, _, a, b, c, hdisc, e, _, _⟩ :=
    separable_node_quadratic_completion f hpure x hx hfinite hsep Ω xbar hxbar hnode
  let : _root_.IsReduced (C.presheaf.stalk x) := hred
  let : IsNoetherianRing (C.presheaf.stalk x) := hnoeth
  let : Algebra.EssFiniteType k (C.presheaf.stalk x) := heft
  let : Algebra (C.residueField x) (CompletedLocalRing C x) := σ.toAlgebra
  have hquad : ∃ a b c : IsLocalRing.ResidueField (C.presheaf.stalk x),
      b ^ 2 - 4 * a * c ≠ 0 ∧
        Nonempty (CompletedLocalRing C x ≃+* QuadraticSeries.CurveRing a b c) := by
    refine ⟨a, b, c, hdisc, ?_⟩
    have heq : QuadraticSeries.equation a b c =
        MvPowerSeries.C a * MvPowerSeries.X 0 ^ 2 +
          MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
          MvPowerSeries.C c * MvPowerSeries.X 1 ^ 2 := by
      unfold QuadraticSeries.equation
      rw [mul_assoc (MvPowerSeries.C b)]
    change Nonempty (_ ≃+* (_ ⧸ Ideal.span {QuadraticSeries.equation a b c}))
    rw [heq]
    exact ⟨e.toRingEquiv⟩
  let graded := canonicalGrading (C.presheaf.stalk x)
  let := graded
  obtain ⟨i, hnormalized, hparameter, hquadratic, hnatural⟩ :=
    quadratic_tangent_comparison k (C.presheaf.stalk x) hdim hquad
  obtain ⟨f₀, hf₀, hlinear, hreg, hgen, hcover⟩ := hparameter
  have hi := normalized_iso_over_residue (C.presheaf.stalk x) f₀ hf₀ hlinear hreg hgen
    hcover i hnormalized
  have hunique : ∀ j : Proj (tangentGrading (C.presheaf.stalk x)) ≅
      Spec (.of (ResidueAlgebra (C.presheaf.stalk x))),
      IsNormalized (C.presheaf.stalk x) j → j = i := by
    intro j hj
    exact normalized_iso_unique (C.presheaf.stalk x) f₀ hf₀ hlinear hreg hgen hcover
      j i hj hnormalized
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨l, hl, hfiber⟩ := reduced_normalization_local_fibre C x
  let D : Comparison C x := {
    zeroIso := tangentZeroIso (C.presheaf.stalk x)
    zeroIso_apply := tangentZeroIso_apply (C.presheaf.stalk x)
    iso := i
    over_residue := hi
    normalized := hnormalized
    unique := hunique
    quadratic := hquadratic
    normalizationLift := l
    normalizationLift_over := hl
    fiberIso := hfiber.isoPullback
    fiberIso_fst := hfiber.isoPullback_hom_fst
    fiberIso_snd := hfiber.isoPullback_hom_snd }
  refine ⟨graded, D, hnatural, ?_⟩
  obtain ⟨ω, ρ, ν, r, hω, hρ, hν, hr, hsquare, hcard⟩ :=
    geometric_branch_square f hpure x hx hfinite hsep Ω xbar hxbar hnode
  let g := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  have hsquare' := hsquare.of_iso (Iso.refl _) i.symm (Iso.refl _) (Iso.refl _)
    (fst' := Spec.map (CommRingCat.ofHom r) ≫ i.inv)
    (snd' := Spec.map (CommRingCat.ofHom (completedBranchScalars g xbar)))
    (f' := i.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)))))
    (g' := Spec.map (CommRingCat.ofHom ρ))
    (by simp) (by simp [g]) (by simp) (by simp)
  refine ⟨ω, ρ, ν, r, hsquare'.isoPullback, hω, hρ, hν, hr, ?_,
    hsquare'.isoPullback_hom_snd, hcard⟩
  rw [hsquare'.isoPullback_hom_fst_assoc]
  simp only [D, Category.assoc, i.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.NodalLocal
