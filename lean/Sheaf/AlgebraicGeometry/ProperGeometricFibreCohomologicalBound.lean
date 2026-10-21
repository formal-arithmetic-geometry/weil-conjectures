/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Uniform dimension and torsion cohomology bounds for proper fibres

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-proper,
`sk-prop-ctf-finite-proper-localizing.proof.md`, Étale statements, uniform bound;
Stacks Project, Tags 0A3V, 00P3, 0F0V and 03QU
(blueprint: lem-sfb-finite-proper-geometric-cd-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper morphism to a quasi-compact scheme has one nonnegative bound on every
base-changed fibre dimension and twice that bound on torsion cohomology of its
fibres over separably closed fields. Empty fibres are included.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-proper,
`sk-prop-ctf-finite-proper-localizing.proof.md`, Étale statements, uniform bound;
Stacks Project, Tags 0A3V, 00P3, 0F0V and 03QU
(blueprint: lem-sfb-finite-proper-geometric-cd-bound).

Proof:
1. Properness implies finite type. Apply `lem-fin-finite-type-fibre-dimension-bound`
   to obtain a natural number e bounding all ordinary fibres over the quasi-compact
   base. If the base is empty, choose e = 0; empty fibres have dimension bottom.
2. For any field-valued point u : Spec L → Y, residue-field point naturality
   (`lem-weil-pbc-residue-field-point-naturality`) factors u through Spec κ(y),
   where y is its image. The fibre-product universal property identifies its fibre
   with the ordinary fibre at y extended to L. Finite type is preserved under
   arbitrary base change (`lem-sfb-finite-type-composition-base-change`), so the
   field-extension clause of `lem-kun-dimension-extension` keeps its dimension
   unchanged, including for empty fibres. Isomorphic schemes have identical
   chains of irreducible closed subsets and hence identical Krull dimensions.
3. For any S → Y and s in S, pullback pasting identifies the fibre of X ×_Y S → S
   at s with X ×_Y Spec κ(s). The maps in both directions have the same projections,
   hence are inverse by the pullback universal property. Apply step 2; no
   quasi-compactness condition on S is needed.
4. For a separably closed Ω and Spec Ω → Y, the fibre Z is finite type over Ω
   and has dimension at most e. By `lem-weil-pbc-torsion-sheaf-characterizations`,
   the colimit torsion hypothesis implies locally annihilated sections.
   `lem-sf-separably-closed-torsion-cd` gives torsion cohomological dimension zero
   for Ω. Apply `new-thm-sc-affine-torsion-cd-bound` with d = e and c = 0, then
   `new-thm-sc-finite-type-torsion-cd-affine-reduction` to obtain vanishing above
   2e. These bounds cover empty schemes and arbitrary torsion without a common
   annihilator or invertibility hypothesis. The cohomology here is derived global
   sections of F in degree zero, as in `def-weil-pbc-etale-cohomology`. -/
theorem exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [CompactSpace Y] :
    ∃ e : ℕ,
      (∀ (S : Scheme.{u}) (g : S ⟶ Y) (s : S),
        topologicalKrullDim ((pullback.snd f g).fiber s) ≤ (e : WithBot ℕ∞)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ybar : Spec (.of Ω) ⟶ Y)
        (F : Sheaf (pullback f ybar).smallEtaleTopology AddCommGrpCat.{u + 1}),
        Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ, 2 * e < q →
          IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback f ybar) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (pullback f ybar).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  obtain ⟨e, he⟩ := exists_fibre_dimension_bound f
  have hfield (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y) :
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
    calc
      topologicalKrullDim (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme)
          = topologicalKrullDim
              (pullback (pullback.snd f (Y.fromSpecResidueField y)) (Spec.map t) :
                Scheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
          (Y.fromSpecResidueField y) (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ = topologicalKrullDim (f.fiber y) := by
        let : (f.fiber y).Over (Spec (Y.residueField y)) :=
          ⟨f.fiberToSpecResidueField y⟩
        let : Algebra (Y.residueField y) K := t.hom.toAlgebra
        let : LocallyOfFiniteType (f.fiber y ↘ Spec (.of (Y.residueField y))) := by
          change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y))
          infer_instance
        let : QuasiCompact (f.fiber y ↘ Spec (.of (Y.residueField y))) := by
          change QuasiCompact (pullback.snd f (Y.fromSpecResidueField y))
          infer_instance
        exact (topologicalKrullDim_fieldExtension_and_denseOpen
          (K := Y.residueField y) (X := f.fiber y)).1 K
      _ ≤ (e : WithBot ℕ∞) := he y
  refine ⟨e, ?_, ?_⟩
  · intro S g s
    let a := pullbackLeftPullbackSndIso f g (S.fromSpecResidueField s)
    exact (IsHomeomorph.topologicalKrullDim_eq _ a.hom.homeomorph.isHomeomorph).le.trans
      (hfield (S.residueField s) (S.fromSpecResidueField s ≫ g))
  · intro Ω _ _ ybar F hF q hq
    have hK : ∀ G : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1},
        G.IsTorsion → ∀ n : ℕ, 0 < n → Subsingleton (Sheaf.H G n) := by
      intro G hG n hn
      obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of Ω)) n
      have hz := AddCommGrpCat.isZero_iff_subsingleton.mpr
        (Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed Ω G hG n hn)
      exact AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso (a.app G))
    have hAffine : ∀ {Z : Scheme.{u}} (b : Z ⟶ Spec (.of Ω)) [LocallyOfFiniteType b]
        [QuasiCompact b] [IsAffine Z] (hZ : topologicalKrullDim Z ≤ (e : WithBot ℕ∞))
        (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
        (n : ℕ), e + 0 < n → Subsingleton (Sheaf.H G n) := by
      intro Z b _ _ _ hZ G hG n hn
      exact Scheme.subsingleton_H_of_two_mul_add_lt_of_isAffine 0 e hK b hZ G hG n hn
    have hH := Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound 0 e
      (pullback.snd f ybar) (hfield Ω ybar) hAffine F
      ((Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hF) q (by omega)
    obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso (pullback f ybar) q
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr hH).of_iso (a.app F).symm

end AlgebraicGeometry
