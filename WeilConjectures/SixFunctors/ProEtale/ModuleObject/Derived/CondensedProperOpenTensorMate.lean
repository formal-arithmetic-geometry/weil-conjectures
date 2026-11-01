/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap

/-!
# Condensed proper/open tensor mate

Source: `literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`,
independence of compactification paragraph (blueprint: lem-sf-condensed-proper-open-tensor-mate).

The statement uses the canonical normalized proper/open mate from
`CondensedOpenProper.Pasting`, the canonical module-object projection morphisms, and
explicit open-unit normalization equations for the two open tensor maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical module-object projection morphism with the exact-model pullback
`P_f = D(f^*)` in its target: the published projection map
`R_f K ⊗ L ⟶ R_f (K ⊗ Lf^* L)` followed by `R_f (K ⊗ -)` of the canonical identification
`Lf^* ≅ D(f^*)` (`leftDerivedUpperStarIsoMapDerivedCategory`). The source endpoint is the
published one definitionally.
Source: the canonical-map convention (blueprint: def-sfb-module-object-projection-map). -/
noncomputable def canonicalModuleObjectProjectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CondensedOpenProper.D Λ X) (L : CondensedOpenProper.D Λ Y) :
    ((derivedTensor Λ Y).obj ((CondensedOpenProper.R Λ f).obj K)).obj L ⟶
      (CondensedOpenProper.R Λ f).obj (((derivedTensor Λ X).obj K).obj
        ((CondensedOpenProper.P Λ f).obj L)) :=
  (moduleObjectProjectionMap Λ f K L :
      ((derivedTensor Λ Y).obj ((CondensedOpenProper.R Λ f).obj K)).obj L ⟶
        (CondensedOpenProper.R Λ f).obj (((derivedTensor Λ X).obj K).obj
          ((upperStar Λ f).leftDerivedFunctor.obj L))) ≫
    (CondensedOpenProper.R Λ f).map (((derivedTensor Λ X).obj K).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.app L))

/-- The pullback identification `P_r P_i ≅ P_v P_p` induced by the commuting square. -/
noncomputable def canonicalPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (_sq : CommSq v r p i) (N : CondensedOpenProper.D Λ D) :
    (CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N) ⟶
      (CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N) := by
  exact (CondensedOpenProper.pComp Λ r i).inv.app N ≫
    eqToHom (by rw [_sq.w]) ≫ (CondensedOpenProper.pComp Λ v p).hom.app N

/-- The tensor transport induced by the canonical pullback comparison. -/
noncomputable def canonicalTensorPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    (_sq : CommSq v r p i) (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D) :
    ((derivedTensor Λ A).obj M).obj
        ((CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N)) ⟶
      ((derivedTensor Λ A).obj M).obj
        ((CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N)) :=
  ((derivedTensor Λ A).obj M).map (canonicalPullbackComparison Λ _sq N)

/-- The canonical inverse pullback tensor comparison `P_j K ⊗ P_j L ⟶ P_j (K ⊗ L)` for the
exact model `P_j = D(j^*)`: the published inverse of `Lj^*(K ⊗ L) ≅ Lj^* K ⊗ Lj^* L`
(`leftDerivedUpperStarTensorIso`), conjugated by the canonical identification
`Lj^* ≅ D(j^*)` (`leftDerivedUpperStarIsoMapDerivedCategory`) in all three places.
Source: the canonical ringed-derived monoidal comparison
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
noncomputable def canonicalOpenTensorComparisonInv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : CondensedOpenProper.D Λ X) (L : CondensedOpenProper.D Λ X) :
    ((derivedTensor Λ U).obj ((CondensedOpenProper.P Λ j).obj K)).obj
        ((CondensedOpenProper.P Λ j).obj L) ⟶
      (CondensedOpenProper.P Λ j).obj (((derivedTensor Λ X).obj K).obj L) :=
  ((derivedTensor Λ U).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K)).app
      ((CondensedOpenProper.P Λ j).obj L) ≫
    ((derivedTensor Λ U).obj ((upperStar Λ j).leftDerivedFunctor.obj K)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app L) ≫
    (((leftDerivedUpperStarTensorIso Λ j).app K).app L).inv ≫
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app (((derivedTensor Λ X).obj K).obj L)

/-- The normalized open tensor map at `j` is characterized by the open-adjunction unit.
Source: the open-unit equation in `lem-sf-open-tensor-normalization`. -/
def openTensorUnitNormalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : CondensedOpenProper.D Λ U) (N : CondensedOpenProper.D Λ X)
    (delta : ((derivedTensor Λ X).obj ((CondensedOpenProper.J Λ j).obj M)).obj N ⟶
      (CondensedOpenProper.J Λ j).obj (((derivedTensor Λ U).obj M).obj
        ((CondensedOpenProper.P Λ j).obj N))) : Prop :=
  (((derivedTensor Λ U).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)).app
      ((CondensedOpenProper.P Λ j).obj N) ≫
    canonicalOpenTensorComparisonInv Λ j ((CondensedOpenProper.J Λ j).obj M) N ≫
    (CondensedOpenProper.P Λ j).map delta) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app
        (((derivedTensor Λ U).obj M).obj ((CondensedOpenProper.P Λ j).obj N))

/-- Condensed proper/open tensor compatibility for ordinary unbounded derived categories.

Fix a prime `ell`, a positive-characteristic field `k` with `char(k) ≠ ell`, an admissible
coefficient ring `Λ`, and a normalized canonical package `data`. Let `A,B,C,D` be separated
finite-type `k`-schemes in a commuting square with proper vertical maps and quasi-compact open
horizontal maps. For maps `delta_v` and `delta_i` satisfying the displayed open-unit
normalization equations, the two canonical composites agree.

Proof (steps 1--7 from the blueprint proof):
1. Set `H = R_r M`, `X = P_i N`, `Y = P_p N`, `K = M ⊗ P_r X`, and `F = J_v M`; use the
   canonical pullback compositor to identify `P_r X` with `P_v Y`.
2. Precompose both arrows with the inverse of the normalized `delta_i`, then use the
   `J_i ⊣ P_i` adjunct bijection, the canonical proper/open mate, and the `P_r ⊣ R_r`
   transpose; every operation is injective on the relevant hom-set.
3. The defining counit-transpose equation for the canonical projection map `pi_p` identifies
   the transpose of the left projection factor with the tensor of the proper counit and the
   identity.
4. The two open-unit normalization equations move the open units through `delta_i` and
   `delta_v`; naturality of the canonical mate moves the remaining comparison through it.
5. The mate normalization and proper counit naturality reduce the left transpose to
   `u_v (epsilon_r ⊗ 1)`.
6. Cancelling `delta_i` on the right and applying the defining transpose equation for `pi_r`
   gives the same `u_v (epsilon_r ⊗ 1)` for the right-hand arrow.
7. The transpose bijections are injective, so the displayed composites are equal; all maps
   are natural in the two unbounded derived inputs and no Tor-amplitude or boundedness
   hypothesis is used.

Source: blueprint proof cited above; finite analogues are Stacks Tags 0F7B, 0B56 and 0GL1.
(blueprint: lem-sf-condensed-proper-open-tensor-mate) -/
theorem condensedProperOpenTensorMate
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsAdmissibleCoefficient Λ)
    {A B C D : Scheme.{u}}
    (aA : A ⟶ Spec (.of k)) (aB : B ⟶ Spec (.of k))
    (aC : C ⟶ Spec (.of k)) (aD : D ⟶ Spec (.of k))
    [LocallyOfFiniteType aA] [QuasiCompact aA] [IsSeparated aA]
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType aC] [QuasiCompact aC] [IsSeparated aC]
    [LocallyOfFiniteType aD] [QuasiCompact aD] [IsSeparated aD]
    {v : A ⟶ B} {r : A ⟶ C} {p : B ⟶ D} {i : C ⟶ D}
    [IsOpenImmersion v] [IsOpenImmersion i]
    [QuasiCompact v] [QuasiCompact i] [IsProper p] [IsProper r]
    (_sq : CommSq v r p i)
    (data : CondensedOpenProper.Pasting Λ)
    (delta_v : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      ((derivedTensor Λ B).obj ((CondensedOpenProper.J Λ v).obj M)).obj
        ((CondensedOpenProper.P Λ p).obj N) ⟶
        (CondensedOpenProper.J Λ v).obj (((derivedTensor Λ A).obj M).obj
          ((CondensedOpenProper.P Λ v).obj ((CondensedOpenProper.P Λ p).obj N))))
    (delta_i : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      ((derivedTensor Λ D).obj ((CondensedOpenProper.J Λ i).obj
        ((CondensedOpenProper.R Λ r).obj M))).obj N ⟶
        (CondensedOpenProper.J Λ i).obj (((derivedTensor Λ C).obj
          ((CondensedOpenProper.R Λ r).obj M)).obj
            ((CondensedOpenProper.P Λ i).obj N)))
    (hdelta_v : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      openTensorUnitNormalization Λ v M ((CondensedOpenProper.P Λ p).obj N)
        (delta_v M N))
    (hdelta_i : ∀ (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D),
      openTensorUnitNormalization Λ i ((CondensedOpenProper.R Λ r).obj M) N
        (delta_i M N))
    (M : CondensedOpenProper.D Λ A) (N : CondensedOpenProper.D Λ D) :
    ((derivedTensor Λ D).map ((CondensedOpenProper.gamma Λ data.units _sq).app M)).app N ≫
        canonicalModuleObjectProjectionMap Λ p ((CondensedOpenProper.J Λ v).obj M) N ≫
        (CondensedOpenProper.R Λ p).map (delta_v M N) =
      delta_i M N ≫
        (CondensedOpenProper.J Λ i).map
          (canonicalModuleObjectProjectionMap Λ r M
            ((CondensedOpenProper.P Λ i).obj N)) ≫
        (CondensedOpenProper.gamma Λ data.units _sq).app
          (((derivedTensor Λ A).obj M).obj
            ((CondensedOpenProper.P Λ r).obj ((CondensedOpenProper.P Λ i).obj N))) ≫
        (CondensedOpenProper.J Λ v ⋙ CondensedOpenProper.R Λ p).map
          (canonicalTensorPullbackComparison Λ _sq M N) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
