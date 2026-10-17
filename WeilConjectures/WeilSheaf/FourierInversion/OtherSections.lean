/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Fourier inversion: inputs from other sections

Statements of blueprint nodes of other sections (the projection formula, the open–closed
recollement and the Thom isomorphism for Weil complexes) used in the proof of Fourier inversion,
recorded here with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section OtherSections

/-- Blueprint `prop-weil-operations`: Six operations on Weil complexes (the projection
formula). For a separated quasi-compact morphism `f : X ⟶ Y` locally of finite type of
`k₀`-schemes of finite type and a lisse Weil sheaf `G` on `Y`, `Rf₀!(f^* G ⊗ K) ≅ G ⊗ Rf₀! K`
naturally in the Weil complex `K` (`G`, lisse, is in particular of finite Tor-amplitude). -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.tensorLisse G hG ≅
      WeilComplex.tensorLisse ((WeilSheaf.upperStar f).obj G)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        WeilComplex.derivedLowerShriek k₀ l f) :=
  sorry

/-- Blueprint `def-weil-open-closed-recollement` and
`prop-weil-open-closed-recollement-adjunctions` (open–closed recollement), for Weil complexes.
Let `i : Z ⟶ X` be a closed immersion of `k₀`-schemes of finite type and `j : U ⟶ X` the
complementary open immersion. There is a natural transformation `K ⟶ Ri_* i^* K` (the closed
unit) which is an isomorphism at every `K` with `j^* K = 0`: in the recollement triangle
`j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`, the first term vanishes.

The closed unit is the unit of `i^* ⊣ Ri_*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction`); it is invertible at
`K` with `j^* K = 0` by
`DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero`, using that
`i_*` is exact, `j^* i_* = 0` and that `i^*`, `j^*` jointly detect zero objects. The open
immersion `j` is quasi-compact since `X` is Noetherian. -/
theorem WeilComplex.exists_isIso_app_of_isZero_upperStar {X Z U : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i]
    [IsOpenImmersion j] [i.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] (hij : Set.range j = (Set.range i)ᶜ)
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ η : 𝟭 (WeilComplex k₀ l X) ⟶
        WeilComplex.upperStar i ⋙ WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) i,
      ∀ K : WeilComplex k₀ l X, IsZero ((WeilComplex.upperStar j).obj K) → IsIso (η.app K) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have hij' : IsCompl (Set.range i.base) (Set.range j.base) := by
    have h : Set.range j.base = (Set.range i.base)ᶜ := hij
    rw [h]
    exact isCompl_compl
  let adj := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i
  refine ⟨{ app K := ObjectProperty.homMk (adj.unit.app K.obj)
            naturality _ _ f := ObjectProperty.hom_ext _ (adj.unit.naturality f.hom) },
    fun K hK ↦ ?_⟩
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl (k₀ := k₀) (l := l)
    i j hij'
  have hiso : IsIso (adj.unit.app K.obj) :=
    DerivedCategory.isIso_mapDerivedCategoryRightDerivedAdjunction_unit_app_of_isZero
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i)
      (ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij')
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij')
      ((ObjectProperty.ι _).map_isZero hK)
  have : IsIso ((ObjectProperty.ι (WeilComplex.objectProperty k₀ l X)).map
      (ObjectProperty.homMk (adj.unit.app K.obj) :
        (show WeilComplex k₀ l X from K) ⟶ (WeilComplex.derivedLowerStar i).obj
          ((WeilComplex.upperStar i).obj K))) := hiso
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

/-- Blueprint `thm-pur-rank-one-thom` (and its vector-bundle form `thm-pur-vector-bundle-thom`),
combined with the projection formula of `prop-weil-operations` for the constant sheaf: for the
trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, `Rπ₀! π^* P ≅ P(-1)[-2]` naturally in the Weil
complex `P` on `X`. The trivial line bundle is given by a cartesian square
`Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. -/
theorem WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar π ⋙ WeilComplex.derivedLowerShriek k₀ l π ≅
      WeilComplex.tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) :=
  sorry

end OtherSections

end AlgebraicGeometry
