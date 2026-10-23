/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LocalizationLowerShriek
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# The open–closed triangle of Weil complexes

For a quasi-compact open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X`, every Weil
complex `K` on `X` sits in a distinguished triangle `Rj₀! j^*K ⟶ K ⟶ Ri₀* i^*K ⟶`
(`prop-sf-open-closed-triangle-all-stages`). It is kept apart from
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality` because its proof identifies `Rj₀!` with the
extension by zero through proper base change, which needs much heavier imports.

## Main statements

- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`: the open–closed triangle.
-/

@[expose] public section

-- The imports bring in `AlgebraicGeometry.specOverSpec` of `(Spec A).Over (Spec R)`, under which
-- `Spec k₀` would lie over itself through `Algebra.id` rather than through the identity, which the
-- structure-morphism instances `(X ↘ S).IsOver S` do not unify with. The canonical instance is
-- given priority.
attribute [local instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilComplex

variable {X Z U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 1000000 in
-- the vertices of the triangle are identified through the chosen compactification of `j`
/-- **The open–closed triangle** (blueprint: `prop-sf-open-closed-triangle-all-stages`): for a
quasi-compact open immersion `j : U ⟶ X` with closed complement `i : Z ⟶ X` and a Weil complex `K`
on `X`, the open counit and the closed unit extend to a distinguished triangle of Weil complexes
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ j₀!j₀^*K[1]`.

This is a weakening of the blueprint node: the vertices of the triangle are only identified up
to some isomorphism, and the first two arrows are not asserted to be the canonical counit and
unit.

The direct image with compact support `Rj₀! = Rḡ_* ā_!` is computed on the chosen
compactification `U ⟶[a] W ⟶[g] X` of `j`; it is the extension by zero `j_!`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso`, by
proper base change), and the triangle is the open–closed triangle of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.exists_distTriang_openClosed`), whose vertices are Weil
complexes. -/
theorem exists_distTriang_openClosed (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ T ∈ distTriang (WeilComplex k₀ l X),
      Nonempty (T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)) ∧
      Nonempty (T.obj₂ ≅ K) ∧
      Nonempty (T.obj₃ ≅ (derivedLowerStar i).obj ((upperStar i).obj K)) := by
  let c := HasCompactification.compactification j (hf := hasCompactification_of_over (k₀ := k₀) j)
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  -- `Rj₀! j^* K ≅ j_! j^* K`
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso j i c.i c.g
    c.comm.symm hij ((upperStar j).obj K).obj ((upperStar j).obj K).property
  -- the open–closed triangle of the underlying complex of `K`
  obtain ⟨w, hw⟩ := ProEtaleWeilSheaf.exists_distTriang_openClosed j i hij.symm K.obj
  let A := (derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)
  let f₁ : A ⟶ K := ObjectProperty.homMk (e.hom ≫
    (ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j).counit.app K.obj)
  obtain ⟨C, g₁, h₁, hT⟩ := distinguished_cocone_triangle f₁
  refine ⟨_, hT, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ?_⟩
  have hT' : (WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj (Triangle.mk f₁ g₁ h₁) ∈
      distTriang _ := hT
  obtain ⟨φ, -, -⟩ := exists_iso_of_arrow_iso _ _ hT' hw (Arrow.isoMk e (Iso.refl _) (by
    change _ = (WeilComplex.objectProperty k₀ l X).ι.map f₁ ≫ 𝟙 _
    rw [Category.comp_id, ObjectProperty.ι_map]
    rfl))
  exact ⟨ObjectProperty.isoMk _ (Triangle.π₃.mapIso φ)⟩


end WeilComplex

end AlgebraicGeometry
