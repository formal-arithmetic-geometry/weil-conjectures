/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.LocalizationLowerShriek
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# The open–closed triangle under direct image with compact support

For a closed immersion `i : Z ↪ X` with open complement `j : U ↪ X` of separated `k₀`-schemes of
finite type, applying `Ra_!` to the open–closed localization triangle `j_!j^*K → K → i_*i^*K →` of
a Weil complex `K` on `X` gives a distinguished triangle

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶`

of Weil complexes on `Spec k₀` (blueprint `prop-functor-package`, clause 3). This file deduces it
and identifies the pullback of a Weil sheaf placed in degree zero with the pullback of the sheaf.

## Main declarations

- `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed`:
  the triangle.
- `AlgebraicGeometry.WeilSheaf.toComplexCompUpperStarIso`: `φ^* (F[0]) ≅ (φ^* F)[0]`.
- `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`: the open–closed triangle
  `Rj₀! j^*K ⟶ K ⟶ Ri₀* i^*K ⟶` of a Weil complex (`prop-sf-open-closed-triangle-all-stages`),
  whose proof identifies `Rj₀!` with the extension by zero through proper base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- `Rf₀!` only depends on the morphism `f`, not on the proofs of its properties: equal morphisms
have isomorphic direct images with compact support. -/
noncomputable def WeilComplex.derivedLowerShriekIsoOfEq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y}
    (h : f = g) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    derivedLowerShriek k₀ l f ≅ derivedLowerShriek k₀ l g :=
  eqToIso (by subst h; rfl)

/-- **The open–closed triangle under `Ra_!`**: for a closed immersion `i : Z ↪ X` with open
complement `j : U ↪ X` of separated `k₀`-schemes of finite type and a Weil complex `K` on `X`,
there is a distinguished triangle of Weil complexes on `Spec k₀`

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶ Ra_{U!} j^*K[1]`,

obtained by applying `Ra_{X!}` to the open–closed recollement triangle `j_!j^*K → K → i_*i^*K →`
(`AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` for the structure
morphism `a_X`), using `a_X ∘ j = a_U` and `a_X ∘ i = a_Z`. -/
theorem WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (K : WeilComplex k₀ l X) :
    ∃ (α : (derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K) ⟶
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K)
      (β : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ⟶
        (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K))
      (γ : (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K) ⟶
        ((derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (WeilComplex k₀ l (Spec (CommRingCat.of k₀))) := by
  have hj : j ≫ X ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) :=
    comp_over j _
  have hi : i ≫ X ↘ Spec (CommRingCat.of k₀) = Z ↘ Spec (CommRingCat.of k₀) :=
    comp_over i _
  have : QuasiCompact (j ≫ X ↘ Spec (CommRingCat.of k₀)) := by rw [hj]; infer_instance
  have : QuasiCompact j := QuasiCompact.of_comp j (X ↘ Spec (CommRingCat.of k₀))
  have hc : IsCompl (Set.range j.base) (Set.range i.base) := by
    rw [hij]; exact isCompl_compl
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_derivedLowerShriek_openClosed j i hc (X ↘ Spec (CommRingCat.of k₀)) K
  let e₁' := e₁ ≪≫ (derivedLowerShriekIsoOfEq hj).app _
  let e₃' := e₃ ≪≫ (derivedLowerShriekIsoOfEq hi).app _
  refine ⟨e₁'.inv ≫ T.mor₁ ≫ e₂.hom, e₂.inv ≫ T.mor₂ ≫ e₃'.hom,
    e₃'.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁'.hom,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁'.symm e₂.symm e₃'.symm ?_ ?_ ?_)⟩
  · simp
  · simp
  · simp [← Functor.map_comp]

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf placed in
degree zero: the pullback of pro-étale Weil sheaves is exact. -/
noncomputable def WeilSheaf.toComplexCompUpperStarIso :
    WeilSheaf.toComplex ⋙ WeilComplex.upperStar φ ≅
      WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.toComplex :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor
        0) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry

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
