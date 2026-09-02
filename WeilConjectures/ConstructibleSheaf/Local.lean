/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Local nature of local constancy, finiteness and finite local constancy

Local constancy is étale local (`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_cover`):
the trivialising covers of the restrictions of `G` to the members of an étale cover compose,
by `Precoverage.ZeroHypercover.bind`, to a trivialising cover of `G`.

Finiteness of the stalks is Zariski local (`IsFiniteSheaf.of_openCover`): a geometric point
lifts to a member of an open cover containing its image, and the stalk of the restriction at
the lift is the stalk. Hence finite local constancy is Zariski local
(`IsFiniteLocallyConstantSheaf.of_openCover`). Each of the three statements is recorded in
the `iff` form as well, the converse direction being the invariance of the three notions
under pullback.

## Implementation notes

Finiteness is stated for *open* covers only, although local constancy is already available
for étale covers: lifting a geometric point along an étale morphism is not covered by
`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_mem_range`, étale morphisms not being surjective
on stalks. It uses instead that the residue extension at a point of the fibre is finite
separable, so that a separably closed field receiving the residue field of the image also
receives the residue field of the point. This is not formalised here; the Zariski statement
is what generic constancy needs, see `WeilConjectures.ConstructibleSheaf.GenericConstancy`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- **Local constancy is étale local**: if the pullbacks of `G` to the members of an étale
cover `𝒰` are locally constant, so is `G`.

Choosing a trivialising cover `𝒱 i` of `(𝒰.f i)^* G` for every `i`, the members of the
bound cover `𝒰.bind 𝒱` factor as

```
   V i j ──(𝒱 i).cover.f j──→ U i
      ╲                        │
       ╲ (𝒰.bind 𝒱).f ⟨i, j⟩   │ 𝒰.f i
        ╲                      ↓
         ─────────────────────→ X
```

and `Etale.upperStarComp` identifies `((𝒰.bind 𝒱).f ⟨i, j⟩)^* G` with
`((𝒱 i).cover.f j)^* (𝒰.f i)^* G`, which is constant by the choice of `𝒱 i`. The bound
cover is reindexed by the points of `X` to land in the universe of `LocallyConstantDatum`. -/
theorem IsLocallyConstantSheaf.of_cover (𝒰 : Cover.{v} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsLocallyConstantSheaf G := by
  obtain ⟨𝒱⟩ := Classical.nonempty_pi.mpr fun i : 𝒰.I₀ ↦
    IsLocallyConstantSheaf.nonempty_locallyConstantDatum
      (F := (Etale.upperStar A (𝒰.f i)).obj G)
  set 𝒲 : Cover.{max v u} etalePrecoverage X := 𝒰.bind fun i ↦ (𝒱 i).cover with h𝒲
  have key (k : 𝒲.I₀) : (G.over (𝒲.etalePrecoverageToEtale k)).IsConstant
      (X.smallEtaleTopology.over (𝒲.etalePrecoverageToEtale k)) := by
    obtain ⟨i, j⟩ := k
    rw [isConstant_over_iff_upperStar]
    -- the two sites agree definitionally: `𝒲.f ⟨i, j⟩` is `(𝒱 i).cover.f j ≫ 𝒰.f i`
    have h : ((Etale.upperStar A (𝒰.f i) ⋙ Etale.upperStar A ((𝒱 i).cover.f j)).obj G).IsConstant
        (𝒲.etalePrecoverageToEtale ⟨i, j⟩).left.smallEtaleTopology :=
      (isConstant_over_iff_upperStar A ((𝒱 i).cover.etalePrecoverageToEtale j) _).mp
        ((𝒱 i).isConstant j)
    exact Sheaf.isConstant_congr _
      ((Etale.upperStarComp A ((𝒱 i).cover.f j) (𝒰.f i)).app G).symm
  exact ⟨⟨⟨𝒲.ulift, fun x ↦ key (𝒲.idx x)⟩⟩⟩

/-- A sheaf is locally constant if and only if its pullbacks to the members of an étale
cover are. -/
theorem isLocallyConstantSheaf_iff_of_cover (𝒰 : Cover.{v} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A) :
    IsLocallyConstantSheaf G ↔
      ∀ i, IsLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G) :=
  ⟨fun _ i ↦ IsLocallyConstantSheaf.upperStar (𝒰.f i) G,
    fun h ↦ have := h; IsLocallyConstantSheaf.of_cover 𝒰 G⟩

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Finiteness is Zariski local**: if the pullbacks of `G` to the members of an open cover
are finite, so is `G`. This is the case of an open cover of
`AlgebraicGeometry.Scheme.IsFiniteSheaf.of_jointly_surjective`. -/
theorem IsFiniteSheaf.of_openCover (𝒰 : OpenCover.{v} X) (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] : IsFiniteSheaf G :=
  IsFiniteSheaf.of_jointly_surjective 𝒰.f
    (fun x ↦ have ⟨i, y, hy⟩ := 𝒰.exists_eq x; ⟨i, y, hy⟩) G

/-- A sheaf is finite if and only if its pullbacks to the members of an open cover are. -/
theorem isFiniteSheaf_iff_of_openCover (𝒰 : OpenCover.{v} X)
    (G : Sheaf X.smallEtaleTopology A) :
    IsFiniteSheaf G ↔ ∀ i, IsFiniteSheaf ((Etale.upperStar A (𝒰.f i)).obj G) :=
  ⟨fun _ i ↦ IsFiniteSheaf.upperStar (𝒰.f i) G,
    fun h ↦ have := h; IsFiniteSheaf.of_openCover 𝒰 G⟩

/-- **Finite local constancy is Zariski local**: if the pullbacks of `G` to the members of
an open cover are finite locally constant, so is `G`. This combines
`AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.of_cover`, an open cover being an étale
cover, with `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_openCover`. -/
theorem IsFiniteLocallyConstantSheaf.of_openCover (𝒰 : OpenCover.{v} X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf :=
    let 𝒱 : Cover.{v} etalePrecoverage X := 𝒰.changeProp (Q := @Etale) fun _ ↦ inferInstance
    have : ∀ i, IsLocallyConstantSheaf ((Etale.upperStar A (𝒱.f i)).obj G) := fun i ↦
      inferInstanceAs (IsLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G))
    IsLocallyConstantSheaf.of_cover 𝒱 G
  toIsFiniteSheaf := IsFiniteSheaf.of_openCover 𝒰 G

/-- A sheaf is finite locally constant if and only if its pullbacks to the members of an
open cover are. -/
theorem isFiniteLocallyConstantSheaf_iff_of_openCover (𝒰 : OpenCover.{v} X)
    (G : Sheaf X.smallEtaleTopology A) :
    IsFiniteLocallyConstantSheaf G ↔
      ∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G) :=
  ⟨fun _ i ↦ IsFiniteLocallyConstantSheaf.upperStar (𝒰.f i) G,
    fun h ↦ have := h; IsFiniteLocallyConstantSheaf.of_openCover 𝒰 G⟩

end Finite

end AlgebraicGeometry.Scheme

end
