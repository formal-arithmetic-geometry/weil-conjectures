/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Direct sums of finite locally constant sheaves

The direct sum of two finite locally constant sheaves on the small étale site of a scheme is
finite locally constant. (blueprint: `lemma:constructible-flc-biproduct`)

## Main results

* `AlgebraicGeometry.Scheme.LocallyConstantDatum.interCover`, with
  `AlgebraicGeometry.Scheme.LocallyConstantDatum.interLeft` and
  `AlgebraicGeometry.Scheme.LocallyConstantDatum.interRight`: two locally constant sheaves
  are trivialised by a common étale cover, the fibre product of trivialising covers.
* `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.biprod`: the direct sum of two locally
  constant sheaves is locally constant.
* `AlgebraicGeometry.Scheme.IsFiniteSheaf.biprod`: the direct sum of two finite sheaves is
  finite.
* `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.biprod`: the direct sum of two
  finite locally constant sheaves is finite locally constant.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section LocallyConstant

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {F G : Sheaf X.smallEtaleTopology A}

/-- The common refinement `(Uᵢ ×_X Vⱼ → X)_{i, j}` of the trivialising covers `(Uᵢ → X)ᵢ` of
`F` and `(Vⱼ → X)ⱼ` of `G`.

```
Uᵢ ×_X Vⱼ ────── snd ──────▶ Uᵢ
    │                         │
fst │                         │ d.cover.f i
    ▼                         ▼
   Vⱼ ──── e.cover.f j ──────▶ X
```
-/
def LocallyConstantDatum.interCover (d : LocallyConstantDatum F) (e : LocallyConstantDatum G) :
    Cover.{u} etalePrecoverage X :=
  d.cover.bind fun i ↦ e.cover.pullback₂ (d.cover.f i)

/-- The common refinement of the trivialising covers of `F` and `G` trivialises `F`: the
restriction of `F` to `Uᵢ` is constant, hence so is its further restriction to
`Uᵢ ×_X Vⱼ`. -/
def LocallyConstantDatum.interLeft (d : LocallyConstantDatum F) (e : LocallyConstantDatum G) :
    LocallyConstantDatum F where
  cover := d.interCover e
  isConstant := fun ⟨i, j⟩ ↦ by
    rw [isConstant_over_iff_upperStar]
    have : ((Etale.upperStar A (d.cover.f i)).obj F).IsConstant
        (d.cover.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (d.cover.etalePrecoverageToEtale i) F).mp (d.isConstant i)
    exact Sheaf.IsConstant.upperStar_of_fac A (pullback.snd (e.cover.f j) (d.cover.f i)) rfl F

/-- The common refinement of the trivialising covers of `F` and `G` trivialises `G`: the
restriction of `G` to `Vⱼ` is constant, hence so is its further restriction to
`Uᵢ ×_X Vⱼ`, the two morphisms `Uᵢ ×_X Vⱼ ⟶ X` being identified by
`CategoryTheory.Limits.pullback.condition`. -/
def LocallyConstantDatum.interRight (d : LocallyConstantDatum F) (e : LocallyConstantDatum G) :
    LocallyConstantDatum G where
  cover := d.interCover e
  isConstant := fun ⟨i, j⟩ ↦ by
    rw [isConstant_over_iff_upperStar]
    have : ((Etale.upperStar A (e.cover.f j)).obj G).IsConstant
        (e.cover.X j).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (e.cover.etalePrecoverageToEtale j) G).mp (e.isConstant j)
    exact Sheaf.IsConstant.upperStar_of_fac A (pullback.fst (e.cover.f j) (d.cover.f i))
      pullback.condition.symm G

/-- The pullback of a direct sum of two sheaves with constant pullbacks is constant: the
pullback `g^*` is a left adjoint, hence preserves binary biproducts. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.upperStar_biprod {Y : Scheme.{u}} (g : Y ⟶ X)
    (F G : Sheaf X.smallEtaleTopology A)
    [((Etale.upperStar A g).obj F).IsConstant Y.smallEtaleTopology]
    [((Etale.upperStar A g).obj G).IsConstant Y.smallEtaleTopology] :
    ((Etale.upperStar A g).obj (F ⊞ G)).IsConstant Y.smallEtaleTopology :=
  have := (Etale.upperStar A g).preservesBinaryBiproducts_of_isLeftAdjoint
  have := Sheaf.isConstant_biprod (F := (Etale.upperStar A g).obj F)
    (G := (Etale.upperStar A g).obj G) terminalIsTerminal
  Sheaf.isConstant_congr _ ((Etale.upperStar A g).mapBiprod F G).symm

/-- **The direct sum of two locally constant sheaves is locally constant**, trivialised by
the common refinement of trivialising covers of the two summands. -/
instance IsLocallyConstantSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] [IsLocallyConstantSheaf G] : IsLocallyConstantSheaf (F ⊞ G) := by
  obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨e⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  refine ⟨⟨⟨d.interCover e, fun i ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  -- both `have`s are stated in the form in which they are found by instance search
  have : ((Etale.upperStar A ((d.interCover e).etalePrecoverageToEtale i).hom).obj F).IsConstant
      ((d.interCover e).etalePrecoverageToEtale i).left.smallEtaleTopology :=
    (isConstant_over_iff_upperStar A _ F).mp ((d.interLeft e).isConstant i)
  have : ((Etale.upperStar A ((d.interCover e).etalePrecoverageToEtale i).hom).obj G).IsConstant
      ((d.interCover e).etalePrecoverageToEtale i).left.smallEtaleTopology :=
    (isConstant_over_iff_upperStar A _ G).mp ((d.interRight e).isConstant i)
  exact Sheaf.IsConstant.upperStar_biprod _ F G

end LocallyConstant

section Finite

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

/-- **The direct sum of two finite sheaves is finite.** The stalk functor at a geometric
point is left adjoint to the skyscraper sheaf functor, so it preserves binary biproducts,
and the underlying type of a binary biproduct is the product of the underlying types:

```
ToType ((F ⊞ G)ₛ) ≃ ToType (Fₛ ⊞ Gₛ) ≃ ToType Fₛ × ToType Gₛ
```
-/
instance IsFiniteSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsFiniteSheaf F] [IsFiniteSheaf G] : IsFiniteSheaf (F ⊞ G) where
  finite_sheafFiber Ω _ _ s := by
    have := IsFiniteSheaf.finite_sheafFiber (FA := FA) (CA := CA) (F := F) Ω s
    have := IsFiniteSheaf.finite_sheafFiber (FA := FA) (CA := CA) (F := G) Ω s
    have := ((pointSmallEtale s).sheafFiber (A := A)).preservesBinaryBiproducts_of_isLeftAdjoint
    exact Finite.of_equiv _
      ((CategoryTheory.forget A).mapIso
        ((pointSmallEtale s).sheafFiber.mapBiprod F G)).toEquiv.symm

/-- **The direct sum of two finite locally constant sheaves is finite locally constant.**
(blueprint: `lemma:constructible-flc-biproduct`) -/
instance IsFiniteLocallyConstantSheaf.biprod (F G : Sheaf X.smallEtaleTopology A)
    [IsFiniteLocallyConstantSheaf F] [IsFiniteLocallyConstantSheaf G] :
    IsFiniteLocallyConstantSheaf (F ⊞ G) where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.biprod F G
  toIsFiniteSheaf := IsFiniteSheaf.biprod F G

end Finite

end AlgebraicGeometry.Scheme

end
